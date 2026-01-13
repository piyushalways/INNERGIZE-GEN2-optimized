/******************************************************************************
 * Copyright © 2022 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include "as7058_chiplib.h"
#include "agc.h"
#include "as7058_bioz_measurement.h"
#include "as7058_eda_scaling.h"
#include "as7058_extract.h"
#include "as7058_interface.h"
#include "as7058_osal_chiplib.h"
#include "as7058_pd_offset_calibration.h"
#include "as7058_typedefs.h"
#include "as7058_version.h"
#include "error_codes.h"
#include "std_inc.h"
#include "as7058_osal_chiplib_template.h"


/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

enum LIB_STATES {
    LIB_STATE_UNINITIALIZED = 0,
    LIB_STATE_CONFIGURATION = 1,
    LIB_STATE_MEASUREMENT = 2,
};

struct device_config {
    as7058_callback_t p_normal_callback;
    as7058_callback_special_measurement_t p_special_callback;
    const void *p_cb_param;
    volatile enum LIB_STATES lib_state;
    as7058_meas_config_t meas_config;
    volatile uint8_t is_meas_running;
    as7058_interrupt_t enabled_irqs;
    uint16_t fifo_threshold;
    as7058_meas_mode_t mode;
    uint8_t reg_val_bioz_cfg; /*!< Value of register BIOZ_CFG as passed to the Chip Library. The reset value of this
                                   register in the silicon is 0x00. */
};

/*! Index of register BIOZ_CFG in as7058_reg_group_ecg_t::reg_buffer. */
#define REG_INDEX__ECG__BIOZ_CFG 0

/*! Bitmask for field gsr_en of register BIOZ_CFG. */
#define REG_MASK__BIOZ_CFG__GSR_EN 0x02

/******************************************************************************
 *                                  GLOBALS                                   *
 ******************************************************************************/

static struct device_config g_dev_config;

/******************************************************************************
 *                               LOCAL FUNCTIONS                              *
 ******************************************************************************/
uint8_t fifo_data[AS7058_FIFO_DATA_BUFFER_SIZE];
uint16_t fifo_data_size = 0;

as7058_status_events_t status_events = {0, 0, 0, 0, 0, 0, 0, 0, 0};
static err_code_t interrupt_handler(void)
{
    err_code_t result;
    as7058_interrupt_t irq_status;
    
    uint16_t fifo_level;
    
    agc_status_t agc_status[AGC_MAX_CHANNEL_CNT];
    uint8_t agc_status_num = AGC_MAX_CHANNEL_CNT;
    
    as7058_interrupt_t combined = {0, 0, 0, 0, 0, 0, 0, 0};
    const as7058_special_measurement_result_t *p_special_result;
    uint16_t result_size;

    if (!g_dev_config.is_meas_running) {
        return ERR_PERMISSION;
    }

    result = as7058_ifce_get_interrupt_status(&irq_status);
    if (ERR_SUCCESS == result) {
        combined.asat = g_dev_config.enabled_irqs.asat & irq_status.asat;
        combined.iir_overflow = g_dev_config.enabled_irqs.iir_overflow & irq_status.iir_overflow;
        combined.leadoff = g_dev_config.enabled_irqs.leadoff & irq_status.leadoff;
        combined.led_lowvds = g_dev_config.enabled_irqs.led_lowvds & irq_status.led_lowvds;
        combined.sequencer = g_dev_config.enabled_irqs.sequencer & irq_status.sequencer;
        combined.vcsel = g_dev_config.enabled_irqs.vcsel & irq_status.vcsel;
        result = as7058_ifce_get_sub_status_registers(combined, &status_events);

        /* Readout FIFO overflow status if enabled and triggered */
        if (ERR_SUCCESS != result) {
            /* Do nothing */
        } else if (irq_status.fifo_overflow && g_dev_config.enabled_irqs.fifo_overflow) {
            result = ERR_OVERFLOW;
        } else if (irq_status.fifo_threshold && g_dev_config.enabled_irqs.fifo_threshold) {
            /* Readout FIFO level if FIFO threshold IRQ is enabled and triggered */
            result = as7058_ifce_get_fifo_level(&fifo_level);
            if (ERR_SUCCESS == result) {

                /* Prevent division by zero */
                if (0 == g_dev_config.fifo_threshold) {
                    result = ERR_CONFIG;
                } else {

                    /* Calculate read length as multiple of FIFO threshold */
                    fifo_level = (fifo_level / g_dev_config.fifo_threshold) * g_dev_config.fifo_threshold;

                    /* Calculate the real data size */
                    fifo_data_size = fifo_level * AS7058_FIFO_SAMPLE_SIZE;

                    /* Check that we have no capacity issues */
                    if (sizeof(fifo_data) < fifo_data_size) {
                        fifo_data_size = 0;
                        result = ERR_SIZE;
                    } else {
                        result = as7058_ifce_get_fifo_data(fifo_data, fifo_data_size);
                    }
                }
            }

            if (ERR_SUCCESS == result) {
                result = agc_get_status(agc_status, &agc_status_num);
            }

            if (ERR_SUCCESS == result && g_dev_config.p_normal_callback) {
                g_dev_config.p_normal_callback(result, fifo_data, fifo_data_size, agc_status, agc_status_num,
                                               status_events, g_dev_config.p_cb_param);
            }

            if ((ERR_SUCCESS == result) && (AS7058_MEAS_MODE_NORMAL == g_dev_config.mode)) {
                result = agc_execute(fifo_data, fifo_data_size);
            }

            if ((ERR_SUCCESS == result) && (AS7058_MEAS_MODE_NORMAL != g_dev_config.mode)) {
                if (AS7058_MEAS_MODE_SPECIAL_SCALING_EDA == g_dev_config.mode) {
                    result_size = sizeof(as7058_eda_scaling_result_t);
                    result = as7058_eda_scaling_process(fifo_data, fifo_data_size,
                                                        (const as7058_eda_scaling_result_t **)&p_special_result);
                } else if (AS7058_MEAS_MODE_SPECIAL_BIOZ == g_dev_config.mode) {
                    result_size = sizeof(as7058_bioz_meas_result_t);
                    result = as7058_bioz_process(fifo_data, fifo_data_size,
                                                 (const as7058_bioz_meas_result_t **)&p_special_result);
                } else if (AS7058_MEAS_MODE_SPECIAL_PD_OFFSET_CALIBRATION == g_dev_config.mode) {
                    result_size = sizeof(as7058_pd_offset_calibration_result_t);
                    result = as7058_pd_offset_calibration_process(
                        fifo_data, fifo_data_size, (const as7058_pd_offset_calibration_result_t **)&p_special_result);
                } else {
                    return ERR_NOT_SUPPORTED;
                }
                if ((ERR_SUCCESS == result) && (g_dev_config.p_special_callback)) {
                    g_dev_config.p_special_callback(g_dev_config.mode, p_special_result, result_size,
                                                    g_dev_config.p_cb_param);
                } else if (ERR_NO_DATA == result) {
                    result = ERR_SUCCESS;
                }
            }
        } else if (g_dev_config.p_normal_callback) {
            g_dev_config.p_normal_callback(result, NULL, 0, NULL, 0, status_events, g_dev_config.p_cb_param);
        }


        
    //printk("fifo_data size: %d \n", fifo_data_size);
  //  result = as7058_ifce_get_fifo_data(fifo_data, 18);
    
        //printk("as7058_ifce_get_fifo_data err: %d \n", result);
      // int as_data_state;
     //  err_code_t as_data = as7058a_hrm_b0_set_input(fifo_data, 18,status_events,NULL,0,NULL,0,&as_data_state);
       //printk("as7058a_hrm_b0_set_input err: %d \n", as_data);
      // printk("as_data_state: %d \n", as_data_state);
    //    for(int i=0; i<18; i++){
    //      printk("fifo_data[%d]: %d \n", i, fifo_data[i]);
    //        fifo_data[i] = fifo_data[i];
    //    }
      
    }

    if (ERR_SUCCESS != result && g_dev_config.p_normal_callback) {
        g_dev_config.p_normal_callback(result, NULL, 0, NULL, 0, status_events, g_dev_config.p_cb_param);
        as7058_stop_measurement();
    }

    return result;
}

uint8_t* get_fifo_data(){
    return fifo_data;
}

as7058_status_events_t *get_status_events(){
    return &status_events;
}


void interrupt_calling_func(void){
      err_code_t result1 = interrupt_handler();
     printf("interrupt_handler err: %d \n", result1);
}

static err_code_t get_measurement_config_from_sensor(as7058_meas_config_t *p_meas_config,
                                                     uint32_t *p_agc_enabled_sub_sample_flags)
{
    err_code_t result;
    agc_configuration_t ags_configs[AGC_MAX_CHANNEL_CNT];
    uint8_t agc_configs_num = AGC_MAX_CHANNEL_CNT;
    uint8_t i;

    M_CHECK_NULL_POINTER(p_meas_config);
    M_CHECK_NULL_POINTER(p_agc_enabled_sub_sample_flags);

    memset(p_meas_config->reserved, 0, sizeof(p_meas_config->reserved));

    result =
        as7058_ifce_get_sample_periods(&p_meas_config->ppg_sample_period_us, &p_meas_config->ecg_seq1_sample_period_us,
                                       &p_meas_config->ecg_seq2_sample_period_us);

    if (ERR_SUCCESS == result) {
        result = as7058_ifce_get_fifo_mapping(&p_meas_config->fifo_map);
    }

    if (ERR_SUCCESS == result) {
        *p_agc_enabled_sub_sample_flags = AS7058_SUB_SAMPLE_FLAG_NONE;
        result = agc_get_configuration(ags_configs, &agc_configs_num);
    }
    if (ERR_SUCCESS == result) {
        for (i = 0; i < AGC_MAX_CHANNEL_CNT; i++) {
            if (i < agc_configs_num) {
                p_meas_config->agc_channels[i] = ags_configs[i].channel;
                if (AGC_MODE_DEFAULT == ags_configs[i].mode) {
                    *p_agc_enabled_sub_sample_flags |= M_AS7058_SUB_SAMPLE_ID_TO_FLAG(ags_configs[i].channel);
                }
            } else {
                p_meas_config->agc_channels[i] = AS7058_SUB_SAMPLE_ID_DISABLED;
            }
        }

        result = as7058_ifce_get_active_sar_sub_samples(&p_meas_config->sar_map);
    }

    if (ERR_SUCCESS == result) {
        result = as7058_ifce_get_sar_transfer_mode(&p_meas_config->sar_transfer_mode);
    }

    return result;
}

/******************************************************************************
 *                             GLOBAL FUNCTIONS                               *
 ******************************************************************************/

err_code_t as7058_initialize(const as7058_callback_t p_normal_callback,
                             const as7058_callback_special_measurement_t p_special_callback, const void *p_cb_param,
                             const char *p_interface_descr)
{
    err_code_t result;
    uint8_t id;

   // M_CHECK_NULL_POINTER(p_normal_callback);

    as7058_shutdown();

    result = as7058_osal_initialize();

    if (ERR_SUCCESS == result) {
        result = as7058_ifce_get_silicon_id(&id);
    }
    if ((ERR_SUCCESS == result) && (AS7058_SILICON_ID != id)) {
        result = ERR_IDENTIFICATION;
    }

    if (ERR_SUCCESS == result) {
        result = as7058_ifce_reset_chip();
    }

    if (ERR_SUCCESS == result) {
        g_dev_config.p_normal_callback = p_normal_callback;
        g_dev_config.p_special_callback = p_special_callback;
        g_dev_config.p_cb_param = p_cb_param;

        result = as7058_osal_register_int_handler(interrupt_handler);
    }

    if (ERR_SUCCESS == result) {
        result = agc_initialize();
    }

    if (ERR_SUCCESS == result) {
        result = as7058_eda_scaling_initialize();
    }
    if (ERR_SUCCESS == result) {
        result = as7058_bioz_initialize();
    }

    if (ERR_SUCCESS == result) {
        result = as7058_pd_offset_calibration_initialize();
    }

    if (ERR_SUCCESS != result) {
        as7058_shutdown();
    } else {
        g_dev_config.lib_state = LIB_STATE_CONFIGURATION;
        g_dev_config.is_meas_running = FALSE;
    }

    return result;
}

err_code_t as7058_shutdown(void)
{
    err_code_t result, result_osal, result_agc, result_eda_scaling, result_bioz, result_pd_offset_calibration;

    // DEBUG: Log entry into the shutdown function
     printk("as7058_shutdown: state = %d", g_dev_config.lib_state);

    if (LIB_STATE_UNINITIALIZED != g_dev_config.lib_state) {
         printk("as7058_shutdown: Entering if block to stop measurement");
        result = as7058_stop_measurement();

        if (ERR_SUCCESS == result) {
            // printk("as7058_shutdown: Measurement stopped, resetting chip");
            result = as7058_ifce_reset_chip();
        }
    } else {
         //printk("as7058_shutdown: Entering else block, already uninitialized");
        result = ERR_SUCCESS;
    }

    result_agc = agc_shutdown();
    if (ERR_SUCCESS == result) {
       // printk("as7058_shutdown: Entering else block, already uninitialized");
        result = result_agc;
    }

    result_eda_scaling = as7058_eda_scaling_shutdown();
    if (ERR_SUCCESS == result) {
        //printk("as7058_shutdown: Entering else block, already uninitialized");
        result = result_eda_scaling;
    }

    result_bioz = as7058_bioz_shutdown();
    if (ERR_SUCCESS == result) {
       // printk("as7058_shutdown: Entering else block, already uninitialized");
        result = result_bioz;
    }

    result_pd_offset_calibration = as7058_pd_offset_calibration_shutdown();
    if (ERR_SUCCESS == result) {
       // printk("as7058_shutdown: Entering else block, already uninitialized");
        result = result_pd_offset_calibration;
    }

    result_osal = as7058_osal_shutdown();
    if (ERR_SUCCESS == result) {
       // printk("as7058_shutdown: Entering else block, already uninitialized");
        result = result_osal;
    }

    memset(&g_dev_config, 0, sizeof(g_dev_config));

    return result;
}

err_code_t as7058_set_reg_group(as7058_reg_group_ids_t id, const uint8_t *p_data, uint8_t size)
{
    if (LIB_STATE_CONFIGURATION != g_dev_config.lib_state) {
        return ERR_PERMISSION;
    }

    if (AS7058_REG_GROUP_ID_ECG == id) {
        /* Store value of register BIOZ_CFG. */
        g_dev_config.reg_val_bioz_cfg = p_data[REG_INDEX__ECG__BIOZ_CFG];

        /* Copy register group buffer so that it is modifiable. */
        M_CHECK_SIZE(size, sizeof(as7058_reg_group_ecg_t));
        uint8_t modified_data[sizeof(as7058_reg_group_ecg_t)];
        memcpy(modified_data, p_data, sizeof(as7058_reg_group_ecg_t));

        /* To work around an issue with Revision A of the silicon, field gsr_en of register BIOZ_CFG must only be set
         * while a GSR measurement is in progress. Since it is not required to start a measurement immediately after
         * writing register values, the field is cleared in the register values buffer that gets written to the silicon.
         * If the field is set in the register values passed to the Chip Library, the Chip Library sets and clears the
         * register field in the silicon immediately before and after measurement, respectively. In the output of all
         * Chip Library functions to read register values, the register's value is always set to the value that has been
         * passed to the Chip Library, independent of the register's current value in the silicon. Note that this
         * workaround is only effective when the measurement is both started and stopped by calling the corresponding
         * Chip Library functions. */
        modified_data[REG_INDEX__ECG__BIOZ_CFG] &= ~REG_MASK__BIOZ_CFG__GSR_EN;

        return as7058_ifce_set_reg_group(id, modified_data, sizeof(as7058_reg_group_ecg_t));
    } else {
        return as7058_ifce_set_reg_group(id, p_data, size);
    }
}

err_code_t as7058_get_reg_group(as7058_reg_group_ids_t id, uint8_t *p_data, uint8_t *p_size)
{
    if (LIB_STATE_CONFIGURATION != g_dev_config.lib_state) {
        return ERR_PERMISSION;
    }

    M_CHECK_SUCCESS(as7058_ifce_get_reg_group(id, p_data, p_size));

    if (AS7058_REG_GROUP_ID_ECG == id) {
        /* Replace the value of register BIOZ_CFG with the value that has been passed to the Chip Library. See the
         * comments in as7058_set_reg_group and as7058_write_register for more information. */
        p_data[REG_INDEX__ECG__BIOZ_CFG] = g_dev_config.reg_val_bioz_cfg;
    }

    return ERR_SUCCESS;
}

err_code_t as7058_write_register(as7058_reg_addresses_t reg_addr, uint8_t reg_val)
{
    if (LIB_STATE_UNINITIALIZED == g_dev_config.lib_state) {
        return ERR_PERMISSION;
    }

    if (AS7058_REGADDR_BIOZ_CFG == reg_addr) {
        /* Store value of register BIOZ_CFG. */
        g_dev_config.reg_val_bioz_cfg = reg_val;

        /* To work around an issue with Revision A of the silicon, field gsr_en of register BIOZ_CFG must only be set
         * while a GSR measurement is in progress. Since it is not required to start a measurement immediately after
         * writing register values, the field is cleared in the register value that gets written to the silicon. If the
         * field is set in the register value passed to the Chip Library, the Chip Library sets and clears the register
         * field in the silicon immediately before and after measurement, respectively. In the output of all Chip
         * Library functions to read register values, the register's value is always set to the value that has been
         * passed to the Chip Library, independent of the register's current value in the silicon. Note that this
         * workaround is only effective when the measurement is both started and stopped by calling the corresponding
         * Chip Library functions. */
        reg_val &= ~REG_MASK__BIOZ_CFG__GSR_EN;
    }

    return as7058_ifce_write_register(reg_addr, reg_val);
}

err_code_t as7058_read_register(as7058_reg_addresses_t reg_addr, uint8_t *p_reg_val)
{
    if (LIB_STATE_UNINITIALIZED == g_dev_config.lib_state) {
        return ERR_PERMISSION;
    }

    M_CHECK_SUCCESS(as7058_ifce_read_register(reg_addr, p_reg_val));

    if (AS7058_REGADDR_BIOZ_CFG == reg_addr) {
        /* Replace the value of register BIOZ_CFG with the value that has been passed to the Chip Library. See the
         * comments in as7058_set_reg_group and as7058_write_register for more information. */
        *p_reg_val = g_dev_config.reg_val_bioz_cfg;
    }

    return ERR_SUCCESS;
}

err_code_t as7058_set_agc_config(const agc_configuration_t *p_agc_configs, uint8_t agc_config_num)
{
    if (LIB_STATE_CONFIGURATION != g_dev_config.lib_state) {
        return ERR_PERMISSION;
    }

    return agc_set_configuration(p_agc_configs, agc_config_num);
}

err_code_t as7058_get_agc_config(agc_configuration_t *p_agc_configs, uint8_t *p_agc_config_num)
{
    if (LIB_STATE_UNINITIALIZED == g_dev_config.lib_state) {
        return ERR_PERMISSION;
    }

    return agc_get_configuration(p_agc_configs, p_agc_config_num);
}

err_code_t as7058_get_measurement_config(as7058_meas_config_t *p_meas_config)
{
    err_code_t result;
    uint32_t agc_enabled_sub_sample_flags;
    M_CHECK_NULL_POINTER(p_meas_config);

    switch (g_dev_config.lib_state) {

    case LIB_STATE_CONFIGURATION:

        result = get_measurement_config_from_sensor(p_meas_config, &agc_enabled_sub_sample_flags);
        break;

    case LIB_STATE_MEASUREMENT:

        memcpy(p_meas_config, &g_dev_config.meas_config, sizeof(as7058_meas_config_t));
        result = ERR_SUCCESS;
        break;

    default:

        result = ERR_PERMISSION;
        break;
    }

    return result;
}

err_code_t as7058_start_measurement(as7058_meas_mode_t mode)
{
    err_code_t result;
    uint32_t active_agc_sub_samples;

    if (LIB_STATE_CONFIGURATION != g_dev_config.lib_state) {
        return ERR_PERMISSION;
    }

    M_CHECK_ARGUMENT_LOWER(mode, AS7058_MEAS_MODE_NUM);

    /* Update the measurement configuration */
    result = get_measurement_config_from_sensor(&g_dev_config.meas_config, &active_agc_sub_samples);

    /* Do not allow parallel AGC and SAR */
    if (ERR_SUCCESS == result) {

        /* Check whether any sub-samples are controlled by both AGC and SAR */
        if (active_agc_sub_samples & g_dev_config.meas_config.sar_map) {
            result = ERR_CONFIG;
        }
    }

    if (ERR_SUCCESS == result) {
        result = as7058_ifce_get_interrupt_enable(&g_dev_config.enabled_irqs);
    }

    if (ERR_SUCCESS == result) {
        result = as7058_ifce_get_fifo_threshold(&g_dev_config.fifo_threshold);
    }

    /* At least on sub sample should be enabled */
    if ((ERR_SUCCESS == result) && (0 == g_dev_config.meas_config.fifo_map)) {
        result = ERR_CONFIG;
    }

    /* Reset AGC first to set inital values for PD offset and LED current
       before measurement starts */
    if (ERR_SUCCESS == result) {
        result = agc_start_processing(&g_dev_config.meas_config, sizeof(g_dev_config.meas_config));
    }

    /* One-time clear of any latched interrupt before enabling line */
as7058_ifce_get_interrupt_status(&(as7058_interrupt_t){0});  // ignore result
as7058_ifce_get_fifo_level(&(uint16_t){0});                   // optional read to clear
/* Now enable GPIO IRQ */
as7058_osal_irq_enable(true);


    if ((ERR_SUCCESS == result) && (AS7058_MEAS_MODE_NORMAL != mode)) {
        /* Check that the special measurement callback was configured */
        if (NULL == g_dev_config.p_special_callback) {
            result = ERR_CONFIG;
        } else if (AS7058_MEAS_MODE_SPECIAL_SCALING_EDA == mode) {
            result = as7058_eda_scaling_start(g_dev_config.meas_config);
        } else if (AS7058_MEAS_MODE_SPECIAL_BIOZ == mode) {
            result = as7058_bioz_start(g_dev_config.meas_config);
        } else if (AS7058_MEAS_MODE_SPECIAL_PD_OFFSET_CALIBRATION == mode) {
            result = as7058_pd_offset_calibration_start(g_dev_config.meas_config);
        }
    }

    /* If the gsr_en field was set in the BIOZ_CFG register value passed to the Chip Library, set register BIOZ_CFG to
     * the stored register value. See the comments in as7058_set_reg_group and as7058_write_register for more
     * information. */
    if ((ERR_SUCCESS == result) && (g_dev_config.reg_val_bioz_cfg & REG_MASK__BIOZ_CFG__GSR_EN)) {
        result = as7058_ifce_write_register(AS7058_REGADDR_BIOZ_CFG, g_dev_config.reg_val_bioz_cfg);
    }

    if (ERR_SUCCESS == result) {
        g_dev_config.is_meas_running = TRUE;
        result = as7058_ifce_start_measurement();
    }

    if (ERR_SUCCESS == result) {
        g_dev_config.lib_state = LIB_STATE_MEASUREMENT;
        g_dev_config.mode = mode;
    } else {
        as7058_stop_measurement();
    }

    return result;
}

err_code_t as7058_stop_measurement(void)
{
    err_code_t result = ERR_DATA_TRANSFER;

    /* in as7058_stop_measurement() and/as7058_shutdown() */
as7058_osal_irq_enable(false);


    if (LIB_STATE_UNINITIALIZED == g_dev_config.lib_state) {
        return ERR_PERMISSION;
    }

    g_dev_config.is_meas_running = FALSE;

    result = as7058_ifce_stop_measurement();

    /* If starting the measurement did set the gsr_en field in register BIOZ_CFG, clear it now. See the comments in
     * as7058_set_reg_group and as7058_write_register for more information. */
    if ((ERR_SUCCESS == result) && (g_dev_config.reg_val_bioz_cfg & REG_MASK__BIOZ_CFG__GSR_EN)) {
        result = as7058_ifce_write_register(AS7058_REGADDR_BIOZ_CFG,
                                            (g_dev_config.reg_val_bioz_cfg & (~REG_MASK__BIOZ_CFG__GSR_EN)));
    }

    if (ERR_SUCCESS == result) {
        result = agc_stop_processing();
    }

    if (ERR_SUCCESS == result) {
        if (AS7058_MEAS_MODE_SPECIAL_SCALING_EDA == g_dev_config.mode) {
            result = as7058_eda_scaling_stop();
        } else if (AS7058_MEAS_MODE_SPECIAL_BIOZ == g_dev_config.mode) {
            result = as7058_bioz_stop();
        } else if (AS7058_MEAS_MODE_SPECIAL_PD_OFFSET_CALIBRATION == g_dev_config.mode) {
            result = as7058_pd_offset_calibration_stop();
        }
    }

    if (ERR_SUCCESS == result) {
        g_dev_config.lib_state = LIB_STATE_CONFIGURATION;
    }

    return result;
}

const char *as7058_get_version(void)
{
    return AS7058_CHIPLIB_VERSION;
}

err_code_t as7058_set_special_measurement_config(as7058_meas_mode_t mode, const void *p_config, uint16_t size)
{
    err_code_t result;

    if (LIB_STATE_CONFIGURATION != g_dev_config.lib_state) {
        return ERR_PERMISSION;
    }

    if (NULL == g_dev_config.p_special_callback) {
        return ERR_CONFIG;
    }

    M_CHECK_NULL_POINTER(p_config);

    if (AS7058_MEAS_MODE_SPECIAL_SCALING_EDA == mode) {
        if (sizeof(as7058_eda_scaling_config_t) == size) {
            result = as7058_eda_scaling_configure((const as7058_eda_scaling_config_t *)(p_config));
        } else {
            result = ERR_SIZE;
        }
    } else if (AS7058_MEAS_MODE_SPECIAL_BIOZ == mode) {
        if (sizeof(as7058_bioz_meas_config_t) == size) {
            result = as7058_bioz_configure((const as7058_bioz_meas_config_t *)(p_config));
        } else {
            result = ERR_SIZE;
        }
    } else if (AS7058_MEAS_MODE_SPECIAL_PD_OFFSET_CALIBRATION == mode) {
        if (sizeof(as7058_pd_offset_calibration_config_t) == size) {
            result = as7058_pd_offset_calibration_configure((const as7058_pd_offset_calibration_config_t *)(p_config));
        } else {
            result = ERR_SIZE;
        }
    } else {
        result = ERR_ARGUMENT;
    }

    return result;
}
