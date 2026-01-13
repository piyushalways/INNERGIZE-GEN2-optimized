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

#include "as7058_eda_scaling.h"
#include "as7058_extract.h"
#include "as7058_interface.h"
#include "as7058_osal_chiplib.h"
#include "as7058_typedefs.h"
#include "error_codes.h"
#include "std_inc.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

#define REG_BITS_BIOZ_SELECT__BIOZ_MEAS_SEL 0x70 /*!< BioZ measurement selection. */

#define REG_BITS_BIOZ_SELECT__BIOZ_MEAS_SEL__BIOIMPEDANCE 0x00 /*!< Normal impedance measurement. */
#define REG_BITS_BIOZ_SELECT__BIOZ_MEAS_SEL__SHORT 0x10        /*!< Short measurement. */
#define REG_BITS_BIOZ_SELECT__BIOZ_MEAS_SEL__1M 0x30           /*!< 2M resistor measurement. */

enum impedance_scaling_states {
    IMPEDANCE_SCALING_STATE_UNINITIALIZED = 0, /*!< Module is in uninitialized state. */
    IMPEDANCE_SCALING_STATE_CONFIGURATION,     /*!< Module is in configuration state. */
    IMPEDANCE_SCALING_STATE_PROCESS_SHORT,     /*!< Module is in processing state for short measurement. */
    IMPEDANCE_SCALING_STATE_PROCESS_RESISTOR,  /*!< Module is in processing state for resistor measurement. */
};

#define MAX_ADC_VALUE 0xFFFFF /*!< Maximum ADC value with 20 bits resolution. */

// TODO This value must be updated as soon we get the results from the manufacturing
#ifndef ADC_TEMP_SLOPE
#define ADC_TEMP_SLOPE                                                                                                 \
    1000000 /*!< Gain definition for temperature calculation scaled by 1000000. Divide by 1000000 to get the unscaled  \
                 value. Not used yet. */
#endif

struct scaling_eda_params {
    as7058_eda_scaling_config_t config;     /*!< Measurement configuration of the module. */
    as7058_eda_scaling_result_t result;     /*!< Internal saved measurement result of the module. */
    uint32_t adc_values[2];                 /*!< Sum of the ADC values for short and resistor measurement. */
    uint16_t adc_values_num[2];             /*!< Number of the ADC values for short and resistor measurement. */
    uint32_t temp_values;                   /*!< Sum of the temperature ADC values. */
    uint16_t temp_values_num;               /*!< Number of the temperature ADC values. */
    enum impedance_scaling_states state;    /*!< Current state of the EDA module. */
    as7058_extract_metadata_t extract_meta; /*!< Metadata for extracting channel data. */
    uint8_t bioz_select_reg_val;            /*!< Original register value of BIOZ_SELECT. */
    as7058_sub_sample_ids_t sub_id_eda;     /*!< Sub-sample ID of the EDA channel. */
    as7058_sub_sample_ids_t sub_id_temp;    /*!< Sub-sample ID of the temperature channel. */
};

/******************************************************************************
 *                                  GLOBALS                                   *
 ******************************************************************************/

static struct scaling_eda_params g_params; /*!< Data for running EDA scaling module. */

/******************************************************************************
 *                               LOCAL FUNCTIONS                              *
 ******************************************************************************/

static err_code_t configure_short_measurement(void)
{
    /* Configure short measurement */
    err_code_t result = as7058_ifce_write_register(
        AS7058_REGADDR_BIOZ_SELECT, g_params.bioz_select_reg_val | REG_BITS_BIOZ_SELECT__BIOZ_MEAS_SEL__SHORT);

    if (ERR_SUCCESS == result) {
        g_params.state = IMPEDANCE_SCALING_STATE_PROCESS_SHORT;
    }

    return result;
}

/******************************************************************************
 *                             GLOBAL FUNCTIONS                               *
 ******************************************************************************/

err_code_t as7058_eda_scaling_initialize(void)
{
    err_code_t result;

    result = as7058_eda_scaling_shutdown();

    if (ERR_SUCCESS == result) {
        g_params.state = IMPEDANCE_SCALING_STATE_CONFIGURATION;
    }

    return result;
}

err_code_t as7058_eda_scaling_configure(const as7058_eda_scaling_config_t *p_special_config)
{
    M_CHECK_NULL_POINTER(p_special_config);

    if ((0 == p_special_config->num_averages) ||
        ((UINT32_MAX / MAX_ADC_VALUE) < (uint32_t)p_special_config->num_averages)) {
        return ERR_ARGUMENT;
    }
    memcpy(&g_params.config, p_special_config, sizeof(as7058_eda_scaling_config_t));
    return ERR_SUCCESS;
}

err_code_t as7058_eda_scaling_start(as7058_meas_config_t meas_config)
{
    err_code_t result;
    int16_t resistor_error_milli_percent = 0;
    as7058_ecg_mux_signals_t ecg_mux_subs[AS7058_NUM_ECG_SUBS];
    uint8_t i;

    if (0 == g_params.config.num_averages) {
        return ERR_CONFIG;
    }

    result = as7058_ifce_get_ecg_mux_config(ecg_mux_subs, AS7058_NUM_ECG_SUBS);
    if (ERR_SUCCESS != result) {
        return result;
    }

    g_params.sub_id_eda = AS7058_SUB_SAMPLE_ID_DISABLED;
    g_params.sub_id_temp = AS7058_SUB_SAMPLE_ID_DISABLED;

    /* Check that ECG are defined. Temperature is optional. */
    for (i = 0; i < AS7058_NUM_ECG_SUBS; i++) {
        if (AS7058_ECG_MUX_EDA == ecg_mux_subs[i] && (AS7058_SUB_SAMPLE_ID_DISABLED == g_params.sub_id_eda)) {
            g_params.sub_id_eda = AS7058_SUB_SAMPLE_ID_ECG_SEQ1_SUB1 + i;
        } else if (AS7058_ECG_MUX_TEMP == ecg_mux_subs[i] && (AS7058_SUB_SAMPLE_ID_DISABLED == g_params.sub_id_temp)) {
            g_params.sub_id_temp = AS7058_SUB_SAMPLE_ID_ECG_SEQ1_SUB1 + i;
        }
    }
    if (AS7058_SUB_SAMPLE_ID_DISABLED == g_params.sub_id_eda ||
        !(meas_config.fifo_map & M_AS7058_SUB_SAMPLE_ID_TO_FLAG(g_params.sub_id_eda))) {
        result = ERR_CONFIG;
    }
    if (AS7058_SUB_SAMPLE_ID_DISABLED != g_params.sub_id_temp &&
        !(meas_config.fifo_map & M_AS7058_SUB_SAMPLE_ID_TO_FLAG(g_params.sub_id_temp))) {
        result = ERR_CONFIG;
    }
    if (ERR_SUCCESS == result) {
        result = as7058_ifce_get_1meg_error(&resistor_error_milli_percent);
    }

    if (ERR_SUCCESS == result) {
        const int32_t resistor = 1000000;
        g_params.result.ref_resistor =
            (uint32_t)(resistor + (int32_t)((int64_t)resistor * (int64_t)resistor_error_milli_percent / 1000 / 100));

        result = as7058_ifce_get_temp_adc_production(&g_params.result.ref_temperature_adc);

        g_params.result.slope = ADC_TEMP_SLOPE;
        g_params.temp_values = 0;
        g_params.temp_values_num = 0;
    }

    /* Configure impedance measurement with short */
    if (ERR_SUCCESS == result) {
        result = as7058_ifce_read_register(AS7058_REGADDR_BIOZ_SELECT, &g_params.bioz_select_reg_val);
    }
    if (ERR_SUCCESS == result) {
        /* Bio Impedance measurement must be selected for EDA */
        if (REG_BITS_BIOZ_SELECT__BIOZ_MEAS_SEL__BIOIMPEDANCE !=
            (REG_BITS_BIOZ_SELECT__BIOZ_MEAS_SEL & g_params.bioz_select_reg_val)) {
            result = ERR_CONFIG;
        }

        /* Configure short measurement */
        if (ERR_SUCCESS == result) {
            result = configure_short_measurement();
        }
    }

    if (ERR_SUCCESS == result) {

        /* Prepare extract metadata */
        memset(&g_params.extract_meta, 0, sizeof(g_params.extract_meta));
        g_params.extract_meta.fifo_map = meas_config.fifo_map;

        /* Reset measurement results */
        memset(g_params.adc_values, 0, sizeof(g_params.adc_values));
        memset(g_params.adc_values_num, 0, sizeof(g_params.adc_values_num));
    }

    return result;
}

err_code_t as7058_eda_scaling_stop(void)
{
    if (IMPEDANCE_SCALING_STATE_CONFIGURATION < g_params.state) {
        g_params.state = IMPEDANCE_SCALING_STATE_CONFIGURATION;
        return as7058_ifce_write_register(AS7058_REGADDR_BIOZ_SELECT, g_params.bioz_select_reg_val);
    }
    return ERR_SUCCESS;
}

err_code_t as7058_eda_scaling_process(const uint8_t *p_fifo_data, uint16_t fifo_data_size,
                                      const as7058_eda_scaling_result_t **pp_scaling_result)
{
    err_code_t result;
    static uint32_t adc_channel_data[AS7058_FIFO_DATA_BUFFER_SIZE / AS7058_FIFO_SAMPLE_SIZE];
    uint16_t adc_channel_data_num = AS7058_FIFO_DATA_BUFFER_SIZE / AS7058_FIFO_SAMPLE_SIZE;
    uint16_t i;
    uint8_t results_valid = FALSE;

    M_CHECK_NULL_POINTER(p_fifo_data);
    M_CHECK_NULL_POINTER(pp_scaling_result);

    if (IMPEDANCE_SCALING_STATE_CONFIGURATION >= g_params.state) {
        return ERR_PERMISSION;
    } else if (0 == g_params.config.num_averages) {
        return ERR_PERMISSION;
    }

    /* Extract temperature */
    if (AS7058_SUB_SAMPLE_ID_DISABLED != g_params.sub_id_temp) {
        result = as7058_extract_samples(g_params.sub_id_temp, p_fifo_data, fifo_data_size, adc_channel_data,
                                        &adc_channel_data_num, &g_params.extract_meta);
        if (ERR_SUCCESS == result) {
            for (i = 0; i < adc_channel_data_num; i++) {
                /* Prevent overflow for temperature averaging */
                if ((UINT32_MAX / MAX_ADC_VALUE) <= g_params.temp_values_num) {
                    break;
                }
                g_params.temp_values += adc_channel_data[i];
                g_params.temp_values_num++;
            }
        }
    }

    g_params.extract_meta.copy_recent_to_current = TRUE;

    adc_channel_data_num = AS7058_FIFO_DATA_BUFFER_SIZE / AS7058_FIFO_SAMPLE_SIZE;
    result = as7058_extract_samples(g_params.sub_id_eda, p_fifo_data, fifo_data_size, adc_channel_data,
                                    &adc_channel_data_num, &g_params.extract_meta);
    if (ERR_SUCCESS == result) {
        /* Detect if data start with EDA+ or EDA- */
        uint8_t start_with_eda_negative = g_params.adc_values_num[0] != g_params.adc_values_num[1];
        if (start_with_eda_negative) {
            g_params.adc_values[1] += adc_channel_data[0];
            g_params.adc_values_num[1]++;
        }
        /* EDA+ and EDA- change with every sub-sample. EDA+ is saved in first buffer, EDA- in the second one. */
        for (i = 0; i < adc_channel_data_num - start_with_eda_negative; i++) {
            g_params.adc_values[i % 2] += adc_channel_data[start_with_eda_negative + i];
            g_params.adc_values_num[i % 2]++;
            if (g_params.config.num_averages <= g_params.adc_values_num[1]) {
                break;
            }
        }
    }
    if (ERR_SUCCESS == result && (g_params.config.num_averages <= g_params.adc_values_num[0]) &&
        (g_params.config.num_averages <= g_params.adc_values_num[1])) {
        result = as7058_ifce_stop_measurement();

        /* Reset extract metadata */
        uint32_t fifo_map = g_params.extract_meta.fifo_map;
        memset(&g_params.extract_meta, 0, sizeof(g_params.extract_meta));
        g_params.extract_meta.fifo_map = fifo_map;

        if (ERR_SUCCESS == result) {
            g_params.adc_values[0] /= g_params.adc_values_num[0];
            g_params.adc_values[1] /= g_params.adc_values_num[1];

            if (IMPEDANCE_SCALING_STATE_PROCESS_SHORT == g_params.state) {

                /* Save the measured averaged values */
                g_params.result.short_p = g_params.adc_values[0];
                g_params.result.short_n = g_params.adc_values[1];

                uint8_t reg_val = g_params.bioz_select_reg_val | REG_BITS_BIOZ_SELECT__BIOZ_MEAS_SEL__1M;

                result = as7058_ifce_write_register(AS7058_REGADDR_BIOZ_SELECT, reg_val);
                if (ERR_SUCCESS == result) {
                    g_params.state = IMPEDANCE_SCALING_STATE_PROCESS_RESISTOR;
                    result = as7058_ifce_start_measurement();
                }
            } else if (IMPEDANCE_SCALING_STATE_PROCESS_RESISTOR == g_params.state) {

                /* Copy the values */
                g_params.result.resistor_p = g_params.adc_values[0];
                g_params.result.resistor_n = g_params.adc_values[1];

                /* Calculate temperature */
                if (g_params.temp_values_num) {
                    g_params.result.temperature_adc = g_params.temp_values / g_params.temp_values_num;
                    g_params.temp_values = 0;
                    g_params.temp_values_num = 0;
                } else {
                    /* Mark temperature value as invalid */
                    g_params.result.temperature_adc = UINT32_MAX;
                }

                results_valid = TRUE;

                result = configure_short_measurement();
                if (ERR_SUCCESS == result) {
                    result = as7058_ifce_start_measurement();
                }
            }
        }

        /* Reset counters */
        g_params.adc_values[0] = 0;
        g_params.adc_values[1] = 0;
        g_params.adc_values_num[0] = 0;
        g_params.adc_values_num[1] = 0;
    }

    if (ERR_SUCCESS == result) {
        if (FALSE == results_valid) {
            result = ERR_NO_DATA;
        } else {
            *pp_scaling_result = &g_params.result;
        }
    }
    return result;
}

err_code_t as7058_eda_scaling_shutdown(void)
{
    memset(&g_params, 0, sizeof(g_params));
    return ERR_SUCCESS;
}
