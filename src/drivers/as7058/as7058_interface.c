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

#include "as7058_interface.h"
#include "as7058_osal_chiplib.h"
#include "as7058_typedefs.h"
#include "error_codes.h"
#include "std_inc.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

#define REG_BITS_FIFO_CTRL__FIFO_CLEAR 0x80
#define REG_BITS_FIFO_CTRL__SAR_DATA_EN 0x02
#define REG_BITS_CHIP_CTRL__CHIP_RESET 0x01
#define REG_BITS_SEQ_START__START_SEQ 0x01

#define REG_BITS_ECG_BIOZ__ECG_BIOZ_OVS_MSK 0x07

#define REG_BITS_FIFO_LEVEL1__FIFO_OVERFLOW 0x04
#define FIFO_THRESHOLD_MSK 0x01FF

#define REG_BITS_ECG_SUBS__ECG2_EN 0x04
#define REG_BITS_ECG_SUBS__ECG1_EN 0x02
#define REG_BITS_ECG_SUBS__ECG1_SUBS 0x01

#define REG_BITS_PPG_MODEX__PPG_MODE_SUBX_SAR 0x03

#define REG_BITS_LED_SUBX__SUBX_DRV1_SEL 0x07
#define REG_BITS_LED_SUBX__SUBX_DRV2_SEL 0x70
#define REG_BITS_LED_SUBX__SUBX_DRV1_SEL_SHIFT 0
#define REG_BITS_LED_SUBX__SUBX_DRV2_SEL_SHIFT 4

#define REG_BITS_REVISION__REVISION 0x0F

#define RESISTOR_ERR_SIGN_MSK 0x200
#define RESISTOR_ERR_INTEGER_MSK 0x1F0
#define RESISTOR_ERR_INTEGER_SHIFT 4
#define RESISTOR_ERR_DECIMAL_MSK 0x00F
#define RESISTOR_ERR_DECIMAL_SHIFT 0

#define REG_BITS_PWR_ON__DEFAULT 0x01
#define REG_BITS_PWR_ISO__DEFAULT 0x1E

/*! Bit mask for a post-processing mode register field (for example: ppg1_pp_sub1 of ::AS7058_REGADDR_PPG1_PP1) that has
 *  been right-shifted to the least-significant bits. */
#define REG_PP_MODE_MASK (AS7058_PP_MODE_NUM - 1)

struct reg_group {
    uint8_t reg_count;
    uint8_t reg_start_addr;
};

/******************************************************************************
 *                                  GLOBALS                                   *
 ******************************************************************************/

const struct reg_group g_reg_groups[AS7058_REG_GROUP_ID_NUM] = {
    {sizeof(as7058_reg_group_power_t), AS7058_REGADDR_CLK_CFG},
    {sizeof(as7058_reg_group_control_t), AS7058_REGADDR_I2C_MODE},
    {sizeof(as7058_reg_group_led_t), AS7058_REGADDR_VCSEL_PASSWORD},
    {sizeof(as7058_reg_group_pd_t), AS7058_REGADDR_PDSEL_CFG},
    {sizeof(as7058_reg_group_ios_t), AS7058_REGADDR_IOS_PPG1_SUB1},
    {sizeof(as7058_reg_group_ppg_t), AS7058_REGADDR_PPGMOD_CFG1},
    {sizeof(as7058_reg_group_ecg_t), AS7058_REGADDR_BIOZ_CFG},
    {sizeof(as7058_reg_group_sinc_t), AS7058_REGADDR_PPG_SINC_CFGA},
    {sizeof(as7058_reg_group_iir_t), AS7058_REGADDR_IIR_CFG},
    {sizeof(as7058_reg_group_seq_t), AS7058_REGADDR_IRQ_ENABLE},
    {sizeof(as7058_reg_group_pp_t), AS7058_REGADDR_PP_CFG},
    {sizeof(as7058_reg_group_fifo_t), AS7058_REGADDR_FIFO_THRESHOLD},
};

/******************************************************************************
 *                               LOCAL FUNCTIONS                              *
 ******************************************************************************/

/*!
 * \brief Converts the value of an resistor error OTP register to a milli percent value (thousandths of a percent).
 *
 * \param[in] reg_value             OTP register value.
 *
 * \return Resistor error in thousandths of a percent.
 */
static int16_t convert_resistor_error_to_milli_percent(uint16_t reg_value)
{
    int16_t error_milli_percent;

    /* Value range: -31960 - 31960 */
    error_milli_percent = ((RESISTOR_ERR_INTEGER_MSK & reg_value) >> RESISTOR_ERR_INTEGER_SHIFT) * 1000;
    error_milli_percent += (((RESISTOR_ERR_DECIMAL_MSK & reg_value) >> RESISTOR_ERR_DECIMAL_SHIFT) + 1) * 60;

    if (0 == (RESISTOR_ERR_SIGN_MSK & reg_value)) {
        /* Negative value */
        error_milli_percent = 0 - error_milli_percent;
    }

    return error_milli_percent;
}

/*! Gets the location of the post-processing mode field for the given sub-sample. Provides the address of the containing
 *  register and the index of the least significant bit of the field. */
static err_code_t get_pp_mode_reg_addr_and_bit_index(as7058_sub_sample_ids_t sub_sample_id,
                                                     as7058_reg_addresses_t *p_addr, uint8_t *p_index)
{
    if (sub_sample_id >= AS7058_SUB_SAMPLE_ID_PPG1_SUB1 && sub_sample_id <= AS7058_SUB_SAMPLE_ID_PPG1_SUB4) {
        /* Register PPG1_PP1 contains the post-processing mode for PPG1 SUB1 to SUB4 starting with SUB1 mode located in
         * the two least significant bits */
        *p_addr = AS7058_REGADDR_PPG1_PP1;
        *p_index = (sub_sample_id - AS7058_SUB_SAMPLE_ID_PPG1_SUB1) * 2;
    } else if (sub_sample_id >= AS7058_SUB_SAMPLE_ID_PPG1_SUB5 && sub_sample_id <= AS7058_SUB_SAMPLE_ID_PPG1_SUB8) {
        /* Register PPG1_PP2 contains the post-processing mode for PPG1 SUB5 to SUB8 starting with SUB5 mode located in
         * the two least significant bits */
        *p_addr = AS7058_REGADDR_PPG1_PP2;
        *p_index = (sub_sample_id - AS7058_SUB_SAMPLE_ID_PPG1_SUB5) * 2;
    } else if (sub_sample_id >= AS7058_SUB_SAMPLE_ID_PPG2_SUB1 && sub_sample_id <= AS7058_SUB_SAMPLE_ID_PPG2_SUB4) {
        /* Register PPG2_PP1 contains the post-processing mode for PPG2 SUB1 to SUB4 starting with SUB1 mode located in
         * the two least significant bits */
        *p_addr = AS7058_REGADDR_PPG2_PP1;
        *p_index = (sub_sample_id - AS7058_SUB_SAMPLE_ID_PPG2_SUB1) * 2;
    } else if (sub_sample_id >= AS7058_SUB_SAMPLE_ID_PPG2_SUB5 && sub_sample_id <= AS7058_SUB_SAMPLE_ID_PPG2_SUB8) {
        /* Register PPG2_PP2 contains the post-processing mode for PPG2 SUB5 to SUB8 starting with SUB5 mode located in
         * the two least significant bits */
        *p_addr = AS7058_REGADDR_PPG2_PP2;
        *p_index = (sub_sample_id - AS7058_SUB_SAMPLE_ID_PPG2_SUB5) * 2;
    } else {
        /* Only sub-samples of the PPG modulators have post-processing configs */
        return ERR_ARGUMENT;
    }

    return ERR_SUCCESS;
}

/******************************************************************************
 *                             GLOBAL FUNCTIONS                               *
 ******************************************************************************/

err_code_t as7058_ifce_write_register(as7058_reg_addresses_t reg_addr, uint8_t reg_val)
{
    return as7058_osal_write_registers(reg_addr, sizeof(reg_val), &reg_val);
}

err_code_t as7058_ifce_read_register(as7058_reg_addresses_t reg_addr, uint8_t *p_reg_val)
{
    M_CHECK_NULL_POINTER(p_reg_val);
    return as7058_osal_read_registers(reg_addr, sizeof(*p_reg_val), p_reg_val);
}

err_code_t as7058_ifce_reset_chip(void)
{
    err_code_t result;
    uint8_t value = 0;

    result = as7058_ifce_write_register(AS7058_REGADDR_CHIP_CTRL, REG_BITS_CHIP_CTRL__CHIP_RESET);
    if (ERR_SUCCESS == result) {
        /* Read register to get reset status bit.
           Reading of this register clears this bit */
        result = as7058_ifce_read_register(AS7058_REGADDR_CHIP_CTRL, &value);
    }

    /* Registers PWR_ON, PWR_ISO are not reset by CHIP_RESET. Will be set separately */
    if (ERR_SUCCESS == result) {
        result = as7058_ifce_write_register(AS7058_REGADDR_PWR_ISO, REG_BITS_PWR_ISO__DEFAULT);
    }
    if (ERR_SUCCESS == result) {
        result = as7058_ifce_write_register(AS7058_REGADDR_PWR_ON, REG_BITS_PWR_ON__DEFAULT);
    }

    return result;
}

err_code_t as7058_ifce_get_silicon_id(uint8_t *p_silicon_id)
{
    return as7058_ifce_read_register(AS7058_REGADDR_SILICON_ID, p_silicon_id);
}

err_code_t as7058_ifce_get_product_id(uint8_t *p_product_id)
{
    return as7058_ifce_read_register(AS7058_REGADDR_PRODUCT_ID, p_product_id);
}

err_code_t as7058_ifce_get_revision(uint8_t *p_revision)
{
    err_code_t result;

    M_CHECK_NULL_POINTER(p_revision);

    result = as7058_ifce_read_register(AS7058_REGADDR_REVISION, p_revision);
    if (ERR_SUCCESS == result) {
        *p_revision &= REG_BITS_REVISION__REVISION;
    }

    return result;
}

err_code_t as7058_ifce_get_2k_error(int16_t *p_2k_error)
{
    err_code_t result;
    uint16_t reg_value;

    M_CHECK_NULL_POINTER(p_2k_error);

    result = as7058_osal_read_registers(AS7058_REGADDR_OTP_BIOZ_REF_L, sizeof(reg_value), (uint8_t *)&reg_value);
    if (ERR_SUCCESS == result) {
        *p_2k_error = convert_resistor_error_to_milli_percent(reg_value);
    }

    return result;
}

err_code_t as7058_ifce_get_1meg_error(int16_t *p_1meg_error)
{
    err_code_t result;
    uint16_t reg_value;

    M_CHECK_NULL_POINTER(p_1meg_error);

    result = as7058_osal_read_registers(AS7058_REGADDR_OTP_GSR_REF_L, sizeof(reg_value), (uint8_t *)&reg_value);
    if (ERR_SUCCESS == result) {
        *p_1meg_error = convert_resistor_error_to_milli_percent(reg_value);
    }

    return result;
}

err_code_t as7058_ifce_get_temp_adc_production(uint32_t *p_temp_adc)
{
    err_code_t result;
    uint16_t reg_value;

    M_CHECK_NULL_POINTER(p_temp_adc);

    result = as7058_osal_read_registers(AS7058_REGADDR_OTP_TEMP_REF_L, sizeof(reg_value), (uint8_t *)&reg_value);
    if (ERR_SUCCESS == result) {
        *p_temp_adc = reg_value << 4;
    }

    return result;
}

err_code_t as7058_ifce_clear_fifo(void)
{
    err_code_t result;
    uint8_t reg_val;

    result = as7058_ifce_read_register(AS7058_REGADDR_FIFO_CTRL, &reg_val);

    if (ERR_SUCCESS == result) {
        result = as7058_ifce_write_register(AS7058_REGADDR_FIFO_CTRL, reg_val | REG_BITS_FIFO_CTRL__FIFO_CLEAR);
    }

    return result;
}

err_code_t as7058_ifce_get_fifo_level(uint16_t *p_fifo_level)
{
    err_code_t result;

    M_CHECK_NULL_POINTER(p_fifo_level);

    result = as7058_osal_read_registers(AS7058_REGADDR_FIFO_LEVEL0, sizeof(*p_fifo_level), (uint8_t *)p_fifo_level);
    if ((ERR_SUCCESS == result) && ((REG_BITS_FIFO_LEVEL1__FIFO_OVERFLOW << 8) & *p_fifo_level)) {
        result = ERR_OVERFLOW;
    }
    return result;
}

err_code_t as7058_ifce_get_fifo_threshold(uint16_t *p_fifo_threshold)
{
    err_code_t result;

    M_CHECK_NULL_POINTER(p_fifo_threshold);

    result = as7058_osal_read_registers(AS7058_REGADDR_FIFO_THRESHOLD, sizeof(*p_fifo_threshold),
                                        (uint8_t *)p_fifo_threshold);
    if (ERR_SUCCESS == result) {
        *p_fifo_threshold &= FIFO_THRESHOLD_MSK;

        /* Increment because interrupt fires only if FIFO_LEVEL > FIFO_THRESHOLD and not FIFO_LEVEL >= FIFO_THRESHOLD */
        /* Prevent division by zero */
        (*p_fifo_threshold)++;
    }
    return result;
}

err_code_t as7058_ifce_get_interrupt_status(as7058_interrupt_t *p_status)
{
    return as7058_ifce_read_register(AS7058_REGADDR_STATUS, (uint8_t *)p_status);
}

err_code_t as7058_ifce_get_sub_status_registers(as7058_interrupt_t irqs, as7058_status_events_t *p_status_registers)
{
    err_code_t result = ERR_SUCCESS;

    M_CHECK_NULL_POINTER(p_status_registers);

    memset(p_status_registers, 0, sizeof(as7058_status_events_t));

    if (irqs.asat) {
        result = as7058_osal_read_registers(AS7058_REGADDR_STATUS_ASATA,
                                            AS7058_REGADDR_STATUS_ASATB - AS7058_REGADDR_STATUS_ASATA + 1,
                                            &(p_status_registers->status_asata));
    }
    if ((ERR_SUCCESS == result) && irqs.leadoff) {
        result = as7058_ifce_read_register(AS7058_REGADDR_STATUS_LEADOFF, &(p_status_registers->status_leadoff));
    }
    if ((ERR_SUCCESS == result) && irqs.led_lowvds) {
        result = as7058_ifce_read_register(AS7058_REGADDR_STATUS_LED, &(p_status_registers->status_led));
    }
    if ((ERR_SUCCESS == result) && irqs.sequencer) {
        result = as7058_ifce_read_register(AS7058_REGADDR_STATUS_SEQ, &(p_status_registers->status_seq));
    }
    if ((ERR_SUCCESS == result) && irqs.vcsel) {
        result = as7058_osal_read_registers(AS7058_REGADDR_STATUS_VCSEL,
                                            AS7058_REGADDR_STATUS_VCSEL_VDD - AS7058_REGADDR_STATUS_VCSEL + 1,
                                            &(p_status_registers->status_vcsel));
    }

    /* We have no sub status register for that. Therefore we put the flag directly inside the structure */
    p_status_registers->status_iir = irqs.iir_overflow;

    return result;
}

err_code_t as7058_ifce_get_interrupt_enable(as7058_interrupt_t *p_enable)
{
    return as7058_ifce_read_register(AS7058_REGADDR_IRQ_ENABLE, (uint8_t *)p_enable);
}

err_code_t as7058_ifce_set_reg_group(as7058_reg_group_ids_t id, const uint8_t *p_data, uint8_t size)
{
    err_code_t result;

    M_CHECK_NULL_POINTER(p_data);
    M_CHECK_ARGUMENT_LOWER(id, AS7058_REG_GROUP_ID_NUM);
    M_CHECK_SIZE(size, g_reg_groups[id].reg_count);

    if (AS7058_REG_GROUP_ID_IIR == id) {
        result = as7058_ifce_write_register(g_reg_groups[id].reg_start_addr, p_data[0]);
        if (ERR_SUCCESS == result) {
            /* Set sub-address to zero, auto-increment is supported */
            result = as7058_ifce_write_register(AS7058_REGADDR_IIR_COEFF_ADDR, 0);
        }
        if (ERR_SUCCESS == result) {
            /* Decrease reg_count by 2 because of config register and padding byte */
            result = as7058_osal_write_registers(
                AS7058_REGADDR_IIR_COEFF_DATA, g_reg_groups[id].reg_count - 2,
                (uint8_t *)(((as7058_reg_group_iir_t *)p_data)->reg_vals.iir_coeff_data_sos));
        }
    } else if (AS7058_REG_GROUP_ID_PWR == id) {
        /* Special handling of this register group because registers are not in one address range and power registers
         * need to be set first. */
        result = as7058_osal_write_registers(AS7058_REGADDR_PWR_ON, 2, p_data);
        if (ERR_SUCCESS == result) {
            result = as7058_osal_write_registers(g_reg_groups[id].reg_start_addr, g_reg_groups[id].reg_count - 2,
                                                 p_data + 2);
        }
    } else if (AS7058_REG_GROUP_ID_CTRL == id) {
        /* To work around an issue with the silicon when an I2C burst write modifies register I2C_MODE, write register
         * I2C_MODE (first register of this register group) in a separate I2C transfer. */
        result = as7058_osal_write_registers(g_reg_groups[id].reg_start_addr, 1, p_data);
        if (ERR_SUCCESS == result) {
            result = as7058_osal_write_registers(g_reg_groups[id].reg_start_addr + 1, g_reg_groups[id].reg_count - 1,
                                                 p_data + 1);
        }
    } else {
        result = as7058_osal_write_registers(g_reg_groups[id].reg_start_addr, g_reg_groups[id].reg_count, p_data);
    }

    return result;
}

err_code_t as7058_ifce_get_reg_group(as7058_reg_group_ids_t id, uint8_t *p_data, uint8_t *p_size)
{
    err_code_t result;

    M_CHECK_ARGUMENT_LOWER(id, AS7058_REG_GROUP_ID_NUM);
    M_CHECK_NULL_POINTER(p_size);

    /* Return size of given group ID */
    if ((NULL == p_data) && (0 == *p_size)) {
        *p_size = g_reg_groups[id].reg_count;
        return ERR_SUCCESS;
    }

    M_CHECK_NULL_POINTER(p_data);

    if (g_reg_groups[id].reg_count > *p_size) {
        return ERR_SIZE;
    }

    if (AS7058_REG_GROUP_ID_IIR == id) {
        result = as7058_ifce_read_register(g_reg_groups[id].reg_start_addr, p_data);
        if (ERR_SUCCESS == result) {
            /* Set sub-address to zero, auto-increment is supported */
            result = as7058_ifce_write_register(AS7058_REGADDR_IIR_COEFF_ADDR, 0);
        }
        if (ERR_SUCCESS == result) {
            ((as7058_reg_group_iir_t *)p_data)->reg_vals.reserved = 0; /* Set reserved byte to zero */
            /* Decrease reg_count by 2 because of config register and padding byte */
            result = as7058_osal_read_registers(
                AS7058_REGADDR_IIR_COEFF_DATA, g_reg_groups[id].reg_count - 2,
                (uint8_t *)(((as7058_reg_group_iir_t *)p_data)->reg_vals.iir_coeff_data_sos));
        }
    } else if (AS7058_REG_GROUP_ID_PWR == id) {
        result = as7058_osal_read_registers(AS7058_REGADDR_PWR_ON, 2, p_data);
        if (ERR_SUCCESS == result) {
            result =
                as7058_osal_read_registers(g_reg_groups[id].reg_start_addr, g_reg_groups[id].reg_count - 2, p_data + 2);
        }
    } else {
        result = as7058_osal_read_registers(g_reg_groups[id].reg_start_addr, g_reg_groups[id].reg_count, p_data);
    }

    *p_size = g_reg_groups[id].reg_count;

    return result;
}

err_code_t as7058_ifce_get_sample_periods(uint32_t *p_ppg_sample_period_us, uint32_t *p_ecg_seq1_sample_period_us,
                                          uint32_t *p_ecg_seq2_sample_period_us)
{
    const uint32_t base_clock_ns = 31250;
    err_code_t result;
    uint16_t ppg_freq_reg;
    struct frequencies {
        uint16_t ecg_freq;
        uint16_t ecg1_freqdiv;
        uint16_t ecg2_freqdiv;
    } ecg_freq_regs;
    uint8_t average = 0;
    as7058_ecg_mux_signals_t ecg_mux_signals[AS7058_NUM_ECG_SUBS];

    M_CHECK_NULL_POINTER(p_ppg_sample_period_us);
    M_CHECK_NULL_POINTER(p_ecg_seq1_sample_period_us);
    M_CHECK_NULL_POINTER(p_ecg_seq2_sample_period_us);

    result = as7058_osal_read_registers(AS7058_REGADDR_PPG_FREQL, sizeof(ppg_freq_reg), (uint8_t *)&ppg_freq_reg);
    if (ERR_SUCCESS == result) {
        *p_ppg_sample_period_us = (uint32_t)DIV64_U64((uint64_t)base_clock_ns * (ppg_freq_reg + 1), 1000);

        result = as7058_osal_read_registers(AS7058_REGADDR_ECG_FREQL, sizeof(ecg_freq_regs), (uint8_t *)&ecg_freq_regs);
    }
    if (ERR_SUCCESS == result) {
        const uint32_t base_sample_period = base_clock_ns * (ecg_freq_regs.ecg_freq + 1);
        *p_ecg_seq1_sample_period_us =
            (uint32_t)DIV64_U64((uint64_t)base_sample_period * (ecg_freq_regs.ecg1_freqdiv + 1), 1000);
        *p_ecg_seq2_sample_period_us =
            (uint32_t)DIV64_U64((uint64_t)base_sample_period * (ecg_freq_regs.ecg2_freqdiv + 1), 1000);

        /* Because BioZ supports averaging, the sample period needs to be modified if enabled */
        result = as7058_osal_read_registers(AS7058_REGADDR_ECG_BIOZ, sizeof(average), &average);
    }
    if ((ERR_SUCCESS == result) && (average & REG_BITS_ECG_BIOZ__ECG_BIOZ_OVS_MSK)) {
        average = 1 << (average & REG_BITS_ECG_BIOZ__ECG_BIOZ_OVS_MSK);
        result = as7058_ifce_get_ecg_mux_config(ecg_mux_signals, AS7058_NUM_ECG_SUBS);
        if (ERR_SUCCESS == result) {
            /* Chip only performs averaging for AS7058_ECG_MUX_I and AS7058_ECG_MUX_Q, all other ECG multiplexer signals
             * are never averaged */
            // TODO If we mix on sequence 1 an averaged signal with an non-averaged signal then we get the wrong sample
            // period for the non-averaged signals.
            uint32_t ecg_mux_flags = (1 << AS7058_ECG_MUX_I) | (1 << AS7058_ECG_MUX_Q);
            if (((1 << ecg_mux_signals[0]) | (1 << ecg_mux_signals[1])) & ecg_mux_flags) {
                *p_ecg_seq1_sample_period_us /= average;
            }
            if ((1 << ecg_mux_signals[2]) & ecg_mux_flags) {
                *p_ecg_seq2_sample_period_us /= average;
            }
        }
    }

    return result;
}

err_code_t as7058_ifce_start_measurement(void)
{
    err_code_t result;
    uint8_t irq_status[10];

    /* Clear FIFO level register and possible active interrupt pin */
    result = as7058_ifce_clear_fifo();

    /* Read old interrupt status register to reset interrupt pin */
    if (ERR_SUCCESS == result) {
        result = as7058_osal_read_registers(AS7058_REGADDR_STATUS_SEQ, sizeof(irq_status), irq_status);
    }
    /* Read the main status register in a separate call again to give chip enough time to reset internal status
     * registers */
    if (ERR_SUCCESS == result) {
        result = as7058_osal_read_registers(AS7058_REGADDR_STATUS, 1, irq_status);
    }
    if ((ERR_SUCCESS == result) && (0 != irq_status[0])) {
        result = ERR_SENSOR_CONFIG;
    }

    /* Start the measurement */
    if (ERR_SUCCESS == result) {
        result = as7058_ifce_write_register(AS7058_REGADDR_SEQ_START, REG_BITS_SEQ_START__START_SEQ);
    }

    return result;
}

err_code_t as7058_ifce_stop_measurement(void)
{
    err_code_t result;
    uint8_t retry = 255;
    uint8_t reg_value;

    result = as7058_ifce_write_register(AS7058_REGADDR_SEQ_START, 0);

    /* Wait for stopped measurement */
    while ((ERR_SUCCESS == result) && (retry-- != 0)) {
        result = as7058_ifce_read_register(AS7058_REGADDR_SEQ_START, &reg_value);
        if ((ERR_SUCCESS == result) && (0 == (reg_value & REG_BITS_SEQ_START__START_SEQ))) {
            break;
        }
    }

    /* It seems that there is a bug in the chip where the measurement is not stopped correctly.
       Stopping the measurement again helps to fix it. */
    if (ERR_SUCCESS == result) {
        result = as7058_ifce_write_register(AS7058_REGADDR_SEQ_START, 0);
    }

    return result;
}

err_code_t as7058_ifce_get_fifo_data(uint8_t *p_data, uint16_t data_num)
{
    M_CHECK_NULL_POINTER(p_data);
    return as7058_osal_read_registers(AS7058_REGADDR_FIFOL, data_num, p_data);
}

err_code_t as7058_ifce_get_fifo_mapping(uint32_t *p_fifo_map)
{
    err_code_t result;
    uint8_t ppg_subs[2];
    uint8_t ecg_subs;

    M_CHECK_NULL_POINTER(p_fifo_map);

    result = as7058_osal_read_registers(AS7058_REGADDR_PPG1_SUB_EN, sizeof(ppg_subs), ppg_subs);
    if (ERR_SUCCESS == result) {
        result = as7058_ifce_read_register(AS7058_REGADDR_ECG_SUBS, &ecg_subs);
    }
    if (ERR_SUCCESS == result) {
        /* Map register contents to sub-sample flags, see ::as7058_sub_sample_flags */
        *p_fifo_map = ppg_subs[0] | ppg_subs[1] << 8;
        if (REG_BITS_ECG_SUBS__ECG2_EN & ecg_subs) {
            *p_fifo_map |= AS7058_SUB_SAMPLE_FLAG_ECG_SEQ2_SUB1;
        }
        /* ECG1_EN is enabled if sequence 1 is enabled, ECG1_SUBS describes the number of sub-samples */
        if (REG_BITS_ECG_SUBS__ECG1_EN & ecg_subs) {
            *p_fifo_map |= AS7058_SUB_SAMPLE_FLAG_ECG_SEQ1_SUB1;
            if (REG_BITS_ECG_SUBS__ECG1_SUBS & ecg_subs) {
                *p_fifo_map |= AS7058_SUB_SAMPLE_FLAG_ECG_SEQ1_SUB2;
            }
        }
    }
    return result;
}

err_code_t as7058_ifce_get_active_sar_sub_samples(uint32_t *p_active_sar)
{
    err_code_t result;
    uint8_t ppg_mode[AS7058_REGADDR_PPG_MODE8 - AS7058_REGADDR_PPG_MODE1 + 1];
    uint8_t i;

    M_CHECK_NULL_POINTER(p_active_sar);

    result = as7058_osal_read_registers(AS7058_REGADDR_PPG_MODE1, sizeof(ppg_mode), ppg_mode);
    if (ERR_SUCCESS == result) {
        /* Map register contents to sub-sample flags, see ::as7058_sub_sample_flags */
        *p_active_sar = AS7058_SUB_SAMPLE_FLAG_NONE;
        for (i = 0; i < sizeof(ppg_mode); i++) {
            if (REG_BITS_PPG_MODEX__PPG_MODE_SUBX_SAR == (REG_BITS_PPG_MODEX__PPG_MODE_SUBX_SAR & ppg_mode[i])) {
                *p_active_sar |= (AS7058_SUB_SAMPLE_FLAG_PPG1_SUB1 | AS7058_SUB_SAMPLE_FLAG_PPG2_SUB1) << i;
            }
        }
    }

    return result;
}

err_code_t as7058_ifce_get_sar_transfer_mode(as7058_sar_transfer_mode_t *p_sar_transfer_mode)
{
    uint8_t fifo_ctrl_reg;
    err_code_t result;

    M_CHECK_NULL_POINTER(p_sar_transfer_mode);

    result = as7058_ifce_read_register(AS7058_REGADDR_FIFO_CTRL, &fifo_ctrl_reg);
    if (ERR_SUCCESS == result) {
        *p_sar_transfer_mode = (REG_BITS_FIFO_CTRL__SAR_DATA_EN & fifo_ctrl_reg) ? AS7058_SAR_TRANSFER_MODE_INLINE
                                                                                 : AS7058_SAR_TRANSFER_MODE_SEPARATE;
    }

    return result;
}

err_code_t as7058_ifce_set_led_current(as7058_led_ids_t led_id, uint8_t current)
{
    if (AS7058_LED_NUM_MAX <= led_id) {
        return ERR_ARGUMENT;
    }

    return as7058_ifce_write_register(AS7058_REGADDR_LED1_ICTRL + led_id, current);
}

err_code_t as7058_ifce_get_led_current(as7058_led_ids_t led_id, uint8_t *p_current)
{
    if (AS7058_LED_NUM_MAX <= led_id) {
        return ERR_ARGUMENT;
    }

    return as7058_ifce_read_register(AS7058_REGADDR_LED1_ICTRL + led_id, p_current);
}

err_code_t as7058_ifce_set_pd_offset(as7058_sub_sample_ids_t sub_sample_id, uint8_t ios)
{
    if (sub_sample_id < AS7058_SUB_SAMPLE_ID_PPG1_SUB1 || sub_sample_id > AS7058_SUB_SAMPLE_ID_PPG2_SUB8) {
        /* Only sub-samples of the PPG modulators have PD configs */
        return ERR_ARGUMENT;
    }

    /* PD offset registers (IOS_PPGx_SUBy) are consecutive and use the same order as as7058_sub_sample_ids, i.e. an
     * as7058_sub_sample_ids value can be mapped to a register address using an offset */
    uint8_t reg_addr = AS7058_REGADDR_IOS_PPG1_SUB1 + (sub_sample_id - AS7058_SUB_SAMPLE_ID_PPG1_SUB1);

    /* Set PD offset */
    return as7058_ifce_write_register(reg_addr, ios);
}

err_code_t as7058_ifce_get_pd_offset(as7058_sub_sample_ids_t sub_sample_id, uint8_t *p_ios)
{
    if (sub_sample_id < AS7058_SUB_SAMPLE_ID_PPG1_SUB1 || sub_sample_id > AS7058_SUB_SAMPLE_ID_PPG2_SUB8) {
        /* Only sub-samples of the PPG modulators have PD configs */
        return ERR_ARGUMENT;
    }

    /* PD offset registers (IOS_PPGx_SUBy) are consecutive and use the same order as as7058_sub_sample_ids, i.e. an
     * as7058_sub_sample_ids value can be mapped to a register address using an offset */
    uint8_t reg_addr = AS7058_REGADDR_IOS_PPG1_SUB1 + (sub_sample_id - AS7058_SUB_SAMPLE_ID_PPG1_SUB1);

    /* Get PD offset */
    return as7058_ifce_read_register(reg_addr, p_ios);
}

err_code_t as7058_ifce_get_sub_sample_led_config(as7058_sub_sample_ids_t sub_sample_id, uint8_t *p_led_config)
{
    uint8_t reg_addr, reg_content;
    uint8_t drv1 /* LED 1 - 4 */, drv2 /* LED 5 - 8 */;
    err_code_t result;

    M_CHECK_NULL_POINTER(p_led_config);

    if ((AS7058_SUB_SAMPLE_ID_DISABLED == sub_sample_id) || (AS7058_SUB_SAMPLE_ID_PPG2_SUB8 < sub_sample_id)) {
        return ERR_ARGUMENT;
    }

    /* PPG offsets are the same for PPG1 and PPG2, IDs have an offset of 1 */
    reg_addr = sub_sample_id + AS7058_REGADDR_LED_SUB1 - 1;
    if (AS7058_SUB_SAMPLE_ID_PPG1_SUB8 < sub_sample_id) {
        reg_addr -= AS7058_SUB_SAMPLE_ID_PPG2_SUB1 - 1;
    }

    result = as7058_ifce_read_register(reg_addr, &reg_content);
    if (ERR_SUCCESS == result) {
        *p_led_config = 0;
        drv1 = (reg_content & REG_BITS_LED_SUBX__SUBX_DRV1_SEL) >> REG_BITS_LED_SUBX__SUBX_DRV1_SEL_SHIFT;
        if (drv1) {
            *p_led_config |= 0x01 << (drv1 - 1); /* Map LED1-4 to bit positions 0-3 */
        }
        drv2 = (reg_content & REG_BITS_LED_SUBX__SUBX_DRV2_SEL) >> REG_BITS_LED_SUBX__SUBX_DRV2_SEL_SHIFT;
        if (drv2) {
            *p_led_config |= 0x10 << (drv2 - 1); /* Map LED5-8 to bit positions 4-7 */
        }
    }

    return result;
}

err_code_t as7058_ifce_set_sub_sample_pd_config(as7058_sub_sample_ids_t sub_sample_id, uint8_t pd_config)
{
    if (sub_sample_id < AS7058_SUB_SAMPLE_ID_PPG1_SUB1 || sub_sample_id > AS7058_SUB_SAMPLE_ID_PPG2_SUB8) {
        /* Only sub-samples of the PPG modulators have PD configs */
        return ERR_ARGUMENT;
    }

    /* PD selection registers (PPGx_PDSELy) are consecutive and use the same order as as7058_sub_sample_ids, i.e. an
     * as7058_sub_sample_ids value can be mapped to a register address using an offset */
    uint8_t reg_addr = AS7058_REGADDR_PPG1_PDSEL1 + (sub_sample_id - AS7058_SUB_SAMPLE_ID_PPG1_SUB1);

    return as7058_ifce_write_register(reg_addr, pd_config);
}

err_code_t as7058_ifce_get_sub_sample_pd_config(as7058_sub_sample_ids_t sub_sample_id, uint8_t *p_pd_config)
{
    if (sub_sample_id < AS7058_SUB_SAMPLE_ID_PPG1_SUB1 || sub_sample_id > AS7058_SUB_SAMPLE_ID_PPG2_SUB8) {
        /* Only sub-samples of the PPG modulators have PD configs */
        return ERR_ARGUMENT;
    }

    /* PD selection registers (PPGx_PDSELy) are consecutive and use the same order as as7058_sub_sample_ids, i.e. an
     * as7058_sub_sample_ids value can be mapped to a register address using an offset */
    uint8_t reg_addr = AS7058_REGADDR_PPG1_PDSEL1 + (sub_sample_id - AS7058_SUB_SAMPLE_ID_PPG1_SUB1);

    return as7058_ifce_read_register(reg_addr, p_pd_config);
}

err_code_t as7058_ifce_set_sub_sample_pp_mode(as7058_sub_sample_ids_t sub_sample_id, as7058_pp_modes_t pp_mode)
{
    if (pp_mode > REG_PP_MODE_MASK) {
        /* Invalid post-processing mode */
        return ERR_ARGUMENT;
    }

    /* Get register address and lower bit index of field to modify */
    uint8_t addr;
    uint8_t bit_index;
    M_CHECK_SUCCESS(get_pp_mode_reg_addr_and_bit_index(sub_sample_id, &addr, &bit_index));

    /* Read register and replace corresponding bits */
    uint8_t value;
    M_CHECK_SUCCESS(as7058_ifce_read_register(addr, &value));
    value &= ~(REG_PP_MODE_MASK << bit_index);
    value |= pp_mode << bit_index;

    return as7058_ifce_write_register(addr, value);
}

err_code_t as7058_ifce_get_sub_sample_pp_mode(as7058_sub_sample_ids_t sub_sample_id, as7058_pp_modes_t *p_pp_mode)
{
    M_CHECK_NULL_POINTER(p_pp_mode);

    /* Get register address and lower bit index of field to read */
    uint8_t addr;
    uint8_t bit_index;
    M_CHECK_SUCCESS(get_pp_mode_reg_addr_and_bit_index(sub_sample_id, &addr, &bit_index));

    /* Read register and output bits of interest */
    uint8_t value;
    M_CHECK_SUCCESS(as7058_ifce_read_register(addr, &value));
    *p_pp_mode = (value >> bit_index) & REG_PP_MODE_MASK;

    return ERR_SUCCESS;
}

err_code_t as7058_ifce_get_ecg_mux_config(as7058_ecg_mux_signals_t *p_mux_signals, uint8_t num_mux_signals)
{
    err_code_t result;
    uint8_t reg_values[3]; /* 3 configuration registers for ECG input multiplexer. */
    uint8_t i;

    M_CHECK_NULL_POINTER(p_mux_signals);
    if (AS7058_NUM_ECG_SUBS != num_mux_signals) {
        return ERR_ARGUMENT;
    }

    result = as7058_osal_read_registers(AS7058_REGADDR_ECGIMUX_CFG1, sizeof(reg_values), reg_values);
    if (ERR_SUCCESS == result) {
        for (i = 0; i < AS7058_NUM_ECG_SUBS; i++) {
            uint8_t imux_sel = (reg_values[1 + (i / 2)] >> ((i % 2) ? 4 : 0)) & 0x07;
            switch (imux_sel) {
            case 0: /* filtered IMUX1 signal */
            /* fall-through */
            case 1: /* unfiltered IMUX1 signal */
                switch (reg_values[0] & 0x0F) {
                case 0:
                    p_mux_signals[i] = AS7058_ECG_MUX_ECG_AMP;
                    break;
                case 3:
                    p_mux_signals[i] = AS7058_ECG_MUX_ECG_LEAD;
                    break;
                case 5:
                    p_mux_signals[i] = AS7058_ECG_MUX_TEMP;
                    break;
                default: /* all others */
                    p_mux_signals[i] = AS7058_ECG_MUX_UNDEFINED;
                    break;
                }
                break;

            case 2: /* ECG lead detection */
                p_mux_signals[i] = AS7058_ECG_MUX_ECG_LEAD;
                break;

            case 3: /* EDA signal */
                p_mux_signals[i] = AS7058_ECG_MUX_EDA;
                break;

            case 4: /* BioZ I signal */
                p_mux_signals[i] = AS7058_ECG_MUX_I;
                break;

            case 5: /* BioZ Q signal */
                p_mux_signals[i] = AS7058_ECG_MUX_Q;
                break;

            case 6: /* Temperature signal */
                p_mux_signals[i] = AS7058_ECG_MUX_TEMP;
                break;

            default: /* all others */
                p_mux_signals[i] = AS7058_ECG_MUX_UNDEFINED;
                break;
            }
        }
    }
    return result;
}

err_code_t as7058_ifce_set_ppg_sample_period_multiplier(uint16_t multiplier)
{
    uint8_t values[2] = {(uint8_t)multiplier, (uint8_t)(multiplier >> 8)};

    return as7058_osal_write_registers(AS7058_REGADDR_PPG_FREQL, 2, values);
}

err_code_t as7058_ifce_get_ppg_sample_period_multiplier(uint16_t *p_multiplier)
{
    M_CHECK_NULL_POINTER(p_multiplier);

    uint8_t values[2];
    M_CHECK_SUCCESS(as7058_osal_read_registers(AS7058_REGADDR_PPG_FREQL, 2, values));

    *p_multiplier = values[0] | (values[1] << 8);

    return ERR_SUCCESS;
}
