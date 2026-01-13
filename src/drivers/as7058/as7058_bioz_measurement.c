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

#include "as7058_bioz_measurement.h"
#include "as7058_extract.h"
#include "as7058_interface.h"
#include "as7058_osal_chiplib.h"
#include "as7058_typedefs.h"
#include "error_codes.h"
#include "std_inc.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

#define REG_BITS_BIOZ_SELECT__BIOZ_MEAS_SEL__BIOIMPEDANCE 0x00 /*!< Normal impedance measurement. */
#define REG_BITS_BIOZ_SELECT__BIOZ_MEAS_SEL__SHORT 0x10        /*!< Short measurement. */
#define REG_BITS_BIOZ_SELECT__BIOZ_MEAS_SEL__2K 0x20           /*!< 2k resistor measurement. */
#define REG_BITS_BIOZ_SELECT__BIOZ_INMUX_SEL__VP1VN2IP3IN4 0   /*!< Body impedance. */
#define REG_BITS_BIOZ_SELECT__BIOZ_INMUX_SEL__VP1VN3IP1IN3 7   /*!< Wrist contact impedance. */
#define REG_BITS_BIOZ_SELECT__BIOZ_INMUX_SEL__VP2VN4IP2IN4 10  /*!< Finger contact impedance. */
#define REG_BITS_BIOZ_SELECT__BIOZ_INMUX_SEL__VP3VN4IP3IN4 11  /*!< Total impedance. */

/*! States of BioZ measurement module. */
enum channel_ids {
    CHANNEL_ID_I = 0, /*!< ECG channel for in-phase measurements. */
    CHANNEL_ID_Q,     /*!< ECG channel for quadrature measurements. */
    CHANNEL_ID_TEMP,  /*!< ECG channel for temperature measurements. */

    CHANNEL_ID_NUM, /*!< Number of ECG channels. */
};

/*! States of BioZ measurement module. */
enum impedance_scaling_states {
    IMPEDANCE_SCALING_STATE_UNINITIALIZED = 0, /*!< Module is in uninitialized state. */
    IMPEDANCE_SCALING_STATE_CONFIGURATION,     /*!< Module is in configuration state. */
    IMPEDANCE_SCALING_STATE_PROCESS,           /*!< Module is in processing state. */
};

#define MAX_ADC_VALUE 0xFFFFF /*!< Maximum ADC value with 20 bits resolution. */

// TODO This value must be updated as soon we get the results from the manufacturing
#ifndef ADC_TEMP_SLOPE
#define ADC_TEMP_SLOPE                                                                                                 \
    1000000 /*!< Gain definition for temperature calculation scaled by 1000000. Divide by 1000000 to get the unscaled  \
                 value. Not used yet. */
#endif

struct scaling_bioz_params {
    as7058_bioz_meas_config_t config; /*!< Measurement configuration of the module. */
    as7058_bioz_meas_result_t result; /*!< Internal saved measurement result of the module. */
    struct {
        uint32_t sum_adc_value;                         /*!< Sum of the ADC values. Value is reset for each
                                                             sub-measurement. */
        uint16_t sum_adc_value_num;                     /*!< Number of ADC values that have been summed. */
        uint16_t drop_counter;                          /*!< Number of ADC values that have been dropped ADC. */
        as7058_sub_sample_ids_t sub_id;                 /*!< Sub-sample ID of the channel. */
    } channels[CHANNEL_ID_NUM];                         /*!< Helper data for each channel. */
    enum impedance_scaling_states state;                /*!< Current state of the BioZ module. */
    as7058_extract_metadata_t extract_meta;             /*!< Metadata for extracting channel data. */
    uint8_t bioz_select_reg_val;                        /*!< Original register value of BIOZ_SELECT. */
    enum as7058_bioz_measurement_types sub_measurement; /*!< Type of the current sub-measurement. */
};

/******************************************************************************
 *                                  GLOBALS                                   *
 ******************************************************************************/

static struct scaling_bioz_params g_params; /*!< Data for running BioZ measurement module. */

/******************************************************************************
 *                               LOCAL FUNCTIONS                              *
 ******************************************************************************/

err_code_t prepare_for_sub_measurement(enum as7058_bioz_measurement_types bioz_type)
{
    const uint8_t bioz_select_reg_vals[AS7058_BIOZ_MEASUREMENT_TYPE_NUM] = {
        REG_BITS_BIOZ_SELECT__BIOZ_MEAS_SEL__SHORT,         REG_BITS_BIOZ_SELECT__BIOZ_MEAS_SEL__2K,
        REG_BITS_BIOZ_SELECT__BIOZ_INMUX_SEL__VP1VN2IP3IN4, REG_BITS_BIOZ_SELECT__BIOZ_INMUX_SEL__VP1VN3IP1IN3,
        REG_BITS_BIOZ_SELECT__BIOZ_INMUX_SEL__VP2VN4IP2IN4, REG_BITS_BIOZ_SELECT__BIOZ_INMUX_SEL__VP3VN4IP3IN4};

    if (AS7058_BIOZ_MEASUREMENT_TYPE_TOTAL < bioz_type) {
        /* Measurements run continuously, start again with short sub-measurement after performing total impedance
         * sub-measurement */
        bioz_type = AS7058_BIOZ_MEASUREMENT_TYPE_SHORT;
    }

    if (AS7058_BIOZ_MEASUREMENT_TYPE_SHORT == bioz_type) {
        /* Reset temperature when a new sequence of sub-measurements is started */
        g_params.channels[CHANNEL_ID_TEMP].sum_adc_value = 0;
        g_params.channels[CHANNEL_ID_TEMP].sum_adc_value_num = 0;
    }

    /* Prepare extract metadata */
    uint32_t fifo_map = g_params.extract_meta.fifo_map;
    memset(&g_params.extract_meta, 0, sizeof(g_params.extract_meta));
    g_params.extract_meta.fifo_map = fifo_map;

    /* Reset measurement results for I and Q, temperature is reset outside this function before performing short
     * sub-measurement */
    uint8_t i;
    for (i = CHANNEL_ID_I; i <= CHANNEL_ID_Q; i++) {
        g_params.channels[i].sum_adc_value = 0;
        g_params.channels[i].sum_adc_value_num = 0;
        g_params.channels[i].drop_counter = 0;
    }

    g_params.sub_measurement = bioz_type;

    return as7058_ifce_write_register(AS7058_REGADDR_BIOZ_SELECT, bioz_select_reg_vals[bioz_type]);
}

err_code_t sum_samples(enum channel_ids channel_id, const uint8_t *p_fifo_data, uint16_t fifo_data_size,
                       uint8_t overwrite_old_meta_data)
{
    err_code_t result;
    uint16_t i;
    static uint32_t adc_channel_data[AS7058_FIFO_DATA_BUFFER_SIZE / AS7058_FIFO_SAMPLE_SIZE];
    uint16_t adc_channel_data_num = AS7058_FIFO_DATA_BUFFER_SIZE / AS7058_FIFO_SAMPLE_SIZE;
    uint16_t max_average_number;

    if (CHANNEL_ID_TEMP > channel_id) {
        max_average_number = g_params.config.num_averages;
    } else if (CHANNEL_ID_TEMP == channel_id) {
        /* Allow more values for temperature samples. */
        max_average_number = UINT32_MAX / MAX_ADC_VALUE;
    } else {
        return ERR_ARGUMENT;
    }

    g_params.extract_meta.copy_recent_to_current = overwrite_old_meta_data;
    result = as7058_extract_samples(g_params.channels[channel_id].sub_id, p_fifo_data, fifo_data_size, adc_channel_data,
                                    &adc_channel_data_num, &g_params.extract_meta);
    if (ERR_SUCCESS == result) {
        uint16_t samples_to_drop =
            M_MIN(g_params.config.num_dropped_first_samples - g_params.channels[channel_id].drop_counter,
                  adc_channel_data_num);
        g_params.channels[channel_id].drop_counter += samples_to_drop;
        for (i = samples_to_drop; i < adc_channel_data_num; i++) {
            g_params.channels[channel_id].sum_adc_value += adc_channel_data[i];
            g_params.channels[channel_id].sum_adc_value_num++;
            if (max_average_number <= g_params.channels[channel_id].sum_adc_value_num) {
                break;
            }
        }
    }
    return result;
}

/******************************************************************************
 *                             GLOBAL FUNCTIONS                               *
 ******************************************************************************/

err_code_t as7058_bioz_initialize(void)
{
    err_code_t result;

    result = as7058_bioz_shutdown();

    if (ERR_SUCCESS == result) {
        g_params.state = IMPEDANCE_SCALING_STATE_CONFIGURATION;
    }

    return result;
}

err_code_t as7058_bioz_configure(const as7058_bioz_meas_config_t *p_special_config)
{
    M_CHECK_NULL_POINTER(p_special_config);

    if ((0 == p_special_config->num_averages) ||
        ((UINT32_MAX / MAX_ADC_VALUE) < (uint32_t)p_special_config->num_averages)) {
        return ERR_ARGUMENT;
    }
    memcpy(&g_params.config, p_special_config, sizeof(as7058_bioz_meas_config_t));
    return ERR_SUCCESS;
}

err_code_t as7058_bioz_start(as7058_meas_config_t meas_config)
{
    err_code_t result;
    int16_t resistor_error_milli_percent = 0;
    as7058_ecg_mux_signals_t ecg_mux_subs[AS7058_NUM_ECG_SUBS];

    if (0 == g_params.config.num_averages) {
        return ERR_CONFIG;
    }

    result = as7058_ifce_get_ecg_mux_config(ecg_mux_subs, AS7058_NUM_ECG_SUBS);
    if (ERR_SUCCESS != result) {
        return result;
    }

    /* Check that both sub-samples of ECG sequencer one are enabled */
    if (!(meas_config.fifo_map & M_AS7058_SUB_SAMPLE_ID_TO_FLAG(AS7058_SUB_SAMPLE_ID_ECG_SEQ1_SUB1)) ||
        !(meas_config.fifo_map & M_AS7058_SUB_SAMPLE_ID_TO_FLAG(AS7058_SUB_SAMPLE_ID_ECG_SEQ1_SUB2))) {
        return ERR_CONFIG;
    }

    /* Check that I and Q channels are defined once inside ECG-multiplexer */
    if (AS7058_ECG_MUX_I == ecg_mux_subs[0] && AS7058_ECG_MUX_Q == ecg_mux_subs[1]) {
        g_params.channels[CHANNEL_ID_I].sub_id = AS7058_SUB_SAMPLE_ID_ECG_SEQ1_SUB1;
        g_params.channels[CHANNEL_ID_Q].sub_id = AS7058_SUB_SAMPLE_ID_ECG_SEQ1_SUB2;
    } else if (AS7058_ECG_MUX_Q == ecg_mux_subs[0] && AS7058_ECG_MUX_I == ecg_mux_subs[1]) {
        g_params.channels[CHANNEL_ID_I].sub_id = AS7058_SUB_SAMPLE_ID_ECG_SEQ1_SUB2;
        g_params.channels[CHANNEL_ID_Q].sub_id = AS7058_SUB_SAMPLE_ID_ECG_SEQ1_SUB1;
    } else {
        return ERR_CONFIG;
    }

    /* Temperature is optional. */
    if (AS7058_ECG_MUX_TEMP == ecg_mux_subs[2] &&
        meas_config.fifo_map & M_AS7058_SUB_SAMPLE_ID_TO_FLAG(AS7058_SUB_SAMPLE_ID_ECG_SEQ2_SUB1)) {
        g_params.channels[CHANNEL_ID_TEMP].sub_id = AS7058_SUB_SAMPLE_ID_ECG_SEQ2_SUB1;
    } else {
        g_params.channels[CHANNEL_ID_TEMP].sub_id = AS7058_SUB_SAMPLE_ID_DISABLED;
    }

    result = as7058_ifce_get_2k_error(&resistor_error_milli_percent);
    if (ERR_SUCCESS == result) {
        const int32_t resistor = 2000;
        g_params.result.ref_resistor =
            (uint32_t)(resistor + (int32_t)((int64_t)resistor * (int64_t)resistor_error_milli_percent / 1000 / 100));

        result = as7058_ifce_get_temp_adc_production(&g_params.result.ref_temperature_adc);

        g_params.result.temperature_adc = 0;
        g_params.result.slope = ADC_TEMP_SLOPE;

        /* Disable dropping of temperature measurements */
        g_params.channels[CHANNEL_ID_TEMP].drop_counter = g_params.config.num_dropped_first_samples;
    }

    /* Save the old register content */
    if (ERR_SUCCESS == result) {
        result = as7058_ifce_read_register(AS7058_REGADDR_BIOZ_SELECT, &g_params.bioz_select_reg_val);
    }
    if (ERR_SUCCESS == result) {
        g_params.extract_meta.fifo_map = meas_config.fifo_map;
        result = prepare_for_sub_measurement(AS7058_BIOZ_MEASUREMENT_TYPE_SHORT);
    }
    if (ERR_SUCCESS == result) {
        g_params.state = IMPEDANCE_SCALING_STATE_PROCESS;
    }

    return result;
}

err_code_t as7058_bioz_stop(void)
{
    err_code_t result;

    if (IMPEDANCE_SCALING_STATE_PROCESS == g_params.state) {
        result = as7058_ifce_write_register(AS7058_REGADDR_BIOZ_SELECT, g_params.bioz_select_reg_val);
        if (ERR_SUCCESS == result) {
            g_params.state = IMPEDANCE_SCALING_STATE_CONFIGURATION;
        }
    } else {
        result = ERR_SUCCESS;
    }

    return result;
}

err_code_t as7058_bioz_process(const uint8_t *p_fifo_data, uint16_t fifo_data_size,
                               const as7058_bioz_meas_result_t **pp_result)
{
    err_code_t result;

    uint8_t results_valid = FALSE;

    M_CHECK_NULL_POINTER(p_fifo_data);
    M_CHECK_NULL_POINTER(pp_result);

    if (IMPEDANCE_SCALING_STATE_PROCESS != g_params.state) {
        return ERR_PERMISSION;
    }

    /* Extract optional temperature */
    if (AS7058_SUB_SAMPLE_ID_DISABLED != g_params.channels[CHANNEL_ID_TEMP].sub_id) {
        result = sum_samples(CHANNEL_ID_TEMP, p_fifo_data, fifo_data_size, FALSE);
    } else {
        result = ERR_SUCCESS;
    }

    /* Extract I and Q */
    if (ERR_SUCCESS == result) {
        result = sum_samples(CHANNEL_ID_I, p_fifo_data, fifo_data_size, FALSE);
    }
    if (ERR_SUCCESS == result) {
        result = sum_samples(CHANNEL_ID_Q, p_fifo_data, fifo_data_size, TRUE);
    }

    if (ERR_SUCCESS == result && (g_params.config.num_averages <= g_params.channels[CHANNEL_ID_I].sum_adc_value_num) &&
        (g_params.config.num_averages <= g_params.channels[CHANNEL_ID_Q].sum_adc_value_num)) {
        result = as7058_ifce_stop_measurement();

        if (ERR_SUCCESS == result) {

            /* Save the measured averaged values */
            g_params.result.measurements[g_params.sub_measurement].in_phase =
                g_params.channels[CHANNEL_ID_I].sum_adc_value / g_params.channels[CHANNEL_ID_I].sum_adc_value_num;
            g_params.result.measurements[g_params.sub_measurement].quadrature =
                g_params.channels[CHANNEL_ID_Q].sum_adc_value / g_params.channels[CHANNEL_ID_Q].sum_adc_value_num;

            if (AS7058_BIOZ_MEASUREMENT_TYPE_TOTAL == g_params.sub_measurement) {
                if (0 < g_params.channels[CHANNEL_ID_TEMP].sum_adc_value_num) {
                    g_params.result.temperature_adc = g_params.channels[CHANNEL_ID_TEMP].sum_adc_value /
                                                      g_params.channels[CHANNEL_ID_TEMP].sum_adc_value_num;
                } else {
                    /* Mark temperature value as invalid */
                    g_params.result.temperature_adc = UINT32_MAX;
                }
                results_valid = TRUE;
            }

            result = prepare_for_sub_measurement(g_params.sub_measurement + 1);
        }

        if (ERR_SUCCESS == result) {
            result = as7058_ifce_start_measurement();
        }
    }

    if (ERR_SUCCESS == result) {
        if (FALSE == results_valid) {
            result = ERR_NO_DATA;
        } else {
            *pp_result = &g_params.result;
        }
    }
    return result;
}

err_code_t as7058_bioz_shutdown(void)
{
    memset(&g_params, 0, sizeof(g_params));
    return ERR_SUCCESS;
}
