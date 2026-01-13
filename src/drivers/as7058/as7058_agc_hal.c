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

#include "agc_hal.h"
#include "as7058_extract.h"
#include "as7058_interface.h"
#include "as7058_typedefs.h"
#include "error_codes.h"
#include "std_inc.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

/*! Checks whether the library was already initialized */
#define M_CHECK_INITIALIZED_STATE()                                                                                    \
    do {                                                                                                               \
        if (0 == g_meas_config.fifo_map) {                                                                             \
            return ERR_PERMISSION;                                                                                     \
        }                                                                                                              \
    } while (0)

/*! Checks whether the sub ID is in a valid range */
#define M_SUB_SAMPLE_RANGE(sub_id)                                                                                     \
    do {                                                                                                               \
        if ((AS7058_SUB_SAMPLE_ID_PPG1_SUB1 > sub_id) || (AS7058_SUB_SAMPLE_ID_PPG2_SUB8 < sub_id)) {                  \
            return ERR_ARGUMENT;                                                                                       \
        }                                                                                                              \
    } while (0)

/******************************************************************************
 *                                  GLOBALS                                   *
 ******************************************************************************/

static as7058_meas_config_t g_meas_config;
static uint8_t g_led_groups[8];                    /* 8 sub-samples because PPG1 SUBx and PPG2 SUBx use the same LEDs */
static uint8_t g_led_currents[AS7058_LED_NUM_MAX]; /* Save the LED currents internally to avoid lot of I2C transfers. */
static as7058_extract_metadata_t g_metadata;

/******************************************************************************
 *                               LOCAL FUNCTIONS                              *
 ******************************************************************************/

/******************************************************************************
 *                             GLOBAL FUNCTIONS                               *
 ******************************************************************************/

err_code_t agc_hal_initialize(void *p_config, uint16_t size)
{
    uint8_t i;
    err_code_t result = ERR_SUCCESS;
    uint8_t led_group_id;

    M_CHECK_NULL_POINTER(p_config);
    M_CHECK_SIZE(sizeof(as7058_meas_config_t), size);

    memset(&g_led_groups, 0, sizeof(g_led_groups));
    memcpy(&g_meas_config, p_config, sizeof(as7058_meas_config_t));
    memset(&g_metadata, 0, sizeof(g_metadata));
    g_metadata.fifo_map = g_meas_config.fifo_map;

    /* Get LED groups for PPG (Modulator 1 and 2 use the same LED groups) */
    for (i = 0; (i < AGC_MAX_CHANNEL_CNT) && (ERR_SUCCESS == result); i++) {
        if (AS7058_SUB_SAMPLE_ID_DISABLED == g_meas_config.agc_channels[i]) {
            continue;
        } else if (AS7058_SUB_SAMPLE_ID_PPG1_SUB8 >= g_meas_config.agc_channels[i]) {
            led_group_id = g_meas_config.agc_channels[i] - AS7058_SUB_SAMPLE_ID_PPG1_SUB1;
        } else if (AS7058_SUB_SAMPLE_ID_PPG2_SUB8 >= g_meas_config.agc_channels[i]) {
            led_group_id = g_meas_config.agc_channels[i] - AS7058_SUB_SAMPLE_ID_PPG2_SUB1;
        } else {
            result = ERR_ARGUMENT;
        }

        if (ERR_SUCCESS == result) {
            result = as7058_ifce_get_sub_sample_led_config(g_meas_config.agc_channels[i], &g_led_groups[led_group_id]);
        }
    }

    for (i = 0; ERR_SUCCESS == result && i < AS7058_LED_NUM_MAX; i++) {
        result = as7058_ifce_get_led_current((as7058_led_ids_t)i, &g_led_currents[i]);
    }

    if (ERR_SUCCESS != result) {
        agc_hal_shutdown();
    }

    return result;
}

err_code_t agc_hal_set_led_current(agc_channel_id_t channel_id, uint8_t led_current)
{
    err_code_t result = ERR_SUCCESS;
    uint8_t led_current_group;
    uint8_t i = 0;

    M_CHECK_INITIALIZED_STATE();
    M_SUB_SAMPLE_RANGE(channel_id);

    if (AS7058_SUB_SAMPLE_ID_PPG1_SUB8 >= channel_id) {
        led_current_group = g_led_groups[channel_id - AS7058_SUB_SAMPLE_ID_PPG1_SUB1];
    } else {
        led_current_group = g_led_groups[channel_id - AS7058_SUB_SAMPLE_ID_PPG2_SUB1];
    }

    while (led_current_group && (ERR_SUCCESS == result)) {

        if (led_current_group & 0x01) {
            result = as7058_ifce_set_led_current((as7058_led_ids_t)i, led_current);
            if (ERR_SUCCESS == result) {
                g_led_currents[i] = led_current;
            }
        }
        led_current_group >>= 1;
        i++;
    }

    return result;
}

err_code_t agc_hal_get_led_current(agc_channel_id_t channel_id, uint8_t *p_led_current)
{
    uint8_t led_current_group;
    uint8_t i = 0;

    M_CHECK_INITIALIZED_STATE();
    M_SUB_SAMPLE_RANGE(channel_id);

    if (AS7058_SUB_SAMPLE_ID_PPG1_SUB8 >= channel_id) {
        led_current_group = g_led_groups[channel_id - AS7058_SUB_SAMPLE_ID_PPG1_SUB1];
    } else {
        led_current_group = g_led_groups[channel_id - AS7058_SUB_SAMPLE_ID_PPG2_SUB1];
    }

    if (0 == led_current_group) {
        return ERR_LED_ACCESS;
    }
    while (led_current_group) {

        if (led_current_group & 0x01) {
            *p_led_current = g_led_currents[i];
            /* We only read the first LED which is connected to this channel.
               It could be that other LEDs which are linked to this channel have other currents.
               This is currently ignored because the API does not support this case. */
            break;
        }
        led_current_group >>= 1;
        i++;
    }

    return ERR_SUCCESS;
}

err_code_t agc_hal_set_pd_offset(agc_channel_id_t channel_id, uint8_t pd_offset)
{
    M_CHECK_INITIALIZED_STATE();

    return as7058_ifce_set_pd_offset(channel_id, pd_offset);
}

err_code_t agc_hal_get_pd_offset(agc_channel_id_t channel_id, uint8_t *p_pd_offset)
{
    M_CHECK_INITIALIZED_STATE();

    return as7058_ifce_get_pd_offset(channel_id, p_pd_offset);
}

err_code_t agc_hal_extract_samples(agc_channel_id_t channel_id, const uint8_t *p_fifo_data, uint16_t fifo_data_size,
                                   uint8_t fifo_data_changed, int32_t *p_chan_data, uint16_t *p_chan_data_num)
{
    M_CHECK_INITIALIZED_STATE();
    M_SUB_SAMPLE_RANGE(channel_id);

    if (fifo_data_changed) {
        memcpy(&(g_metadata.current), &(g_metadata.recent), sizeof(g_metadata.current));
    }

    return as7058_extract_samples(channel_id, p_fifo_data, fifo_data_size, (uint32_t *)p_chan_data, p_chan_data_num,
                                  &g_metadata);
}

err_code_t agc_hal_get_sampling_period_us(agc_channel_id_t channel_id, uint32_t *p_sampling_period)
{
    M_CHECK_INITIALIZED_STATE();
    M_SUB_SAMPLE_RANGE(channel_id);
    M_CHECK_NULL_POINTER(p_sampling_period);

    if (AS7058_SUB_SAMPLE_ID_PPG2_SUB8 >= channel_id) {
        *p_sampling_period = g_meas_config.ppg_sample_period_us;
    } else if (AS7058_SUB_SAMPLE_ID_ECG_SEQ1_SUB2 >= channel_id) {
        *p_sampling_period = g_meas_config.ecg_seq1_sample_period_us;
    } else {
        *p_sampling_period = g_meas_config.ecg_seq2_sample_period_us;
    }

    return ERR_SUCCESS;
}

err_code_t agc_hal_shutdown()
{
    memset(&g_meas_config, 0, sizeof(g_meas_config));
    return ERR_SUCCESS;
}
