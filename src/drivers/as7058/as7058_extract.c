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

#include "error_codes.h"
#include "std_inc.h"

#include "as7058_extract.h"
#include "as7058_typedefs.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

#define AS7058_FIFO_DATA_MARKER_MASK 0x07

typedef enum { AS7058_PPG1_ID = 0, AS7058_PPG2_ID = 1, AS7058_PPG_ID_NUM = 2 } as7058_ppg_ids_t;

/******************************************************************************
 *                                  GLOBALS                                   *
 ******************************************************************************/

/******************************************************************************
 *                               LOCAL FUNCTIONS                              *
 ******************************************************************************/

static as7058_sub_sample_flags_t get_next_sub_sample_flag(uint32_t fifo_map,
                                                          as7058_sub_sample_flags_t old_sub_sample_flag)
{
    as7058_sub_sample_flags_t next_sub_sample = AS7058_SUB_SAMPLE_FLAG_NONE;
    as7058_sub_sample_flags_t highest_sub_sample;

    if (AS7058_SUB_SAMPLE_FLAG_NONE == old_sub_sample_flag ||
        (AS7058_SUB_SAMPLE_FLAG_ECG_SEQ1_SUB1 <= old_sub_sample_flag)) {
        return AS7058_SUB_SAMPLE_FLAG_NONE;
    }

    highest_sub_sample = (AS7058_SUB_SAMPLE_FLAG_PPG1_SUB8 >= old_sub_sample_flag) ? AS7058_SUB_SAMPLE_FLAG_PPG1_SUB8
                                                                                   : AS7058_SUB_SAMPLE_FLAG_PPG2_SUB8;

    while (highest_sub_sample >= old_sub_sample_flag) {
        old_sub_sample_flag <<= 1;
        if (old_sub_sample_flag & fifo_map) {
            next_sub_sample = old_sub_sample_flag;
            break;
        }
    }

    return next_sub_sample;
}

/******************************************************************************
 *                             GLOBAL FUNCTIONS                               *
 ******************************************************************************/

err_code_t as7058_extract_samples(as7058_sub_sample_ids_t extract_sub_id, const uint8_t *p_fifo_data,
                                  uint16_t fifo_data_size, uint32_t *p_chan_data, uint16_t *p_chan_data_num,
                                  as7058_extract_metadata_t *p_metadata)
{
    uint32_t i;
    as7058_sub_sample_ids_t sub_id;
    int32_t sample;
    enum as7058_fifo_data_marker data_marker;
    uint16_t maximum_num;
    as7058_sub_sample_flags_t current_sample_type;
    as7058_sub_sample_flags_t extract_sub_flag;
    as7058_sub_sample_flags_t ppg_sub_old_flags[AS7058_PPG_ID_NUM];

    as7058_sub_sample_flags_t ppg1_sub_first = AS7058_SUB_SAMPLE_FLAG_NONE;
    as7058_sub_sample_flags_t ppg2_sub_first = AS7058_SUB_SAMPLE_FLAG_NONE;

    M_CHECK_NULL_POINTER(p_metadata);
    M_CHECK_NULL_POINTER(p_fifo_data);
    M_CHECK_NULL_POINTER(p_chan_data);
    M_CHECK_NULL_POINTER(p_chan_data_num);

    if (0 == *p_chan_data_num) {
        return ERR_ARGUMENT;
    }

    /* AS7058_SUB_SAMPLE_FLAG_ECG_SEQ2_SUB1 uses the highest bit. There should be an error if fifo_map is greater than
     * this. */
    if ((0 == p_metadata->fifo_map) || ((AS7058_SUB_SAMPLE_FLAG_ECG_SEQ2_SUB1 << 1) <= p_metadata->fifo_map)) {
        return ERR_ARGUMENT;
    }
    if ((AS7058_SUB_SAMPLE_ID_NUM <= extract_sub_id) || (AS7058_SUB_SAMPLE_ID_DISABLED == extract_sub_id)) {
        return ERR_ARGUMENT;
    }

    if (0 == fifo_data_size) {
        return ERR_ARGUMENT;
    }

    if (fifo_data_size % AS7058_FIFO_SAMPLE_SIZE) {
        return ERR_ARGUMENT;
    }

    extract_sub_flag = M_AS7058_SUB_SAMPLE_ID_TO_FLAG(extract_sub_id);
    if (0 == (p_metadata->fifo_map & extract_sub_flag)) {
        return ERR_ARGUMENT;
    }

    /* Copy maximum data to internal value */
    maximum_num = *p_chan_data_num;
    *p_chan_data_num = 0;

    /* Copy meta data */
    ppg_sub_old_flags[AS7058_PPG1_ID] = p_metadata->current.ppg1_sub;
    ppg_sub_old_flags[AS7058_PPG2_ID] = p_metadata->current.ppg2_sub;

    for (i = 0; i < fifo_data_size; i += AS7058_FIFO_SAMPLE_SIZE) {
        sample = p_fifo_data[i] >> 4;
        sample |= p_fifo_data[i + 1] << 4;
        sample |= p_fifo_data[i + 2] << 12;

        data_marker = p_fifo_data[i] & AS7058_FIFO_DATA_MARKER_MASK;
        if (AS7058_FIFO_DATA_MARKER_PPG1_FIRST == data_marker) {
            /* Find out which sub-sample is the first one in the FIFO map, cache for future data marker encounters */
            if (AS7058_SUB_SAMPLE_FLAG_NONE == ppg1_sub_first) {
                for (sub_id = AS7058_SUB_SAMPLE_ID_PPG1_SUB1; sub_id <= AS7058_SUB_SAMPLE_ID_PPG1_SUB8; sub_id++) {
                    if (M_AS7058_SUB_SAMPLE_ID_TO_FLAG(sub_id) & p_metadata->fifo_map) {
                        ppg1_sub_first = M_AS7058_SUB_SAMPLE_ID_TO_FLAG(sub_id);
                        break;
                    }
                }
            }
            current_sample_type = ppg1_sub_first;
            ppg_sub_old_flags[AS7058_PPG1_ID] = ppg1_sub_first;
        } else if (AS7058_FIFO_DATA_MARKER_PPG2_FIRST == data_marker) {
            /* Find out which sub-sample is the first one in the FIFO map, cache for future data marker encounters */
            if (AS7058_SUB_SAMPLE_FLAG_NONE == ppg2_sub_first) {
                for (sub_id = AS7058_SUB_SAMPLE_ID_PPG2_SUB1; sub_id <= AS7058_SUB_SAMPLE_ID_PPG2_SUB8; sub_id++) {
                    if (M_AS7058_SUB_SAMPLE_ID_TO_FLAG(sub_id) & p_metadata->fifo_map) {
                        ppg2_sub_first = M_AS7058_SUB_SAMPLE_ID_TO_FLAG(sub_id);
                        break;
                    }
                }
            }
            current_sample_type = ppg2_sub_first;
            ppg_sub_old_flags[AS7058_PPG2_ID] = ppg2_sub_first;
        } else if (AS7058_FIFO_DATA_MARKER_STATUS == data_marker) {
            /* Status marker is not supported because it must be extracted together with following ADC data */
            continue;
        } else if (AS7058_FIFO_DATA_MARKER_ECG_SEQ1_SUB1 == data_marker) {
            current_sample_type = AS7058_SUB_SAMPLE_FLAG_ECG_SEQ1_SUB1;
        } else if (AS7058_FIFO_DATA_MARKER_ECG_SEQ1_SUB2 == data_marker) {
            current_sample_type = AS7058_SUB_SAMPLE_FLAG_ECG_SEQ1_SUB2;
        } else if (AS7058_FIFO_DATA_MARKER_ECG_SEQ2_SUB1 == data_marker) {
            current_sample_type = AS7058_SUB_SAMPLE_FLAG_ECG_SEQ2_SUB1;
        } else { /* AS7058_FIFO_DATA_MARKER_MOD1_OTHER or AS7058_FIFO_DATA_MARKER_MOD2_OTHER */
            as7058_ppg_ids_t modulator_id =
                (AS7058_FIFO_DATA_MARKER_PPG2_OTHER == data_marker) ? AS7058_PPG2_ID : AS7058_PPG1_ID;
            current_sample_type = get_next_sub_sample_flag(p_metadata->fifo_map, ppg_sub_old_flags[modulator_id]);
            if (AS7058_SUB_SAMPLE_FLAG_NONE == current_sample_type) {
                return ERR_ARGUMENT;
            }
            ppg_sub_old_flags[modulator_id] = current_sample_type;
        }

        if (current_sample_type == extract_sub_flag) {
            if (maximum_num > *p_chan_data_num) {
                p_chan_data[(*p_chan_data_num)++] = sample;
            } else {
                return ERR_SIZE;
            }
        }
    }

    p_metadata->recent.ppg1_sub = ppg_sub_old_flags[AS7058_PPG1_ID];
    p_metadata->recent.ppg2_sub = ppg_sub_old_flags[AS7058_PPG2_ID];

    if (p_metadata->copy_recent_to_current) {
        memcpy(&(p_metadata->current), &(p_metadata->recent), sizeof(p_metadata->current));
    }

    return ERR_SUCCESS;
}
