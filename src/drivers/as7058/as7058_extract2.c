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

#include "as7058_extract2.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

#ifndef AS7058_EXTRACT2_FUNC_DEFN
/*! Preprocessor macro that is placed in front of every definition of a public function with external linkage. By
 *  default this macro is defined to expand to nothing, but it can be defined externally. Example use cases include
 *  setting keywords. */
#define AS7058_EXTRACT2_FUNC_DEFN
#endif

#define AS7058_EXTRACT2_FIFO_ITEM_MARKER_MASK (uint32_t)0x00000007
#define AS7058_EXTRACT2_FIFO_ITEM_DATA_SHIFT 4
#define AS7058_EXTRACT2_SEPARATE_SAR_STATUS_SYNCHRONIZATION_MASK (uint32_t)0x0000000E
#define AS7058_EXTRACT2_SEPARATE_SAR_STATUS_MODULATOR_MASK (uint32_t)0x000F0000
#define AS7058_EXTRACT2_SEPARATE_SAR_STATUS_MODULATOR_SHIFT 16
#define AS7058_EXTRACT2_SEPARATE_SAR_STATUS_SUB_SAMPLE_MASK (uint32_t)0x0000F000
#define AS7058_EXTRACT2_SEPARATE_SAR_STATUS_SUB_SAMPLE_SHIFT 12
#define AS7058_EXTRACT2_SEPARATE_SAR_STATUS_PD_OFFSET_MASK (uint32_t)0x00000FF0
#define AS7058_EXTRACT2_SEPARATE_SAR_STATUS_PD_OFFSET_SHIFT 4
#define AS7058_EXTRACT2_INLINE_SAR_STATUS_ADC_VALUE_MASK (uint32_t)0x000FFFE0
#define AS7058_EXTRACT2_INLINE_SAR_STATUS_PD_OFFSET_UPPER_MASK (uint32_t)0x0000001E
#define AS7058_EXTRACT2_INLINE_SAR_STATUS_PD_OFFSET_UPPER_SHIFT 1

/******************************************************************************
 *                               LOCAL FUNCTIONS                              *
 ******************************************************************************/

/*!
 * \brief Gets the first enabled sub-sample following the given sub-sample for the given PPG modulator.
 *
 * \param[in] modulator          Modulator. Must be a PPG modulator value, i.e. ::AS7058_MODULATOR_PPG1 or
 *                               ::AS7058_MODULATOR_PPG2.
 * \param[in] sub_sample         Input sub-sample.
 * \param[in] fifo_map           FIFO map.
 * \param[in] consider_current   Controls which sub-sample is the first that is considered. If ::FALSE, the input
 *                               sub-sample is not considered and the first enabled sub-sample after the input
 *                               sub-sample is output. If not ::FALSE, the input sub-sample is considered and may be
 *                               output.
 * \param[out] p_next_sub_sample Output sub-sample.
 *
 * \retval ::ERR_SUCCESS  Output produced.
 * \retval ::ERR_DATA     No enabled sub-sample exists that follows the given sub-sample.
 * \retval ::ERR_ARGUMENT Modulator is not a PPG modulator value.
 */
static err_code_t get_next_ppg_sub_sample(as7058_modulator_t modulator, as7058_modulator_sub_sample_t sub_sample,
                                          uint32_t fifo_map, uint8_t consider_current,
                                          as7058_modulator_sub_sample_t *p_next_sub_sample)
{
    uint32_t base_mask;
    if (AS7058_MODULATOR_PPG1 == modulator) {
        base_mask = AS7058_SUB_SAMPLE_FLAG_PPG1_SUB1;
    } else if (AS7058_MODULATOR_PPG2 == modulator) {
        base_mask = AS7058_SUB_SAMPLE_FLAG_PPG2_SUB1;
    } else {
        /* Invalid modulator */
        return ERR_ARGUMENT;
    }

    if (AS7058_MODULATOR_SUB_SAMPLE_INVALID == sub_sample) {
        /* Invalid input sub-sample */
        return ERR_DATA;
    }

    for (uint8_t i = sub_sample + (consider_current ? 0 : 1); i <= AS7058_MODULATOR_SUB_SAMPLE_8; i++) {
        if ((base_mask << i) & fifo_map) {
            *p_next_sub_sample = i;
            return ERR_SUCCESS;
        }
    }

    /* The current sub-sample is the last enabled sub-sample of this PPG modulator */
    return ERR_DATA;
}

/*!
 * \brief Gets the modulator and sub-sample corresponding to a FIFO marker.
 *
 * Throughout a measurement, this function is intended to be called for each FIFO item in the order the have been
 * produced. Invalid outputs are produced if the function is not called for every FIFO item in the correct order. Before
 * calling this message for first time during a measurement, the value of the last_ppg_sub_samples array must be set to
 * ::AS7058_MODULATOR_SUB_SAMPLE_INVALID. For subsequent calls of the function during a measurement, the values of the
 * array must remain set to the values previously set by this function. During a measurement, always pass the same
 * fifo_map argument value.
 *
 * \param[in] marker                    Marker of the FIFO item.
 * \param[in] fifo_map                  FIFO map.
 * \param[out] p_modulator              Modulator the FIFO item with the given marker corresponds to.
 * \param[out] p_sub_sample             Sub-sample the FIFO item with the given marker corresponds to.
 * \param[inout] p_last_ppg_sub_samples Stores the last returned sub-samples for the PPG modulators.
 *
 * \retval ::ERR_SUCCESS Output produced.
 * \retval ::ERR_DATA    Inconsistency detected.
 * \retval ::ERR_NO_DATA Marker marks a SAR status item.
 */
static err_code_t
get_sub_sample_for_marker(as7058_fifo_data_marker_t marker, uint32_t fifo_map, as7058_modulator_t *p_modulator,
                          as7058_modulator_sub_sample_t *p_sub_sample,
                          as7058_modulator_sub_sample_t (*p_last_ppg_sub_samples)[AS7058_MODULATOR_NUM_PPG])
{
    if ((AS7058_FIFO_DATA_MARKER_PPG1_FIRST == marker) || (AS7058_FIFO_DATA_MARKER_PPG2_FIRST == marker)) {
        *p_modulator = (AS7058_FIFO_DATA_MARKER_PPG1_FIRST == marker ? AS7058_MODULATOR_PPG1 : AS7058_MODULATOR_PPG2);
        M_CHECK_SUCCESS(
            get_next_ppg_sub_sample(*p_modulator, AS7058_MODULATOR_SUB_SAMPLE_1, fifo_map, TRUE, p_sub_sample));
        (*p_last_ppg_sub_samples)[*p_modulator] = *p_sub_sample;
    } else if ((AS7058_FIFO_DATA_MARKER_PPG1_OTHER == marker) || (AS7058_FIFO_DATA_MARKER_PPG2_OTHER == marker)) {
        *p_modulator = (AS7058_FIFO_DATA_MARKER_PPG1_OTHER == marker ? AS7058_MODULATOR_PPG1 : AS7058_MODULATOR_PPG2);
        M_CHECK_SUCCESS(get_next_ppg_sub_sample(*p_modulator, (*p_last_ppg_sub_samples)[*p_modulator], fifo_map, FALSE,
                                                p_sub_sample));
        (*p_last_ppg_sub_samples)[*p_modulator] = *p_sub_sample;
    } else if ((AS7058_FIFO_DATA_MARKER_ECG_SEQ1_SUB1 == marker) || (AS7058_FIFO_DATA_MARKER_ECG_SEQ1_SUB2 == marker)) {
        *p_modulator = AS7058_MODULATOR_ECG_SEQ1;
        *p_sub_sample = (AS7058_FIFO_DATA_MARKER_ECG_SEQ1_SUB1 == marker ? AS7058_MODULATOR_SUB_SAMPLE_1
                                                                         : AS7058_MODULATOR_SUB_SAMPLE_2);
    } else if (AS7058_FIFO_DATA_MARKER_ECG_SEQ2_SUB1 == marker) {
        *p_modulator = AS7058_MODULATOR_ECG_SEQ2;
        *p_sub_sample = AS7058_MODULATOR_SUB_SAMPLE_1;
    } else { /* AS7058_FIFO_DATA_MARKER_STATUS == marker */
        return ERR_NO_DATA;
    }

    return ERR_SUCCESS;
}

/*!
 * \brief Parses FIFO data of a separate SAR status item.
 *
 * \param[in] data          Data of the FIFO item.
 * \param[out] p_modulator  Modulator the SAR status corresponds to.
 * \param[out] p_sub_sample Sub-sample the SAR status corresponds to.
 * \param[out] p_pd_offset  Current photodiode offset current value of the corresponding sub-sample.
 *
 * \retval ::ERR_SUCCESS Output produced.
 * \retval ::ERR_DATA    Inconsistency detected.
 * \retval ::ERR_NO_DATA Item is a synchronization status item.
 */
static err_code_t parse_separate_sar_status(uint32_t data, as7058_modulator_t *p_modulator,
                                            as7058_modulator_sub_sample_t *p_sub_sample, uint8_t *p_pd_offset)
{
    if (data & AS7058_EXTRACT2_SEPARATE_SAR_STATUS_SYNCHRONIZATION_MASK) {
        /* Synchronization status items are not related to SAR, so they are discarded */
        return ERR_NO_DATA;
    }

    uint32_t ppg_modulator = (data & AS7058_EXTRACT2_SEPARATE_SAR_STATUS_MODULATOR_MASK) >>
                             AS7058_EXTRACT2_SEPARATE_SAR_STATUS_MODULATOR_SHIFT;
    uint32_t sub_sample = (data & AS7058_EXTRACT2_SEPARATE_SAR_STATUS_SUB_SAMPLE_MASK) >>
                          AS7058_EXTRACT2_SEPARATE_SAR_STATUS_SUB_SAMPLE_SHIFT;

    if ((ppg_modulator > AS7058_MODULATOR_PPG2) || (sub_sample > AS7058_MODULATOR_SUB_SAMPLE_8)) {
        /* Invalid modulator or sub-sample in SAR status encountered */
        return ERR_DATA;
    }

    *p_modulator = ppg_modulator;
    *p_sub_sample = sub_sample;

    /* The full PD offset is provided at bit indices 11:5 */
    *p_pd_offset = ((data & AS7058_EXTRACT2_SEPARATE_SAR_STATUS_PD_OFFSET_MASK) >>
                    AS7058_EXTRACT2_SEPARATE_SAR_STATUS_PD_OFFSET_SHIFT);

    return ERR_SUCCESS;
}

/*!
 * \brief Parses FIFO data with inline SAR status.
 *
 * \param[in] data         Data of the FIFO item.
 * \param[out] p_adc_value ADC value of the sample. The lower five bits are always unset.
 * \param[out] p_pd_offset Current photodiode offset current value of the corresponding sub-sample. The lower four bits
 *                         are always unset.
 */
static void parse_inline_sar_status(uint32_t data, uint32_t *p_adc_value, uint8_t *p_pd_offset)
{
    /* Upper 15 bits of the ADC value are provided at bit indices 19:5, the lower five bits are not provided */
    *p_adc_value = data & AS7058_EXTRACT2_INLINE_SAR_STATUS_ADC_VALUE_MASK;

    /* Upper four bits of the PD offset are provided at bit indices 4:1, the lower four bits are not provided */
    *p_pd_offset = ((data & AS7058_EXTRACT2_INLINE_SAR_STATUS_PD_OFFSET_UPPER_MASK) >>
                    AS7058_EXTRACT2_INLINE_SAR_STATUS_PD_OFFSET_UPPER_SHIFT)
                   << 4;
}

/*!
 * \brief Parses a FIFO item.
 *
 * \param[in] input     Begin of the FIFO item. The byte pointed to and two subsequent bytes (i.e. three bytes total)
 *                      are read.
 * \param[out] p_marker Marker of the FIFO item.
 * \param[out] p_data   Data of the FIFO item. If the data is not of interest, this parameter can be NULL.
 */
static void parse_fifo_item(const uint8_t *p_input, as7058_fifo_data_marker_t *p_marker, uint32_t *p_data)
{
    uint32_t item = (p_input[2] << 16) | (p_input[1] << 8) | p_input[0];

    *p_marker = item & AS7058_EXTRACT2_FIFO_ITEM_MARKER_MASK;

    if (p_data) {
        *p_data = item >> AS7058_EXTRACT2_FIFO_ITEM_DATA_SHIFT;
    }
}

/*!
 * \brief Converts a modulator and a sub-sample to a ::as7058_sub_sample_ids value.
 *
 * \warning The combination of modulator and sub_sample must be valid. No validation of parameters is implemented.
 *
 * \param[in] modulator  Modulator.
 * \param[in] sub_sample Sub-sample.
 *
 * \returns ::as7058_sub_sample_ids value.
 */
static as7058_sub_sample_ids_t convert_to_chiplib_sub_sample_id(as7058_modulator_t modulator,
                                                                as7058_modulator_sub_sample_t sub_sample)
{
    if (AS7058_MODULATOR_PPG1 == modulator) {
        return AS7058_SUB_SAMPLE_ID_PPG1_SUB1 + sub_sample;
    } else if (AS7058_MODULATOR_PPG2 == modulator) {
        return AS7058_SUB_SAMPLE_ID_PPG2_SUB1 + sub_sample;
    } else if (AS7058_MODULATOR_ECG_SEQ1 == modulator) {
        return AS7058_SUB_SAMPLE_ID_ECG_SEQ1_SUB1 + sub_sample;
    } else { /* AS7058_MODULATOR_ECG_SEQ2 == modulator */
        return AS7058_SUB_SAMPLE_ID_ECG_SEQ2_SUB1;
    }
}

/******************************************************************************
 *                              GLOBAL FUNCTIONS                              *
 ******************************************************************************/

AS7058_EXTRACT2_FUNC_DEFN err_code_t as7058_extract2_prepare_for_new_measurement(
    uint32_t fifo_map, uint32_t sar_map, as7058_sar_transfer_mode_t sar_transfer_mode, as7058_extract2_state_t *p_state)
{
    M_CHECK_NULL_POINTER(p_state);
    if (fifo_map >= (AS7058_SUB_SAMPLE_FLAG_ECG_SEQ2_SUB1 << 1)) {
        /* Invalid flags are set in FIFO map */
        return ERR_ARGUMENT;
    }
    if (sar_map >= AS7058_SUB_SAMPLE_FLAG_ECG_SEQ1_SUB1) {
        /* Sub-samples that do not support SAR are set in SAR map */
        return ERR_ARGUMENT;
    }
    if (sar_transfer_mode > AS7058_SAR_TRANSFER_MODE_INLINE) {
        /* SAR transfer mode is invalid */
        return ERR_ARGUMENT;
    }

    p_state->fifo_map = fifo_map;
    p_state->sar_map = sar_map;
    p_state->sar_transfer_mode = sar_transfer_mode;
    for (uint8_t ppg_modulator = 0; ppg_modulator < AS7058_MODULATOR_NUM_PPG; ppg_modulator++) {
        p_state->last_ppg_sub_samples[ppg_modulator] = AS7058_MODULATOR_SUB_SAMPLE_INVALID;

        for (uint8_t sub_sample = 0; sub_sample < AS7058_MODULATOR_SUB_SAMPLE_NUM_PPG; sub_sample++) {
            p_state->last_pd_offsets[ppg_modulator][sub_sample] = 0;
        }
    }
    p_state->last_pd_offsets_valid = 0;

    return ERR_SUCCESS;
}

AS7058_EXTRACT2_FUNC_DEFN err_code_t as7058_extract2(const uint8_t *p_fifo_data, uint16_t fifo_data_size,
                                                     as7058_extract2_sub_sample_samples_t *pp_sub_sample_samples,
                                                     as7058_extract2_sample_t *p_sample_buffer,
                                                     uint16_t sample_buffer_length, as7058_extract2_state_t *p_state)
{
    if (fifo_data_size > 0) {
        M_CHECK_NULL_POINTER(p_fifo_data);
    }
    M_CHECK_NULL_POINTER(pp_sub_sample_samples);
    M_CHECK_NULL_POINTER(p_sample_buffer);
    M_CHECK_NULL_POINTER(p_state);
    if (p_state->fifo_map >= (AS7058_SUB_SAMPLE_FLAG_ECG_SEQ2_SUB1 << 1)) {
        /* Invalid flags are set in FIFO map */
        return ERR_ARGUMENT;
    }
    if (p_state->sar_map >= AS7058_SUB_SAMPLE_FLAG_ECG_SEQ1_SUB1) {
        /* Sub-samples that do not support SAR are set in SAR map */
        return ERR_ARGUMENT;
    }
    if (p_state->sar_transfer_mode > AS7058_SAR_TRANSFER_MODE_INLINE) {
        /* SAR transfer mode is invalid */
        return ERR_ARGUMENT;
    }

    /* Count samples per sub-sample for partitioning of `p_sample_buffer` */
    uint16_t sub_sample_samples_num[AS7058_SUB_SAMPLE_ID_NUM] = {0};
    as7058_modulator_sub_sample_t last_ppg_sub_samples[AS7058_MODULATOR_NUM_PPG] = {
        p_state->last_ppg_sub_samples[AS7058_MODULATOR_PPG1],
        p_state->last_ppg_sub_samples[AS7058_MODULATOR_PPG2],
    };
    uint16_t fifo_data_index;
    uint16_t fifo_data_index_after_last_begin;
    if (fifo_data_size < 3) {
        /* FIFO data doesn't contain a full FIFO item since fifo_data_size is less than the size of a single item */
        fifo_data_index_after_last_begin = 0;
    } else {
        /* Assuming that fifo_data_size is a multiple of three, the first byte of the last FIFO item is located at index
         * `fifo_data_size - 3`, i.e. the index of the following byte is `fifo_data_size - 2`. */
        fifo_data_index_after_last_begin = fifo_data_size - 2;
    }
    for (fifo_data_index = 0; fifo_data_index < fifo_data_index_after_last_begin; fifo_data_index += 3) {
        as7058_fifo_data_marker_t marker;
        parse_fifo_item(p_fifo_data + fifo_data_index, &marker, NULL);

        as7058_modulator_t modulator;
        as7058_modulator_sub_sample_t sub_sample;
        err_code_t result =
            get_sub_sample_for_marker(marker, p_state->fifo_map, &modulator, &sub_sample, &last_ppg_sub_samples);
        if (result != ERR_NO_DATA) {
            /* Only consider FIFO entries with non-status markers as the status items do not take extra space in
             * `p_sample_buffer` (get_sub_sample_for_marker returns ERR_NO_DATA for status items) */
            M_CHECK_SUCCESS(result);
            sub_sample_samples_num[convert_to_chiplib_sub_sample_id(modulator, sub_sample)]++;
        }
    }
    if (fifo_data_index != fifo_data_size) {
        /* FIFO data size is not a multiple of three */
        return ERR_SIZE;
    }

    /* Partition `p_sample_buffer` into into individually sized sections for each sub-sample; the size of a section
     * depends on the corresponding sub-sample's number of samples */
    as7058_extract2_sample_t *p_next_sub_sample_samples[AS7058_SUB_SAMPLE_ID_NUM];
    (*pp_sub_sample_samples)[AS7058_SUB_SAMPLE_ID_DISABLED] = p_sample_buffer;
    p_next_sub_sample_samples[AS7058_SUB_SAMPLE_ID_DISABLED] = p_sample_buffer;
    for (as7058_sub_sample_ids_t sub_sample = AS7058_SUB_SAMPLE_ID_PPG1_SUB1; sub_sample < AS7058_SUB_SAMPLE_ID_NUM;
         sub_sample++) {
        (*pp_sub_sample_samples)[sub_sample] =
            (*pp_sub_sample_samples)[sub_sample - 1] + sub_sample_samples_num[sub_sample - 1];
        p_next_sub_sample_samples[sub_sample] =
            p_next_sub_sample_samples[sub_sample - 1] + sub_sample_samples_num[sub_sample - 1];
    }
    (*pp_sub_sample_samples)[AS7058_SUB_SAMPLE_ID_NUM] = (*pp_sub_sample_samples)[AS7058_SUB_SAMPLE_ID_ECG_SEQ2_SUB1] +
                                                         sub_sample_samples_num[AS7058_SUB_SAMPLE_ID_ECG_SEQ2_SUB1];
    if ((*pp_sub_sample_samples)[AS7058_SUB_SAMPLE_ID_NUM] > (p_sample_buffer + sample_buffer_length)) {
        /* sample_buffer_length is insufficient */
        return ERR_SIZE;
    }

    /* Extract data */
    for (fifo_data_index = 0; fifo_data_index < fifo_data_index_after_last_begin; fifo_data_index += 3) {
        as7058_fifo_data_marker_t marker;
        uint32_t data;
        parse_fifo_item(p_fifo_data + fifo_data_index, &marker, &data);

        as7058_modulator_t modulator;
        as7058_modulator_sub_sample_t sub_sample;
        err_code_t result = get_sub_sample_for_marker(marker, p_state->fifo_map, &modulator, &sub_sample,
                                                      &p_state->last_ppg_sub_samples);
        if (result != ERR_NO_DATA) { /* i.e. marker != AS7058_FIFO_DATA_MARKER_STATUS */
            M_CHECK_SUCCESS(result);

            as7058_sub_sample_ids_t chiplib_sub_sample_id = convert_to_chiplib_sub_sample_id(modulator, sub_sample);
            uint32_t chiplib_sub_sample_flag = M_AS7058_SUB_SAMPLE_ID_TO_FLAG(chiplib_sub_sample_id);

            uint32_t adc_value;
            uint8_t pd_offset;
            uint8_t sar_enabled;
            if (!(chiplib_sub_sample_flag & p_state->sar_map)) {
                /* `data` contains the 20-bit ADC value, PD offset is not provided */
                adc_value = data;
                pd_offset = 0;
                sar_enabled = 0;
            } else if (AS7058_SAR_TRANSFER_MODE_SEPARATE == p_state->sar_transfer_mode) {
                if (chiplib_sub_sample_flag & p_state->last_pd_offsets_valid) {
                    /* `data` contains the 20-bit ADC value, PD offset is taken from the last status item provided for
                     * this sub-sample */
                    adc_value = data;
                    pd_offset = p_state->last_pd_offsets[modulator][sub_sample];
                    sar_enabled = 1;
                } else {
                    /* No SAR status received for this sub-sample */
                    return ERR_DATA;
                }
            } else { /* AS7058_SAR_TRANSFER_MODE_INLINE == p_state->sar_transfer_mode */
                /* `data` contains the upper 15 bits of the 20-bit ADC value and the PD offset */
                parse_inline_sar_status(data, &adc_value, &pd_offset);
                sar_enabled = 1;
            }

            p_next_sub_sample_samples[chiplib_sub_sample_id]->adc_value = adc_value;
            p_next_sub_sample_samples[chiplib_sub_sample_id]->pd_offset = pd_offset;
            p_next_sub_sample_samples[chiplib_sub_sample_id]->sar_enabled = sar_enabled;
            p_next_sub_sample_samples[chiplib_sub_sample_id]->reserved = 0;
            p_next_sub_sample_samples[chiplib_sub_sample_id]++;
        } else { /* ERR_NO_DATA == result, i.e. AS7058_FIFO_DATA_MARKER_STATUS == marker */
            uint8_t pd_offset;
            err_code_t sar_result = parse_separate_sar_status(data, &modulator, &sub_sample, &pd_offset);
            if (sar_result != ERR_NO_DATA) {
                M_CHECK_SUCCESS(sar_result);

                as7058_sub_sample_ids_t chiplib_sub_sample_id = convert_to_chiplib_sub_sample_id(modulator, sub_sample);
                uint32_t chiplib_sub_sample_flag = M_AS7058_SUB_SAMPLE_ID_TO_FLAG(chiplib_sub_sample_id);

                if ((p_state->sar_transfer_mode != AS7058_SAR_TRANSFER_MODE_SEPARATE) ||
                    !(M_AS7058_SUB_SAMPLE_ID_TO_FLAG(chiplib_sub_sample_id) & p_state->sar_map)) {
                    /* Unexpected SAR status */
                    return ERR_DATA;
                }

                p_state->last_pd_offsets[modulator][sub_sample] = pd_offset;
                p_state->last_pd_offsets_valid |= chiplib_sub_sample_flag;
            }
        }
    }

    return ERR_SUCCESS;
}
