/******************************************************************************
 * Copyright © 2022 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

#ifndef __AS7058_EXTRACT_H__
#define __AS7058_EXTRACT_H__

/*!
 * \file        as7058_extract.h
 * \authors     ARIT
 * \copyright   ams OSRAM
 * \addtogroup  extract_group Sub-sample extraction
 *
 * \brief Extract module to get dedicated sub-samples from FIFO data stream.
 *
 *  @{
 */

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include "as7058_typedefs.h"
#include "error_codes.h"
#include "std_inc.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

/*! Metadata description. */
struct extract_metadata {
    as7058_sub_sample_flags_t ppg1_sub; /*!< Sub-sample of PPG1. */
    as7058_sub_sample_flags_t ppg2_sub; /*!< Sub-sample of PPG2. */
};

/*! Metadata for extraction function. */
typedef struct {
    uint32_t fifo_map;               /*!< Currently available sub-samples inside the FIFO data stream.
                                          See ::as7058_sub_sample_flags and ::as7058_meas_config_t. */
    struct extract_metadata current; /*!< Current metadata. */
    struct extract_metadata recent;  /*!< Recent metadata. */
    uint8_t copy_recent_to_current;  /*!< Non-zero value: Current meta data will be overwritten by recent metadata. */
} as7058_extract_metadata_t;

/******************************************************************************
 *                                 FUNCTIONS                                  *
 ******************************************************************************/

/*!
 * \brief Extract the requested sub-samples from FIFO data stream.
 *
 * \param[in] extract_sub_id            Sub-sample ID for which the FIFO data shall extracted.
 * \param[in] p_fifo_data               FIFO data.
 * \param[in] fifo_data_size            Size of FIFO data.
 * \param[out] p_chan_data              Pointer to buffer where the sub-sample data can be saved.
 * \param[inout] p_chan_data_num        Input: Number of provided p_chan_data elements;
 *                                      Output: Number of used p_chan_data elements.
 * \param[inout] p_metadata             Structure will be used to get last sequencer information and save newest one.
 *                                      Furthermore, the FIFO mapping must be configured here.

 * \retval ::ERR_SUCCESS                Function returns without error.
 * \retval ::ERR_ARGUMENT               At least one parameter is wrong.
 * \retval ::ERR_POINTER                Detected NULL pointer for data.
 */
err_code_t as7058_extract_samples(as7058_sub_sample_ids_t extract_sub_id, const uint8_t *p_fifo_data,
                                  uint16_t fifo_data_size, uint32_t *p_chan_data, uint16_t *p_chan_data_num,
                                  as7058_extract_metadata_t *p_metadata);

#ifdef __cplusplus
}
#endif // __cplusplus

/*! @} */

#endif /* __AS7058_EXTRACT_H__ */
