/******************************************************************************
 * Copyright © 2022 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

#ifndef __AS7058_RAW_APP_H__
#define __AS7058_RAW_APP_H__

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

/*!
 * \file       as7058_raw_app.h
 * \authors    PKRN
 * \copyright  ams OSRAM
 * \addtogroup AS7058_RAW_APP Raw Data Application
 *
 * @{
 */

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include <stdint.h>

#include "as7058_raw_app_typedefs.h"

#include "error_codes.h"
#include "as7058_typedefs.h"
#include "as7058_app_manager_typedefs.h"
#include "agc_typedefs.h"
#include "vital_signs_accelerometer.h"
#include "bio_common.h"

/******************************************************************************
 *                                 FUNCTIONS                                  *
 ******************************************************************************/

/*!
 * \brief Initializes the Raw Data application.
 *
 * \retval ::ERR_SUCCESS    Initialized successfully.
 */
err_code_t as7058_raw_app_initialize(void);

/*!
 * \brief Configures the application.
 *
 * This function can only be called when the application is initialized and not in a processing session.
 *
 * \param[in] p_config Pointer to the configuration structure, see ::as7058_raw_app_configuration_t. It must not be
 *                     NULL.
 * \param[in] size     Size of the configuration structure. It must be `sizeof(as7058_raw_app_configuration_t)`.
 *
 * \retval ::ERR_SUCCESS    Updated successfully.
 * \retval ::ERR_POINTER    Invalid pointer to configuration structure.
 * \retval ::ERR_SIZE       Size does not match expected size.
 * \retval ::ERR_PERMISSION Not initialized or in a processing session.
 */
err_code_t as7058_raw_app_configure(const void *p_config, uint8_t size);

/*!
 * \brief Provides measurement metadata to the application and starts a processing session.
 *
 * This function can only be called when the application is initialized and not in a processing session.
 *
 * \param[in] ppg_sample_period_us      Current sample period of the PPG sequencer in microseconds.
 * \param[in] ecg_seq1_sample_period_us Current sample period of ECG SEQ1 in microseconds.
 * \param[in] ecg_seq2_sample_period_us Current sample period of ECG SEQ2 in microseconds.
 * \param[in] fifo_map                  Current FIFO map.
 *
 * \retval ::ERR_SUCCESS    Prepared successfully.
 * \retval ::ERR_ARGUMENT   Invalid argument value.
 * \retval ::ERR_PERMISSION Not initialized or in a processing session.
 */
err_code_t as7058_raw_app_start(uint32_t ppg_sample_period_us, uint32_t ecg_seq1_sample_period_us,
                                uint32_t ecg_seq2_sample_period_us, uint32_t fifo_map);

/*!
 * \brief Provides measurement data to the application.
 *
 * This function can only be called when the application is initialized and in a processing session.
 *
 * \param[in] p_fifo_data      Pointer to the FIFO data buffer.
 * \param[in] fifo_data_size   Size of the data in the FIFO data buffer in bytes.
 * \param[in] status_events    Status events of the sensor.
 * \param[in] p_agc_statuses   Pointer to a buffer containing the current AGC statuses.
 * \param[in] agc_statuses_num Number of items in the AGC statuses buffer.
 * \param[in] p_acc_data       Pointer to accelerometer data buffer.
 * \param[in] acc_data_cnt     Number of samples in the accelerometer data buffer FIFO data.
 * \param[in] ext_event_cnt    Number of external events that occurred since the last call of this function.
 * \param[out] p_result        The value pointed to by this argument is updated with information whether the application
 *                             is ready for execution. This value must not be NULL.
 *
 * \retval ::ERR_SUCCESS    Appended data successfully.
 * \retval ::ERR_POINTER    Invalid pointer argument value.
 * \retval ::ERR_ARGUMENT   Too many AGC status information items provided.
 * \retval ::ERR_PERMISSION Not initialized or not in a processing session.
 * \retval ::ERR_FIFO       Unable to store provided data.
 */
err_code_t as7058_raw_app_set_input(const uint8_t *p_fifo_data, uint16_t fifo_data_size,
                                    as7058_status_events_t status_events, const agc_status_t *p_agc_statuses,
                                    uint8_t agc_statuses_num, const vs_acc_data_t *p_acc_data, uint8_t acc_data_cnt,
                                    uint8_t ext_event_cnt, bio_execution_status_t *p_result);

/*!
 * \brief Processes the data provided to the application.
 *
 * This function can only be called when the application is initialized and in a processing session.
 *
 * \param[out] p_result The value pointed to by this argument is updated with information whether the application has
 *                      data available for output. This value must not be NULL.
 *
 * \retval ::ERR_SUCCESS    Executed successfully.
 * \retval ::ERR_POINTER    Invalid pointer argument value.
 * \retval ::ERR_PERMISSION Not initialized or not in a processing session.
 */
err_code_t as7058_raw_app_execute(bio_output_status_t *p_result);

/*!
 * \brief Gets output data from the application.
 *
 * This function can only be called when the application is initialized and in a processing session.
 *
 * \param[out]   p_dest     Pointer to the buffer where data shall be copied to.
 * \param[inout] p_size     Pointer to the maximum size of the destination buffer. Will be updated with the actual size
 *                          of the output data after copying.
 *
 * \retval ::ERR_SUCCESS    Copied data successfully.
 * \retval ::ERR_NO_DATA    No data available for output.
 * \retval ::ERR_POINTER    Invalid pointer argument value.
 * \retval ::ERR_ARGUMENT   Destination buffer size insufficient.
 * \retval ::ERR_PERMISSION Not initialized or not in a processing session.
 */
err_code_t as7058_raw_app_get_output(void *p_dest, uint16_t *p_size);

/*!
 * \brief Ends the current processing session.
 *
 * This function can only be called when the application is initialized.
 *
 * \retval ::ERR_SUCCESS    Processing session ended successfully.
 * \retval ::ERR_PERMISSION Not initialized.
 */
err_code_t as7058_raw_app_stop(void);

/*!
 * \brief De-initializes the application.
 *
 * \retval ::ERR_SUCCESS De-initialized successfully.
 */
err_code_t as7058_raw_app_shutdown(void);

/*! @} */

#ifdef __cplusplus
}
#endif // __cplusplus

#endif /* __AS7058_RAW_APP_H__ */
