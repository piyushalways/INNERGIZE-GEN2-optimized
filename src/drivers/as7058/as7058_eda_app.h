/******************************************************************************
 * Copyright © 2022 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

#ifndef __AS7058_EDA_APP_H__
#define __AS7058_EDA_APP_H__

#ifdef __cplusplus
extern "C" {
#endif

/*!
 * \file       as7058_eda_app.h
 * \authors    PKRN
 * \copyright  ams OSRAM
 * \addtogroup AS7058_EDA_APP EDA Application
 *
 * @{
 */

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include "as7058_eda_app_typedefs.h"

#include "as7058_typedefs.h"
#include "agc_typedefs.h"
#include "bio_common.h"
#include "vital_signs_accelerometer.h"

/******************************************************************************
 *                                 FUNCTIONS                                  *
 ******************************************************************************/

/*!
 * \brief Initializes the bio app.
 *
 * \retval ::ERR_SUCCESS Initialized successfully.
 */
err_code_t as7058_eda_app_initialize(void);

/*!
 * \brief Configures the bio app.
 *
 * This function can only be called when the bio app is initialized and not in a processing session.
 *
 * \param[in] p_config Pointer to the configuration structure, see ::as7058_eda_app_configuration_t. It must not be
 *                     NULL.
 * \param[in] size     Size of the configuration structure. It must be `sizeof(as7058_eda_app_configuration_t)`.
 *
 * \retval ::ERR_SUCCESS    Updated successfully.
 * \retval ::ERR_ARGUMENT   Configuration is invalid.
 * \retval ::ERR_POINTER    Invalid pointer to configuration structure.
 * \retval ::ERR_SIZE       Size does not match expected size.
 * \retval ::ERR_PERMISSION Not initialized or in a processing session.
 */
err_code_t as7058_eda_app_configure(const void *p_config, uint8_t size);

/*!
 * \brief Provides the sensor signals and accelerometer sample periods to the bio app and starts a processing session.
 *
 * This function can only be called when the bio app is initialized and not in a processing session.
 *
 * \param[in] p_signal_sample_periods_us Pointer to an array containing the sample periods of each signal in
 *                                       microseconds. This value is ignored by this bio app since it does not require
 *                                       sample period information.
 * \param[in] signal_num                 The number of sensor signals provided to the bio app. It must be
 *                                       ::AS7058_EDA_APP_SIGNAL_NUM.
 * \param[in] acc_sample_period_us       The sample period of the accelerometer in microseconds. This value is ignored
 *                                       by this bio app as it does not use accelerometer data.
 *
 * \htmlonly
 *             p_signal_sample_
 *             _periods_us
 *                  │
 *                  └─►┌───────────────────────────────┐
 *     EDA Alternating │ EDA Alternating Sample Period │
 *                     ├───────────────────────────────┤
 *         Temperature │   Temperature Sample Period   │
 *                     └───────────────────────────────┘
 * \endhtmlonly
 *
 * \retval ::ERR_SUCCESS    Updated successfully.
 * \retval ::ERR_ARGUMENT   Invalid signal count provided.
 * \retval ::ERR_CONFIG     Application has not been configured.
 * \retval ::ERR_PERMISSION Not initialized or in a processing session.
 */
err_code_t as7058_eda_app_start(const uint32_t *p_signal_sample_periods_us, uint8_t signal_num,
                                uint32_t acc_sample_period_us);

/*!
 * \brief Provides measurement data to the bio app.
 *
 * This function can only be called when the bio app is initialized and in a processing session.
 *
 * \param[in] signal_samples_type The data type of sensor signals. It must be ::AS7058_EDA_APP_SIGNAL_DATA_TYPE.
 * \param[in] p_signal_samples    Pointer to an array of ::bio_signal_samples_t. There must be
 *                                ::AS7058_EDA_APP_SIGNAL_NUM items in the array, ordered according to
 *                                ::as7058_eda_app_signal. This value must not be NULL.
 * \param[in] pp_agc_statuses     Pointer to an array containing pointers to the AGC status of a signal. This value is
 *                                ignored by this bio app.
 * \param[in] signal_num          The number of sensor signals provided to the bio app. This value must be
 *                                ::AS7058_EDA_APP_SIGNAL_NUM.
 * \param[in] p_acc_samples       Pointer to an array containing accelerometer samples. This value is ignored by this
 *                                bio app.
 * \param[in] acc_sample_num      The number of accelerometer samples contained in the array pointed to by
 *                                p_acc_samples. This value is ignored by this bio app.
 * \param[out] p_result           The value pointed to by this argument is updated with information whether the bio app
 *                                is ready for execution. This value must not be NULL.
 *
 * \htmlonly
 *               p_signal_
 *               samples
 *                  │               p_i32
 *                  └─►┌──────────┐   ┌──►┌──────────────────────┐
 *                     │   data ──────┘   │     EDA+ Sample 0    │
 *     EDA Alternating │ ──────── │       ├──────────────────────┤
 *                     │ count: 4 │       │     EDA- Sample 0    │
 *                     ├──────────┤ p_i32 ├──────────────────────┤
 *                     │   data ──────┐   │     EDA+ Sample 1    │
 *         Temperature │ ──────── │   │   ├──────────────────────┤
 *                     │ count: 2 │   │   │     EDA- Sample 1    │
 *                     └──────────┘   │   └──────────────────────┘
 *                                    └──►┌──────────────────────┐
 *                                        │ Temperature Sample 0 │
 *                                        ├──────────────────────┤
 *                                        │ Temperature Sample 1 │
 *                                        └──────────────────────┘
 * \endhtmlonly
 *
 * \retval ::ERR_SUCCESS    Data accepted.
 * \retval ::ERR_ARGUMENT   Invalid signal sample type or invalid signal count provided.
 * \retval ::ERR_POINTER    At least one pointer argument is NULL which must not be NULL.
 * \retval ::ERR_FIFO       Cannot store the provided data due to exhausted internal buffers.
 * \retval ::ERR_PERMISSION Not initialized or not in a processing session.
 */
err_code_t as7058_eda_app_set_input(bio_signal_samples_type_t signal_samples_type,
                                    const bio_signal_samples_t *p_signal_samples,
                                    const agc_status_t *const *pp_agc_statuses, uint8_t signal_num,
                                    const vs_acc_data_t *p_acc_samples, uint8_t acc_sample_num,
                                    bio_execution_status_t *p_result);

/*!
 * \brief Processes the data previously provided to the bio app.
 *
 * This function can be called once after ::as7058_eda_app_set_input indicated via the p_result argument that the bio
 * app is executable. Afterwards, this function can be called again when a subsequent call of
 * ::as7058_eda_app_set_input indicated that the bio app is executable. The bio app must be initialized and in a
 * processing session when calling this function.
 *
 * \param[out] p_result The value pointed to by this argument is updated with information whether the bio app has data
 *                      available for output. This value must not be NULL.
 *
 * \retval ::ERR_SUCCESS    Processing successful.
 * \retval ::ERR_POINTER    p_result is NULL.
 * \retval ::ERR_DATA       EDA calculation resulted in invalid results.
 * \retval ::ERR_FIFO       Cannot store the EDA calculation results due to exhausted internal buffers.
 * \retval ::ERR_PERMISSION Not initialized or not in a processing session.
 */
err_code_t as7058_eda_app_execute(bio_output_status_t *p_result);

/*!
 * \brief Copies output data generated by the app to a buffer provided by the caller.
 *
 * This function can be called once after ::as7058_eda_app_execute indicated via the p_result argument that output data
 * is available. Afterwards, this function can be called again when a subsequent call of ::as7058_eda_app_execute
 * indicated that output data is available. The bio app must be initialized and in a processing session when calling
 * this function.
 *
 * The size of the output data is sizeof(as7058_eda_app_output_t).
 *
 * \param[out] p_dest   Points to the start of the buffer where the output data shall be copied to. This value must not
 *                      be NULL.
 * \param[inout] p_size Points to a variable containing the size of the buffer where the output data shall be copied to.
 *                      After copying, the value of this variable is updated with the actual size of the copied data.
 *                      This value must not be NULL.
 *
 * \retval ::ERR_SUCCESS    Copying successful.
 * \retval ::ERR_POINTER    At least one pointer argument is NULL which must not be NULL.
 * \retval ::ERR_SIZE       The size of the buffer is not sufficient.
 * \retval ::ERR_NO_DATA    No output data is available for copying.
 * \retval ::ERR_PERMISSION Not initialized or not in a processing session.
 */
err_code_t as7058_eda_app_get_output(void *p_dest, uint16_t *p_size);

/*!
 * \brief Stops the current processing session of the bio app, allowing it to be reconfigured.
 *
 * This function can only be called when the bio app is initialized and in a processing session.
 *
 * \retval ::ERR_SUCCESS    Stopping successful.
 * \retval ::ERR_PERMISSION Not initialized.
 */
err_code_t as7058_eda_app_stop(void);

/*!
 * \brief De-initializes the bio app.
 *
 * \retval ::ERR_SUCCESS De-initialization successful.
 */
err_code_t as7058_eda_app_shutdown(void);

#ifdef __cplusplus
}
#endif

/*! @} */

#endif /* __AS7058_EDA_APP_H__ */
