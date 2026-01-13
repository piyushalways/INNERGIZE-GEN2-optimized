/******************************************************************************
 * Copyright © 2022 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

#ifndef __BIO_RRM_A0_H__
#define __BIO_RRM_A0_H__

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

/*!
 * \file      bio_rrm_a0.h
 * \authors   RSIN
 * \copyright ams OSRAM
 * \addtogroup bio_rrm_a0_group Respiration Rate Bio App
 *
 * \brief Implements the Respiration Rate Bio App.
 *
 * This module allows for respiration rate monitoring using a supported ams OSRAM Vital Signs AFE. It conforms to the
 * Bio App Interface, allowing for easy integration in the Application Manager of supported ams OSRAM Vital Signs AFEs.
 *
 * \note For optimal performance, it is strongly advised to enable compiler optimizations when compiling this module
 *       from source.
 *
 * @{
 */

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include "bio_rrm_a0_typedefs.h"

#include "agc_typedefs.h"
#include "vital_signs_accelerometer.h"

/******************************************************************************
 *                                 DEFINITIONS                                *
 ******************************************************************************/

#ifndef BIO_RRM_A0_FUNC_DECL
/*! Preprocessor macro that is placed in front of every public function declaration with external linkage. It expands to
 *  nothing. */
#define BIO_RRM_A0_FUNC_DECL
#endif

/******************************************************************************
 *                                 FUNCTIONS                                  *
 ******************************************************************************/

/*!
 * \brief Initializes the Bio App.
 *
 * \retval ::ERR_SUCCESS Function returns without error.
 */
BIO_RRM_A0_FUNC_DECL err_code_t bio_rrm_a0_initialize(void);

/*!
 *
 * \brief Configures the Bio App.
 *
 * This function can only be called when the Bio App is initialized and not in a processing session.
 *
 * \param[in] p_config Pointer to the configuration structure. This value is ignored by this Bio App as it does not
 *                     support configuration.
 * \param[in] size     Size of the configuration structure. It must be zero.
 *
 * \retval ::ERR_SUCCESS    Function returns without error.
 * \retval ::ERR_SIZE       Argument is invalid.
 * \retval ::ERR_PERMISSION Access to the library is blocked, call ::bio_rrm_a0_initialize at first.
 */
BIO_RRM_A0_FUNC_DECL err_code_t bio_rrm_a0_configure(const void *p_config, uint8_t size);

/*!
 * \brief Copies the current configuration of the Bio App to the provided buffer.
 *
 * This function can only be called when the Bio App is initialized and not in a processing session.
 *
 * As this Bio App does not support configuration, the size of the copied configuration will always be zero bytes.
 *
 * \param[out] p_dest   Points to the start of the buffer where the configuration shall be copied to. This value must
 *                      not be NULL.
 * \param[inout] p_size Points to a variable containing the size of the buffer where the configuration shall be copied
 *                      to. After copying, the value of this variable is updated with the actual size of the copied
 *                      configuration. This value must not be NULL.
 *
 * \retval ::ERR_SUCCESS    Copying successful.
 * \retval ::ERR_NO_DATA    Bio App is not configured.
 * \retval ::ERR_POINTER    At least one pointer argument is NULL which must not be NULL.
 * \retval ::ERR_SIZE       The size of the buffer is not sufficient.
 * \retval ::ERR_PERMISSION Not initialized or in a processing session.
 */
BIO_RRM_A0_FUNC_DECL err_code_t bio_rrm_a0_get_configuration(void *p_dest, uint8_t *p_size);

/*!
 * \brief Provides the sensor signal sample period to the Bio App and starts a processing session.
 *
 * This function can only be called when the Bio App is initialized and not in a processing session.
 *
 * The sample frequency of the PPG signal must be 20 Hz, 25 Hz, 50 Hz, 100 Hz, or 200 Hz. The sample frequency of the
 * accelerometer signal must be 0 (processing of accelerometer data disabled), 25 Hz, 50 Hz, 100 Hz, or 200 Hz.
 *
 * \param[in] p_signal_sample_periods_us Pointer to an array containing the sample periods of each signal in
 *                                       microseconds. There must be ::BIO_RRM_A0_SIGNAL_NUM items in the array,
 *                                       ordered according to ::bio_rrm_a0_signal. This value must not be NULL.
 * \param[in] signal_num                 The number of sensor signals provided to the Bio App. It must be
 *                                       ::BIO_RRM_A0_SIGNAL_NUM.
 * \param[in] acc_sample_period_us       The sample period of the accelerometer in microseconds.
 *
 * \code{.unparsed}
 *     p_signal_sample_
 *     _periods_us
 *          │
 *          └─►┌───────────────────┐
 *        PPG  │ PPG Sample Period │
 *             └───────────────────┘
 * \endcode
 *
 * \retval ::ERR_SUCCESS    Updated successfully.
 * \retval ::ERR_ARGUMENT   Invalid sample period or invalid signal count provided.
 * \retval ::ERR_POINTER    p_signal_sample_periods_us is NULL.
 * \retval ::ERR_PERMISSION Not initialized or in a processing session.
 */
BIO_RRM_A0_FUNC_DECL err_code_t bio_rrm_a0_start(const uint32_t *p_signal_sample_periods_us, uint8_t signal_num,
                                                 uint32_t acc_sample_period_us);

/*!
 * \brief Provides measurement data to the Bio App.
 *
 * This function can only be called when the Bio App is initialized and in a processing session.
 *
 * \param[in] signal_samples_type The data type of sensor signals. It must be ::BIO_RRM_A0_SIGNAL_DATA_TYPE.
 * \param[in] signal_num          The number of sensor signals provided to the Bio App. It must be
 *                                ::BIO_RRM_A0_SIGNAL_NUM.
 * \param[in] p_signal_samples    Pointer to an array of ::bio_signal_samples_t. There must be ::BIO_RRM_A0_SIGNAL_NUM
 *                                items in the array, ordered according to ::bio_rrm_a0_signal. For each signal, the
 *                                same number of samples needs to be provided.
 * \param[in] pp_agc_statuses     Pointer to an array containing pointers to the AGC status of a signal. This value is
 *                                ignored by this Bio App as it does not use AGC data.
 * \param[in] p_acc_samples       Pointer to an array containing accelerometer samples. This value is ignored by this
 *                                Bio App as it does not use accelerometer data.
 * \param[in] acc_sample_num      The number of accelerometer samples contained in the array pointed to by
 *                                p_acc_samples. This value is ignored by this Bio App as it does not use accelerometer
 *                                data.
 * \param[out] p_result           The value pointed to by this argument is updated with information  whether the Bio App
 *                                is ready for execution. This value must not be NULL.
 *
 * \code{.unparsed}
 *     p_signal_
 *     samples
 *        │               p_i32
 *        └─►┌──────────┐   ┌──►┌──────────────┐
 *           │   data ──────┘   │ PPG Sample 0 │
 *       PPG │ ──────── │       ├──────────────┤
 *           │ count: 2 │       │ PPG Sample 1 │
 *           └──────────┘       └──────────────┘
 * \endcode
 *
 * \retval ::ERR_SUCCESS            Data accepted.
 * \retval ::ERR_ARGUMENT           Invalid signal sample type or invalid signal count provided.
 * \retval ::ERR_POINTER            At least one pointer argument is NULL which must not be NULL.
 * \retval ::ERR_PERMISSION         Not initialized or not in a processing session.
 * \retval ::ERR_SYNCHRONISATION    Accelerator and PPG data are out of synchronisation. Internal buffers are too small.
 */
BIO_RRM_A0_FUNC_DECL err_code_t bio_rrm_a0_set_input(bio_signal_samples_type_t signal_samples_type,
                                                     const bio_signal_samples_t *p_signal_samples,
                                                     const agc_status_t *const *pp_agc_statuses, uint8_t signal_num,
                                                     const vs_acc_data_t *p_acc_samples, uint8_t acc_sample_num,
                                                     bio_execution_status_t *p_result);

/*!
 * \brief Processes the data previously provided to the Bio App.
 *
 * This function can be called once after ::bio_rrm_a0_set_input indicated via the p_result argument that the Bio App is
 * executable. Afterwards, this function can be called again when a subsequent call of ::bio_rrm_a0_set_input indicated
 * that the Bio App is executable. The Bio App must be initialized and in a processing session when calling this
 * function.
 *
 * \param[out] p_result The value pointed to by this argument is updated with information whether the Bio App has data
 *                      available for output. This value must not be NULL.
 *
 * \retval ::ERR_SUCCESS    Processing successful.
 * \retval ::ERR_POINTER    p_result is NULL.
 * \retval ::ERR_PERMISSION Not initialized or not in a processing session.
 */
BIO_RRM_A0_FUNC_DECL err_code_t bio_rrm_a0_execute(bio_output_status_t *p_result);

/*!
 * \brief Copies output data generated by the Bio App to a buffer provided by the caller.
 *
 * This function can be called once after ::bio_rrm_a0_execute indicated via the p_result argument that output data is
 * available. Afterwards, this function can be called again when a subsequent call of ::bio_rrm_a0_execute indicated
 * that output data is available. The Bio App must be initialized and in a processing session when calling this
 * function.
 * The size of the output data is sizeof(bio_rrm_a0_output_t).
 *
 * \note The internal buffer of the algorithm is a sliding buffer of 20 seconds, and the algorithm processes it every
 *       second and therefore the first result would be available after 20 second.
 *       Once processed, the returned respiratory rate value is expressed in beats per minute multiplied by 100.
 *       So, for instance, a value of 3050 means 30.5 bpm. This result also consists of a confidence value associated
 *       with the respiratory rate, which gives a hint of certainty about the found respiratory rate. This confidence is
 *       expressed between 0 and 100. It might take longer if the data is not good enough (presence of artifacts).
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
BIO_RRM_A0_FUNC_DECL err_code_t bio_rrm_a0_get_output(void *p_dest, uint16_t *p_size);

/*!
 * \brief Stops the current processing session of the Bio App, allowing it to be reconfigured.
 *
 * This function can only be called when the Bio App is initialized.
 *
 * \retval ::ERR_SUCCESS    Stopping successful.
 * \retval ::ERR_PERMISSION Not initialized.
 */
BIO_RRM_A0_FUNC_DECL err_code_t bio_rrm_a0_stop(void);

/*!
 * \brief De-initializes the Bio App.
 *
 * \retval ::ERR_SUCCESS De-initialization successful.
 */
BIO_RRM_A0_FUNC_DECL err_code_t bio_rrm_a0_shutdown(void);

/*!
 * \brief Gets the version of the Bio App.
 *
 * \return Version string.
 */
BIO_RRM_A0_FUNC_DECL const char *bio_rrm_a0_get_version(void);

#ifdef __cplusplus
}
#endif // __cplusplus

/*! @} */

#endif /* __BIO_RRM_A0_H__ */
