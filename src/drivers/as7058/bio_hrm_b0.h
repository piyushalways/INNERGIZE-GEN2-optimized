/******************************************************************************
 * Copyright © 2023 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

#ifndef __BIO_HRM_B0_H__
#define __BIO_HRM_B0_H__

#ifdef __cplusplus
extern "C" {
#endif

/*!
 * \addtogroup bio_hrm_b0 HRM Bio App
 *
 * \brief Implements the HRM Bio App.
 *
 * This module allows for heart rate monitoring using a supported ams OSRAM Vital Signs AFE. It conforms to the Bio App
 * Interface, allowing for easy integration in the Application Manager of supported ams OSRAM Vital Signs AFEs.
 *
 * @{
 */

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include "bio_hrm_b0_typedefs.h"

#include "agc_typedefs.h"
#include "vital_signs_accelerometer.h"

/******************************************************************************
 *                                 DEFINITIONS                                *
 ******************************************************************************/

#ifndef BIO_HRM_B0_FUNC_DECL
/*! Preprocessor macro that is placed in front of every public function declaration with external linkage. It expands to
 *  nothing. */
#define BIO_HRM_B0_FUNC_DECL
#endif

/******************************************************************************
 *                                 FUNCTIONS                                  *
 ******************************************************************************/

/*!
 * \brief Initializes the Bio App.
 *
 * \retval ::ERR_SUCCESS Initialized successfully.
 */
BIO_HRM_B0_FUNC_DECL err_code_t bio_hrm_b0_initialize(void);

/*!
 * \brief Configures the Bio App.
 *
 * This function can only be called when the Bio App is initialized and not in a processing session.
 *
 * \param[in] p_config Pointer to the configuration structure, see ::bio_hrm_b0_configuration_t. It must not be NULL.
 * \param[in] size     Size of the configuration structure. It must be `sizeof(bio_hrm_b0_configuration_t)`.
 *
 * \retval ::ERR_SUCCESS    Updated successfully.
 * \retval ::ERR_POINTER    Invalid pointer to configuration structure.
 * \retval ::ERR_SIZE       Size does not match expected size.
 * \retval ::ERR_ARGUMENT   Invalid configuration values.
 * \retval ::ERR_PERMISSION Not initialized.
 */
BIO_HRM_B0_FUNC_DECL err_code_t bio_hrm_b0_configure(const void *p_config, uint8_t size);

/*!
 * \brief Copies the current configuration of the Bio App to the provided buffer.
 *
 * This function can only be called when the Bio App is initialized and not in a processing session.
 *
 * The size of the configuration is `sizeof(bio_hrm_b0_configuration_t)`.
 *
 * \param[out] p_dest   Points to the start of the buffer where the configuration shall be copied to. This value must
 *                      not be NULL.
 * \param[inout] p_size Points to a variable containing the size of the buffer where the configuration shall be copied
 *                      to. After copying, the value of this variable is updated with the actual size of the copied
 *                      configuration. This value must not be NULL.
 *
 * \retval ::ERR_SUCCESS    Copying successful.
 * \retval ::ERR_POINTER    At least one pointer argument is NULL which must not be NULL.
 * \retval ::ERR_SIZE       The size of the buffer is not sufficient.
 * \retval ::ERR_PERMISSION Not initialized or in a processing session.
 */
BIO_HRM_B0_FUNC_DECL err_code_t bio_hrm_b0_get_configuration(void *p_dest, uint8_t *p_size);

/*!
 * \brief Provides the sensor signals and accelerometer sample periods to the Bio App and starts a processing session.
 *
 * This function can only be called when the Bio App is initialized.
 *
 * The sample frequency of the PPG signals must be 25 Hz, 50 Hz, 100 Hz, or 200 Hz. The sample frequency of the
 * accelerometer signal must be 0 (processing of accelerometer data disabled), 25 Hz, 50 Hz, 100 Hz, or 200 Hz.
 *
 * \param[in] p_signal_sample_periods_us Pointer to an array containing the sample periods of each signal in
 *                                       microseconds. There must be ::BIO_HRM_B0_SIGNAL_NUM items in the array, ordered
 *                                       according to ::bio_hrm_b0_signal. This value must not be NULL.
 * \param[in] signal_num                 The number of sensor signals provided to the Bio App. It must be
 *                                       ::BIO_HRM_B0_SIGNAL_NUM.
 * \param[in] acc_sample_period_us       The sample period of the accelerometer in microseconds.
 *
 * \code{.unparsed}
 *     p_signal_sample_
 *     _periods_us
 *          │
 *          └─►┌──────────┐   ┌──►┌───────────────────────┐
 *       Green │          ├───┘   │ Green Sample Period   │
 *             ├──────────┤       └───────────────────────┘
 *     Ambient │          ├──────►┌───────────────────────┐
 *             └──────────┘       │ Ambient Sample Period │
 *                                └───────────────────────┘
 * \endcode
 *
 * \retval ::ERR_SUCCESS    Updated successfully.
 * \retval ::ERR_ARGUMENT   Invalid sample periods or invalid signal count provided.
 * \retval ::ERR_POINTER    p_signal_sample_periods_us is NULL.
 * \retval ::ERR_PERMISSION Not initialized.
 */
BIO_HRM_B0_FUNC_DECL err_code_t bio_hrm_b0_start(const uint32_t *p_signal_sample_periods_us, uint8_t signal_num,
                                                 uint32_t acc_sample_period_us);

/*!
 * \brief Provides measurement data to the Bio App.
 *
 * This function can only be called when the Bio App is initialized and in a processing session.
 *
 * \param[in] signal_samples_type The data type of sensor signals. It must be ::BIO_HRM_B0_SIGNAL_DATA_TYPE.
 * \param[in] signal_num          The number of sensor signals provided to the Bio App. It must be
 *                                ::BIO_HRM_B0_SIGNAL_NUM.
 * \param[in] p_signal_samples    Pointer to an array of ::bio_signal_samples_t. There must be ::BIO_HRM_B0_SIGNAL_NUM
 *                                items in the array, ordered according to ::bio_hrm_b0_signal. For each signal, the
 *                                same number of samples needs to be provided.
 * \param[in] pp_agc_statuses     Pointer to an array containing pointers to the AGC status of a signal. This parameter
 *                                is ignored as this Bio App does not process AGC statuses.
 * \param[in] p_acc_samples       Pointer to an array containing accelerometer samples.
 * \param[in] acc_sample_num      The number of accelerometer samples contained in the array pointed to by
 *                                p_acc_samples.
 * \param[out] p_result           The value pointed to by this argument is updated with information whether the Bio App
 *                                is ready for execution. This value must not be NULL.
 *
 * \code{.unparsed}
 *       p_signal_
 *       samples
 *          │               p_i32
 *          └─►┌──────────┐   ┌──►┌──────────────────┐
 *             │   data ──────┘   │ Green Sample 0   │
 *       Green │ ──────── │       ├──────────────────┤
 *             │ count: 2 │       │ Green Sample 1   │
 *             ├──────────┤ p_i32 └──────────────────┘
 *             │   data ─────────►┌──────────────────┐
 *     Ambient │ ──────── │       │ Ambient Sample 0 │
 *             │ count: 2 │       ├──────────────────┤
 *             └──────────┘       │ Ambient Sample 1 │
 *                                └──────────────────┘
 * \endcode
 *
 * \retval ::ERR_SUCCESS         Data accepted.
 * \retval ::ERR_ARGUMENT        Invalid signal sample type, invalid signal count provided, or not all signals have the
 *                               same number of sample.
 * \retval ::ERR_POINTER         At least one pointer argument is NULL which must not be NULL.
 * \retval ::ERR_SYNCHRONISATION Accelerator and PPG data are out of synchronisation. Internal buffers are too small.
 * \retval ::ERR_PERMISSION      Not initialized or not in a processing session.
 */
BIO_HRM_B0_FUNC_DECL err_code_t bio_hrm_b0_set_input(bio_signal_samples_type_t signal_samples_type,
                                                     const bio_signal_samples_t *p_signal_samples,
                                                     const agc_status_t *const *pp_agc_statuses, uint8_t signal_num,
                                                     const vs_acc_data_t *p_acc_samples, uint8_t acc_sample_num,
                                                     bio_execution_status_t *p_result);

/*!
 * \brief Processes the data previously provided to the Bio App.
 *
 * This function can be called once after ::bio_hrm_b0_set_input indicated via the p_result argument that the Bio App is
 * executable. Afterwards, this function can be called again when a subsequent call of ::bio_hrm_b0_set_input indicated
 * that the Bio App is executable. The Bio App must be initialized and in a processing session when calling this
 * function.
 *
 * \param[out] p_result The value pointed to by this argument is updated with information whether the Bio App has data
 *                      available for output. This value must not be NULL.
 *
 * \retval ::ERR_SUCCESS    Processing successful.
 * \retval ::ERR_DATA       Data processing failed.
 * \retval ::ERR_POINTER    p_result is NULL.
 * \retval ::ERR_PERMISSION Not initialized or not in a processing session.
 */
BIO_HRM_B0_FUNC_DECL err_code_t bio_hrm_b0_execute(bio_output_status_t *p_result);

/*!
 * \brief Copies output data generated by the app to a buffer provided by the caller.
 *
 * This function can be called once after ::bio_hrm_b0_execute indicated via the p_result argument that output data is
 * available. Afterwards, this function can be called again when a subsequent call of ::bio_hrm_b0_execute indicated
 * that output data is available. The Bio App must be initialized and in a processing session when calling this
 * function.
 *
 * The size of the output data is `sizeof(bio_hrm_b0_output_t)`.
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
BIO_HRM_B0_FUNC_DECL err_code_t bio_hrm_b0_get_output(void *p_dest, uint16_t *p_size);

/*!
 * \brief Stops the current processing session of the Bio App, allowing it to be reconfigured.
 *
 * This function can only be called when the Bio App is initialized and in a processing session.
 *
 * \retval ::ERR_SUCCESS    Stopping successful.
 * \retval ::ERR_PERMISSION Not initialized or not in a processing session.
 */
BIO_HRM_B0_FUNC_DECL err_code_t bio_hrm_b0_stop(void);

/*!
 * \brief De-initializes the Bio App.
 *
 * \retval ::ERR_SUCCESS De-initialization successful.
 */
BIO_HRM_B0_FUNC_DECL err_code_t bio_hrm_b0_shutdown(void);

/*!
 * \brief Gets the version of the Bio App.
 *
 * \return Version string.
 */
BIO_HRM_B0_FUNC_DECL const char *bio_hrm_b0_get_version(void);

#ifdef __cplusplus
}
#endif

/*! @} */

#endif /* __BIO_HRM_B0_H__ */
