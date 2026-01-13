/******************************************************************************
 * Copyright © 2022 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

#ifndef __BIO_SRD_H__
#define __BIO_SRD_H__

#ifdef __cplusplus
extern "C" {
#endif

/*!
 * \file       bio_srd.h
 * \authors    PKRN
 * \copyright  ams OSRAM
 * \addtogroup bio_srd_group
 *
 * \brief This Bio App has three signal status regions. It outputs the region in which the input value currently into.
 *        The thresholds of the regions are configurable.
 *
 * @{
 */

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include "bio_srd_typedefs.h"

#include "agc_typedefs.h"
#include "vital_signs_accelerometer.h"

/******************************************************************************
 *                                 FUNCTIONS                                  *
 ******************************************************************************/

/*!
 * \brief Initializes the Bio App.
 *
 * \retval ::ERR_SUCCESS Initialized successfully.
 */
err_code_t bio_srd_initialize(void);

/*!
 * \brief Configures the Bio App.
 *
 * This function can only be called when the Bio App is initialized and not in a processing session.
 *
 * \param[in] p_config Pointer to the configuration structure, see ::bio_srd_configuration_t. It must not be NULL.
 * \param[in] size     Size of the configuration structure. It must be `sizeof(bio_srd_configuration_t)`.
 *
 * \retval ::ERR_SUCCESS    Updated successfully.
 * \retval ::ERR_ARGUMENT   Upper threshold is lower than the lower threshold.
 * \retval ::ERR_POINTER    Invalid pointer to configuration structure.
 * \retval ::ERR_SIZE       Size does not match expected size.
 * \retval ::ERR_PERMISSION Not initialized or in a processing session.
 */
err_code_t bio_srd_configure(const void *p_config, uint8_t size);

/*!
 * \brief Copies the current configuration of the Bio App to the provided buffer.
 *
 * This function can only be called when the Bio App is initialized and not in a processing session.
 *
 * The size of the configuration is `sizeof(bio_srd_configuration_t)`.
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
err_code_t bio_srd_get_configuration(void *p_dest, uint8_t *p_size);

/*!
 * \brief Provides the sensor signals and accelerometer sample periods to the Bio App and starts a processing session.
 *
 * This function can only be called when the Bio App is initialized and not in a processing session.
 *
 * \param[in] p_signal_sample_periods_us Pointer to an array containing the sample periods of each signal in
 *                                       microseconds. There must be ::BIO_SRD_SIGNAL_NUM items in the array,
 *                                       ordered according to ::bio_srd_signal. This value must not be NULL. This
 *                                       app requires that all signals are samples with an identical non-zero sample
 *                                       period.
 * \param[in] signal_num                 The number of sensor signals provided to the Bio App. It must be
 *                                       ::BIO_SRD_SIGNAL_NUM.
 * \param[in] acc_sample_period_us       The sample period of the accelerometer in microseconds. This value is ignored
 *                                       by this Bio App as it does not use accelerometer data.
 *
 * \htmlonly
 *       p_signal_sample_
 *       _periods_us
 *            │
 *            └─►┌───────────────────────────┐
 *   Main Signal │ Main Signal Sample Period │
 *               └───────────────────────────┘
 * \endhtmlonly
 *
 * \retval ::ERR_SUCCESS    Updated successfully.
 * \retval ::ERR_ARGUMENT   Invalid sample period or invalid signal count provided.
 * \retval ::ERR_POINTER    p_signal_sample_periods_us is NULL.
 * \retval ::ERR_PERMISSION Not initialized or in a processing session.
 */
err_code_t bio_srd_start(const uint32_t *p_signal_sample_periods_us, uint8_t signal_num, uint32_t acc_sample_period_us);

/*!
 * \brief Provides measurement data to the Bio App.
 *
 * This function can only be called when the Bio App is initialized and in a processing session.
 *
 * \param[in] signal_samples_type The data type of sensor signals. It must be ::BIO_SRD_SIGNAL_DATA_TYPE.
 * \param[in] signal_num          The number of sensor signals provided to the Bio App. It must be
 *                                ::BIO_SRD_SIGNAL_NUM.
 * \param[in] p_signal_samples    Pointer to an array of ::bio_signal_samples_t. There must be ::BIO_SRD_SIGNAL_NUM
 *                                items in the array, ordered according to ::bio_srd_signal. For each signal, the
 *                                same number of samples needs to be provided.
 * \param[in] pp_agc_statuses     Pointer to an array containing pointers to the AGC status of a signal. The items of
 *                                the pointer array are ordered according to ::bio_srd_signal. If no AGC status is
 *                                available for a channel, the corresponding pointer must point to NULL. The number of
 *                                items in the pointer array must be ::BIO_SRD_SIGNAL_NUM. This value is ignored by this
 *                                Bio App as it does not use AGC data.
 * \param[in] p_acc_samples       Pointer to an array containing accelerometer samples. This value is ignored by this
 *                                Bio App as it does not use accelerometer data.
 * \param[in] acc_sample_num      The number of accelerometer samples contained in the array pointed to by
 *                                p_acc_samples. This value is ignored by this Bio App as it does not use accelerometer
 *                                data.
 * \param[out] p_result           The value pointed to by this argument is updated with information whether the Bio App
 *                                is ready for execution. This value must not be NULL.
 *
 * \htmlonly
 *         p_signal_
 *         samples
 *            │               p_i32
 *            └─►┌──────────┐   ┌──►┌──────────────────────┐
 *               │   data ──────┘   │ Main Signal Sample 0 │
 *   Main Signal │ ──────── │       ├──────────────────────┤
 *               │ count: 2 │       │ Main Signal Sample 1 │
 *               └──────────┘       └──────────────────────┘
 * \endhtmlonly
 *
 * \retval ::ERR_SUCCESS    Data accepted.
 * \retval ::ERR_ARGUMENT   Invalid signal sample type or invalid signal count provided.
 * \retval ::ERR_POINTER    At least one pointer argument is NULL which must not be NULL.
 * \retval ::ERR_PERMISSION Not initialized or not in a processing session.
 */
err_code_t bio_srd_set_input(bio_signal_samples_type_t signal_samples_type,
                             const bio_signal_samples_t *p_signal_samples, const agc_status_t *const *pp_agc_statuses,
                             uint8_t signal_num, const vs_acc_data_t *p_acc_samples, uint8_t acc_sample_num,
                             bio_execution_status_t *p_result);

/*!
 * \brief Processes the data previously provided to the Bio App.
 *
 * This function can be called once after ::bio_srd_set_input indicated via the p_result argument that the Bio App
 * is executable. Afterwards, this function can be called again when a subsequent call of ::bio_srd_set_input
 * indicated that the Bio App is executable. The Bio App must be initialized and in a processing session when calling
 * this function.
 *
 * \param[out] p_result The value pointed to by this argument is updated with information whether the Bio App has data
 *                      available for output. This value must not be NULL.
 *
 * \retval ::ERR_SUCCESS    Processing successful.
 * \retval ::ERR_POINTER    p_result is NULL.
 * \retval ::ERR_PERMISSION Not initialized or not in a processing session.
 */
err_code_t bio_srd_execute(bio_output_status_t *p_result);

/*!
 * \brief Copies output data generated by the app to a buffer provided by the caller.
 *
 * This function can be called once after ::bio_srd_execute indicated via the p_result argument that output data is
 * available. Afterwards, this function can be called again when a subsequent call of ::bio_srd_execute indicdated
 * that output data is available. The Bio App must be initialized and in a processing session when calling this
 * function.
 *
 * The size of the output data is sizeof(bio_srd_output_t).
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
err_code_t bio_srd_get_output(void *p_dest, uint16_t *p_size);

/*!
 * \brief Stops the current processing session of the Bio App, allowing it to be reconfigured.
 *
 * This function can only be called when the Bio App is initialized.
 *
 * \retval ::ERR_SUCCESS    Stopping successful.
 * \retval ::ERR_PERMISSION Not initialized.
 */
err_code_t bio_srd_stop(void);

/*!
 * \brief De-initializes the Bio App.
 *
 * \retval ::ERR_SUCCESS De-initialization successful.
 */
err_code_t bio_srd_shutdown(void);

/*!
 * \brief Gets the version of the Bio App.
 *
 * \return Version string.
 */
const char *bio_srd_get_version(void);

#ifdef __cplusplus
}
#endif

/*! @} */

#endif /* __BIO_SRD_H__ */
