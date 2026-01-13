/******************************************************************************
 * Copyright © 2022 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

#ifndef __BIO_SPO2_A0_H__
#define __BIO_SPO2_A0_H__

#ifdef __cplusplus
extern "C" {
#endif

/*!
 * \file       bio_spo2_a0.h
 * \authors    ARIT, PKRN
 * \copyright  ams OSRAM
 * \addtogroup bio_spo2_a0_group
 *
 * \brief This module provides an interface to the ams OSRAM SpO2 algorithm which conforms to the Generic Bio App
 *        Handler Interface Specification.
 *
 * @{
 */

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include "bio_spo2_a0_typedefs.h"

#include "agc_typedefs.h"
#include "vital_signs_accelerometer.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

#ifndef BIO_SPO2_A0_FUNC_DECL
/*! Preprocessor macro that is placed in front of every public function declaration with external linkage. It expands to
 *  nothing. */
#define BIO_SPO2_A0_FUNC_DECL
#endif

#ifndef SPO2_APP_INPUT_BUF_NUM
/*!
 * \brief The internal buffer is sized to support a sampling frequency of 200 Hz, assuming that ::bio_spo2_a0_execute is
 *        called at least every second when the Bio App is executable.
 */
#define SPO2_APP_INPUT_BUF_NUM 200
#endif

/******************************************************************************
 *                                 FUNCTIONS                                  *
 ******************************************************************************/

/*!
 * \brief Initializes the Bio App.
 *
 * \retval ::ERR_SUCCESS Initialized successfully.
 */
BIO_SPO2_A0_FUNC_DECL err_code_t bio_spo2_a0_initialize(void);

/*!
 * \brief Configures the Bio App.
 *
 * This function can only be called when the Bio App is initialized and not in a processing session.
 *
 * \param[in] p_config Pointer to the configuration structure, see ::bio_spo2_a0_configuration_t. It must not be NULL.
 * \param[in] size     Size of the configuration structure. It must be `sizeof(bio_spo2_a0_configuration_t)`.
 *
 * \retval ::ERR_SUCCESS    Updated successfully.
 * \retval ::ERR_POINTER    Invalid pointer to configuration structure.
 * \retval ::ERR_SIZE       Size does not match expected size.
 * \retval ::ERR_PERMISSION Not initialized.
 */
BIO_SPO2_A0_FUNC_DECL err_code_t bio_spo2_a0_configure(const void *p_config, uint8_t size);

/*!
 * \brief Copies the current configuration of the Bio App to the provided buffer.
 *
 * This function can only be called when the Bio App is initialized and not in a processing session.
 *
 * The size of the configuration is `sizeof(bio_spo2_a0_configuration_t)`.
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
BIO_SPO2_A0_FUNC_DECL err_code_t bio_spo2_a0_get_configuration(void *p_dest, uint8_t *p_size);

/*!
 * \brief Provides the sensor signals and accelerometer sample periods to the Bio App and starts a processing session.
 *
 * This function can only be called when the Bio App is initialized.
 *
 * \param[in] p_signal_sample_periods_us Pointer to an array containing the sample periods of each signal in
 *                                       microseconds. There must be ::BIO_SPO2_A0_SIGNAL_NUM items in the array,
 *                                       ordered according to ::bio_spo2_a0_signal. This value must not be NULL. This
 *                                       app requires that all signals are samples with an identical non-zero sample
 *                                       period.
 * \param[in] signal_num                 The number of sensor signals provided to the Bio App. It must be
 *                                       ::BIO_SPO2_A0_SIGNAL_NUM.
 * \param[in] acc_sample_period_us       The sample period of the accelerometer in microseconds. This value is ignored
 *                                       by this Bio App as it does not use accelerometer data.
 *
 * \htmlonly
 *     p_signal_sample_
 *     _periods_us
 *          │
 *          └─►┌───────────────────────┐
 *     PPG Red │ PPG Red Sample Period │
 *             ├───────────────────────┤
 *      PPG IR │ PPG IR Sample Period  │
 *             ├───────────────────────┤
 *     Ambient │ Ambient Sample Period │
 *             └───────────────────────┘
 * \endhtmlonly
 *
 * \retval ::ERR_SUCCESS    Updated successfully.
 * \retval ::ERR_ARGUMENT   Invalid sample periods or invalid signal count provided.
 * \retval ::ERR_POINTER    p_signal_sample_periods_us is NULL.
 * \retval ::ERR_PERMISSION Not initialized.
 */
BIO_SPO2_A0_FUNC_DECL err_code_t bio_spo2_a0_start(const uint32_t *p_signal_sample_periods_us, uint8_t signal_num,
                                                   uint32_t acc_sample_period_us);

/*!
 * \brief Provides measurement data to the Bio App.
 *
 * This function can only be called when the Bio App is initialized and in a processing session.
 *
 * \param[in] signal_samples_type The data type of sensor signals. It must be ::BIO_SPO2_A0_SIGNAL_DATA_TYPE.
 * \param[in] signal_num          The number of sensor signals provided to the Bio App. It must be
 *                                ::BIO_SPO2_A0_SIGNAL_NUM.
 * \param[in] p_signal_samples    Pointer to an array of ::bio_signal_samples_t. There must be ::BIO_SPO2_A0_SIGNAL_NUM
 *                                items in the array, ordered according to ::bio_spo2_a0_signal. For each signal, the
 *                                same number of samples needs to be provided.
 * \param[in] pp_agc_statuses     Pointer to an array containing pointers to the AGC status of a signal. The items of
 *                                the pointer array are ordered according to ::bio_spo2_a0_signal. If no AGC status is
 *                                available for a channel, the corresponding pointer must point to NULL. The number of
 *                                items in the pointer array must be ::BIO_SPO2_A0_SIGNAL_NUM.
 * \param[in] p_acc_samples       Pointer to an array containing accelerometer samples. This value is ignored by this
 *                                Bio App as it does not use accelerometer data.
 * \param[in] acc_sample_num      The number of accelerometer samples contained in the array pointed to by
 *                                p_acc_samples. This value is ignored by this Bio App as it does not use accelerometer
 *                                data.
 * \param[out] p_result           The value pointed to by this argument is updated with information whether the Bio App
 *                                is ready for execution. This value must not be NULL.
 *
 * \htmlonly
 *       p_signal_                                          pp_agc_
 *       samples                                            statuses
 *          │               p_u16                              │
 *          └─►┌──────────┐   ┌──►┌──────────────────┐         └─►┌──────────┐   ┌──►┌────────────┐
 *             │   data ──────┘   │ PPG Red Sample 0 │    PPG Red │          ├───┘   │ PPG Red    │
 *     PPG Red │ ──────── │       ├──────────────────┤            ├──────────┤       │ AGC Status │
 *             │ count: 2 │       │ PPG Red Sample 1 │     PPG IR │          ├───┐   └────────────┘
 *             ├──────────┤ p_u16 └──────────────────┘            ├──────────┤   └──►┌────────────┐
 *             │   data ─────────►┌──────────────────┐    Ambient │   NULL   │       │ PPG IR     │
 *      PPG IR │ ──────── │       │ PPG IR Sample 0  │            └──────────┘       │ AGC Status │
 *             │ count: 2 │       ├──────────────────┤                               └────────────┘
 *             ├──────────┤ p_u16 │ PPG IR Sample 1  │
 *             │   data ──────┐   └──────────────────┘
 *     Ambient │ ──────── │   └──►┌──────────────────┐
 *             │ count: 2 │       │ Ambient Sample 0 │
 *             └──────────┘       ├──────────────────┤
 *                                │ Ambient Sample 1 │
 *                                └──────────────────┘
 * \endhtmlonly
 *
 * \retval ::ERR_SUCCESS    Data accepted.
 * \retval ::ERR_ARGUMENT   Invalid signal sample type or invalid signal count provided.
 * \retval ::ERR_POINTER    At least one pointer argument is NULL which must not be NULL.
 * \retval ::ERR_OVERFLOW   Cannot store the provided data due to exhausted internal buffers.
 * \retval ::ERR_PERMISSION Not initialized or not in a processing session.
 */
BIO_SPO2_A0_FUNC_DECL err_code_t bio_spo2_a0_set_input(bio_signal_samples_type_t signal_samples_type,
                                                       const bio_signal_samples_t *p_signal_samples,
                                                       const agc_status_t *const *pp_agc_statuses, uint8_t signal_num,
                                                       const vs_acc_data_t *p_acc_samples, uint8_t acc_sample_num,
                                                       bio_execution_status_t *p_result);

/*!
 * \brief Processes the data previously provided to the Bio App.
 *
 * This function can be called once after ::bio_spo2_a0_set_input indicated via the p_result argument that the Bio App
 * is executable. Afterwards, this function can be called again when a subsequent call of ::bio_spo2_a0_set_input
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
BIO_SPO2_A0_FUNC_DECL err_code_t bio_spo2_a0_execute(bio_output_status_t *p_result);

/*!
 * \brief Copies output data generated by the app to a buffer provided by the caller.
 *
 * This function can be called once after ::bio_spo2_a0_execute indicated via the p_result argument that output data is
 * available. Afterwards, this function can be called again when a subsequent call of ::bio_spo2_a0_execute indicdated
 * that output data is available. The Bio App must be initialized and in a processing session when calling this
 * function.
 *
 * The size of the output data is sizeof(bio_spo2_a0_output_t).
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
BIO_SPO2_A0_FUNC_DECL err_code_t bio_spo2_a0_get_output(void *p_dest, uint16_t *p_size);

/*!
 * \brief Stops the current processing session of the Bio App, allowing it to be reconfigured.
 *
 * This function can only be called when the Bio App is initialized and in a processing session.
 *
 * \retval ::ERR_SUCCESS    Stopping successful.
 * \retval ::ERR_PERMISSION Not initialized or not in a processing session.
 */
BIO_SPO2_A0_FUNC_DECL err_code_t bio_spo2_a0_stop(void);

/*!
 * \brief De-initializes the Bio App.
 *
 * \retval ::ERR_SUCCESS De-initialization successful.
 */
BIO_SPO2_A0_FUNC_DECL err_code_t bio_spo2_a0_shutdown(void);

/*!
 * \brief Gets the version of the Bio App.
 *
 * \return Version string.
 */
BIO_SPO2_A0_FUNC_DECL const char *bio_spo2_a0_get_version(void);

#ifdef __cplusplus
}
#endif

/*! @} */

#endif /* __BIO_SPO2_A0_H__ */
