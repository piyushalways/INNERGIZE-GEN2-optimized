/******************************************************************************
 * Copyright © 2022 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

#ifndef __AS7058_APP_MANAGER_H__
#define __AS7058_APP_MANAGER_H__

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

/*!
 * \file       as7058_app_manager.h
 * \authors    PKRN
 * \copyright  ams OSRAM
 * \addtogroup AS7058_APPMGR Application Manager
 *
 * \brief The AS7058 Application Manager routes measurement data to Vital Signs Applications and provides a unified
 * interface for application configuration and obtaining resulting output data.
 *
 * @{
 */

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include <stdint.h>

#include "as7058_app_manager_typedefs.h"
#include "error_codes.h"
#include "vital_signs_accelerometer.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

#ifndef AS7058_APPMGR_FUNC_DECL
/*! Preprocessor macro that is placed in front of every public function declaration with external linkage. By default
 *  this macro is defined to expand to nothing, but it can be defined externally. Example use cases include setting
 *  keywords. */
#define AS7058_APPMGR_FUNC_DECL
#endif

/******************************************************************************
 *                                 FUNCTIONS                                  *
 ******************************************************************************/

/*!
 * \brief Initializes the Application Manager.
 *
 * The Application Manager transitions to Configuration state after initialization.
 *
 * \retval ::ERR_SUCCESS Initialized successfully.
 */
AS7058_APPMGR_FUNC_DECL err_code_t as7058_appmgr_initialize(void);

/*!
 * \brief Sets the enabled Vital Signs Applications.
 *
 * This function can only be called when the Application Manager is in Configuration state.
 *
 * \param[in] enabled_apps Flags of enabled Vital Signs Applications, see ::as7058_appmgr_app_flag. A Vital Signs
 *                         Application is enabled when the corresponding bit is set and disabled when the bit is not
 *                         set.
 *
 * \retval ::ERR_SUCCESS       Updated successfully.
 * \retval ::ERR_ARGUMENT      Invalid selection of applications.
 * \retval ::ERR_NOT_SUPPORTED At least one selected application was disabled at compile-time.
 * \retval ::ERR_PERMISSION    Invalid state.
 */
AS7058_APPMGR_FUNC_DECL err_code_t as7058_appmgr_enable_apps(uint32_t enabled_apps);

/*!
 * \brief Sets the signal routing for a Vital Signs Application.
 *
 * Each Vital Signs Application has an ordered list of signals assigned, which can be found in \ref AS7058_APPMGR_APPS.
 * When ::as7058_appmgr_set_input is called, the Application Manager extracts the samples of each signal of each enabled
 * Vital Signs Application. In order to extract samples from the provided sensor FIFO data, the Application Manager
 * requires a mapping between sensor channels and Vital Signs Application signals. This mapping is provided to the
 * Application Manager for each Vital Signs Application using this function.
 *
 * No signal routing is required for ::AS7058_APPMGR_APP_ID_RAW.
 *
 * This function can only be called when the Application Manager is in Configuration state.
 *
 * \param[in] app          Identifier of the Vital Signs Application for which the signal routing shall be set.
 * \param[in] p_channels   Pointer to the start of an array containing the channel identifiers used for each signal of
 *                         the given Vital Signs Application, in the order specified in the subsections of \ref
 *                         AS7058_APPMGR_APPS. Can be NULL if channels_num is zero.
 * \param[in] channels_num Number of items contained in the p_channels array. This number must be equal to the signal
 *                         count of the given Vital Signs Application, which can be found in the subsections of \ref
 *                         AS7058_APPMGR_APPS.
 *
 * \retval ::ERR_SUCCESS       Updated successfully.
 * \retval ::ERR_ARGUMENT      Invalid application identifier or invalid channel identifiers.
 * \retval ::ERR_NOT_SUPPORTED Application was disabled at compile-time.
 * \retval ::ERR_SIZE          Mismatching number of channels.
 * \retval ::ERR_POINTER       Invalid pointer argument value.
 * \retval ::ERR_PERMISSION    Invalid state.
 */
AS7058_APPMGR_FUNC_DECL err_code_t as7058_appmgr_set_signal_routing(as7058_appmgr_app_id_t app,
                                                                    const as7058_sub_sample_ids_t *p_channels,
                                                                    uint8_t channels_num);

/*!
 * \brief Configures a Vital Signs Application.
 *
 * This function can only be called when the Application Manager is in Configuration state.
 *
 * \param[in] app      Identifier of the Vital Signs Application to configure.
 * \param[in] p_config Pointer to the configuration structure for the given Vital Signs Application, which can found in
 *                     the subsections of \ref AS7058_APPMGR_APPS.
 * \param[in] size     Size of the configuration structure.
 *
 * \retval ::ERR_SUCCESS       Updated successfully.
 * \retval ::ERR_ARGUMENT      Invalid application identifier or mismatching configuration structure size.
 * \retval ::ERR_NOT_SUPPORTED Application was disabled at compile-time.
 * \retval ::ERR_POINTER       Invalid pointer argument value.
 * \retval ::ERR_PERMISSION    Invalid state.
 */
AS7058_APPMGR_FUNC_DECL err_code_t as7058_appmgr_configure_app(as7058_appmgr_app_id_t app, const void *p_config,
                                                               uint8_t size);

/*!
 * \brief Sets which signal sample preprocessing features are enabled for the given app.
 *
 * This function can only be called when the Application Manager is in Configuration state.
 *
 * \param[in] app      Identifier of the Vital Signs Application to configure.
 * \param[in] flags    Flags of enabled preprocessing features, see ::as7058_appmgr_preprocessing_flag. A preprocessing
 *                     feature is enabled when the corresponding bit is set and disabled when the bit is not set.
 *
 * \retval ::ERR_SUCCESS       Updated successfully.
 * \retval ::ERR_ARGUMENT      Invalid application identifier, application does not support signal sample preprocessing,
 *                             or invalid flags.
 * \retval ::ERR_NOT_SUPPORTED Application was disabled at compile-time.
 * \retval ::ERR_PERMISSION    Invalid state.
 */
AS7058_APPMGR_FUNC_DECL err_code_t as7058_appmgr_enable_preprocessing(as7058_appmgr_app_id_t app, uint32_t flags);

/*!
 * \brief Configures a signal sample preprocessing feature.
 *
 * There can only be one configuration per signal sample preprocessing feature. The configuration of a preprocessing
 * feature applies to all applications that have the preprocessing feature enabled.
 *
 * This function can only be called when the Application Manager is in Configuration state.
 *
 * \param[in] preprocessing Identifier of the signal sample preprocessing feature to configure.
 * \param[in] p_config      Pointer to the configuration structure for the given signal sample preprocessing feature,
 *                          which can found in the subsections of \ref AS7058_APPMGR_PREPROCESSING.
 * \param[in] size          Size of the configuration structure.
 *
 * \retval ::ERR_SUCCESS    Updated successfully.
 * \retval ::ERR_ARGUMENT   Invalid preprocessing feature identifier or invalid configuration structure contents.
 * \retval ::ERR_POINTER    Invalid pointer argument value.
 * \retval ::ERR_SIZE       Invalid size of the configuration structure.
 * \retval ::ERR_PERMISSION Invalid state.
 */
AS7058_APPMGR_FUNC_DECL err_code_t as7058_appmgr_configure_preprocessing(as7058_appmgr_preprocessing_id_t preprocessing,
                                                                         const void *p_config, uint16_t size);

/*!
 * \brief Starts processing.
 *
 * This function can only be called when the Application Manager is in Configuration state. The Application Manager
 * transitions to Processing state when this function executes successfully.
 *
 * \param[in] measurement_config   Measurement configuration used to acquire the data that will be provided to the
 *                                 Application Manager. This value is typically obtained from the Chip Library.
 * \param[in] acc_sample_period_us Sample period of the accelerometer in microseconds.
 *
 * \retval ::ERR_SUCCESS    Updated successfully.
 * \retval ::ERR_CONFIG     Measurement or accelerometer configuration invalid or incompatible with application
 *                          configurations, or preprocessing feature enabled but not configured.
 * \retval ::ERR_PERMISSION Invalid state.
 */
AS7058_APPMGR_FUNC_DECL err_code_t as7058_appmgr_start_processing(as7058_meas_config_t measurement_config,
                                                                  uint32_t acc_sample_period_us);

/*!
 * \brief Provides measurement data of the regular measurement mode to the Application Manager.
 *
 * This function can only be called when the Application Manager is in Processing state.
 *
 * \param[in]  p_fifo_data           Pointer to the start of the sensor FIFO data. This data is typically obtained from
 *                                   the Chip Library. Can be NULL if fifo_data_size is zero.
 * \param[in]  fifo_data_size        Size of the FIFO data.
 * \param[in]  status_events         Chip status events, containing information regarding interrupts that occurred on
 *                                   the chip. This value is typically obtained from the Chip Library.
 * \param[in]  p_agc_statuses        Pointer to the start of an array containing Automatic Gain Control (AGC) status
 *                                   information for each channel with enabled AGC. The required order of the status
 *                                   information items is determined by the agc_channels array of the
 *                                   as7058_meas_config_t structure passed to ::as7058_appmgr_start_processing. For
 *                                   example, if the agc_channels array contains AS7058_SUB_SAMPLE_ID_PPG1_SUB1 at index
 *                                   0, this array must contain the AGC status information for
 *                                   AS7058_SUB_SAMPLE_ID_PPG1_SUB1 at index 0. AGC status information must always be
 *                                   provided for each channel with enabled AGC. This pointer is typically obtained from
 *                                   the Chip Library. Can be NULL if agc_statuses_num is zero.
 * \param[in]  agc_statuses_num      Number of items in the array containing AGC status information. Can be zero if
 *                                   fifo_data_size is zero.
 * \param[in]  p_acc_samples         Pointer to the start of an array containing accelerometer samples. Can be NULL if
 *                                   acc_samples_num is zero.
 * \param[in]  acc_samples_num       Number of accelerometer samples.
 * \param[out] p_ready_for_execution Set to ::TRUE when at least one Vital Signs Applications indicated that is is ready
 *                                   for execution, ::FALSE otherwise.
 *
 * \retval ::ERR_SUCCESS    Measurement data accepted.
 * \retval ::ERR_SIZE       Too many samples in the FIFO data or invalid number of AGC status information items.
 * \retval ::ERR_OVERFLOW   Sample counts are too different to be handled.
 * \retval ::ERR_DATA       Data inconsistency detected.
 * \retval ::ERR_POINTER    Invalid pointer argument value.
 * \retval ::ERR_PERMISSION Invalid state.
 */
AS7058_APPMGR_FUNC_DECL err_code_t as7058_appmgr_set_input(const uint8_t *p_fifo_data, uint16_t fifo_data_size,
                                                           as7058_status_events_t status_events,
                                                           const agc_status_t *p_agc_statuses, uint8_t agc_statuses_num,
                                                           const vs_acc_data_t *p_acc_samples, uint16_t acc_samples_num,
                                                           uint8_t *p_ready_for_execution);

/*!
 * \brief Provides measurement data of special measurement modes to the Application Manager.
 *
 * It can only be called when the Application Manager is in Processing state.
 *
 * \param[in]  mode                  Identifier of the special measurement mode.
 * \param[in]  p_input               Pointer to the measurement data of the special measurement mode.
 * \param[out] p_ready_for_execution Set to ::TRUE when at least one Vital Signs Applications indicated that is is ready
 *                                   for execution, ::FALSE otherwise.
 *
 * \retval ::ERR_SUCCESS    Measurement data accepted.
 * \retval ::ERR_ARGUMENT   Invalid measurement mode identifier.
 * \retval ::ERR_POINTER    Invalid pointer argument value.
 * \retval ::ERR_PERMISSION Invalid state.
 */
AS7058_APPMGR_FUNC_DECL err_code_t as7058_appmgr_set_special_measurement_input(
    as7058_meas_mode_t mode, const as7058_special_measurement_result_t *p_input, uint8_t *p_ready_for_execution);

/*!
 * \brief Informs the Application Manager that an external event occurred.
 *
 * The function counts how many times it has been called and provides the count to applications on the next invocation
 * of ::as7058_appmgr_set_input. This function can only be called when the Application Manager is in Processing state.
 *
 * \retval ::ERR_SUCCESS    Information accepted.
 * \retval ::ERR_OVERFLOW   Too many events occurred since last ::as7058_appmgr_set_input call.
 * \retval ::ERR_PERMISSION Invalid state.
 */
AS7058_APPMGR_FUNC_DECL err_code_t as7058_appmgr_set_ext_event_occurred(void);

/*!
 * \brief Executes enabled Vital Signs Applications.
 *
 * This function can only be called when the Application Manager is in Processing state.
 *
 * \param[out] p_data_available Flags of Vital Signs Applications that indicated that their execution generated output
 *                              data, see ::as7058_appmgr_app_flag. An app has output data available when the
 *                              corresponding bit is set. The value pointed to by this argument is cleared before bits
 *                              are set.
 *
 * \retval ::ERR_SUCCESS    Execution successful.
 * \retval ::ERR_POINTER    Invalid pointer argument value.
 * \retval ::ERR_PERMISSION Invalid state.
 */
AS7058_APPMGR_FUNC_DECL err_code_t as7058_appmgr_execute(uint32_t *p_data_available);

/*!
 * \brief Writes output of a Vital Signs Application to a buffer provided by the caller.
 *
 * This function can only be called when the Application Manager is in Processing state.
 *
 * \param[in]    app    Identifier of the Vital Signs Application to get output from.
 * \param[out]   p_dest Pointer to the buffer where the output shall be written to. The output is application-specific
 *                      and is described in the subsections of \ref AS7058_APPMGR_APPS.
 * \param[inout] p_size Pointer to the amount of memory allocated for the output data. The function updates the value
 *                      pointed to with the actual size of the written output data.
 *
 * \retval ::ERR_SUCCESS       Output data write successful.
 * \retval ::ERR_ARGUMENT      Invalid app identifier or disabled application.
 * \retval ::ERR_NOT_SUPPORTED Application was disabled at compile-time.
 * \retval ::ERR_POINTER       Invalid pointer argument value.
 * \retval ::ERR_PERMISSION    Invalid state.
 */
AS7058_APPMGR_FUNC_DECL err_code_t as7058_appmgr_get_output(as7058_appmgr_app_id_t app, void *p_dest, uint16_t *p_size);

/*!
 * \brief Stops processing.
 *
 * This function can only be called when the Application Manager is not in Uninitialized state.
 *
 * \retval ::ERR_SUCCESS    Stop successful.
 * \retval ::ERR_PERMISSION Invalid state.
 */
AS7058_APPMGR_FUNC_DECL err_code_t as7058_appmgr_stop_processing(void);

/*!
 * \brief De-initializes the Application Manager.
 *
 * \retval ::ERR_SUCCESS De-initialization successful.
 */
AS7058_APPMGR_FUNC_DECL err_code_t as7058_appmgr_shutdown(void);

/*!
 * \brief Gets the version of the Application Manager.
 *
 * \return Version string.
 */
AS7058_APPMGR_FUNC_DECL const char *as7058_appmgr_get_version(void);

#ifdef __cplusplus
}
#endif // __cplusplus

/*! @} */

#endif /* __AS7058_APP_MANAGER_H__ */
