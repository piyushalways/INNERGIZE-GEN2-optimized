/******************************************************************************
 * Copyright © 2022 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

#ifndef __AS7058_CHIP_LIB_H__
#define __AS7058_CHIP_LIB_H__

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

/*!
 * \file        as7058_chiplib.h
 * \authors     ARIT
 * \copyright   ams OSRAM
 * \addtogroup  chiplib_group ChipLib Functions
 *
 * \brief This is the chip library for ams vital signs chip AS7058.
 *
 * @{
 */

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include "agc_typedefs.h"
#include "as7058_typedefs.h"
#include "error_codes.h"
#include "std_inc.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

/******************************************************************************
 *                                 FUNCTIONS                                  *
 ******************************************************************************/

/*!
 * \brief Initializes the library and the device.
 *
 * Following tasks will be done here:
 * - Initialize hardware abstraction layer.
 * - Reset chip.
 *
 * \note This function must be called at first, otherwise all other functions return with error code.
 *
 * \param[in] p_normal_callback     Pointer to normal callback function, see as7058_callback_t.
 * \param[in] p_special_callback    Pointer to special callback function, see ::as7058_callback_special_measurement_t.
 *                                  Can be NULL if no special measurement is needed.
 * \param[in] p_cb_param            Optional pointer to an application parameter, which will be transmitted with every
 *                                  callback.
 * \param[in] p_interface_descr     Chiplib forwards this interface description to as7058_osal_initialize.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_ARGUMENT           An argument is invalid.
 * \retval ::ERR_IDENTIFICATION     The specified sensor was not found.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 */
err_code_t as7058_initialize(const as7058_callback_t p_normal_callback,
                             const as7058_callback_special_measurement_t p_special_callback, const void *p_cb_param,
                             const char *p_interface_descr);

/*!
 * \brief Stops all internal actions and power down the device.
 *
 * Following tasks will be done here:
 * - Stops measurement, if running.
 * - Power down the sensor device.
 * - Shutdown the hardware abstraction layer.
 * - Block calling of all other functions, but initialize.
 *
 * \retval ::ERR_SUCCESS        Function returns without error.
 * \retval ::ERR_DATA_TRANSFER  Error during communication with sensor.
 */
err_code_t as7058_shutdown(void);

/*!
 * \brief Write a register group.
 *
 * This function configures the sensor by directly writing values to a group of sensor registers.
 *
 * \param[in] id                    Identification number of the register group, see ::as7058_reg_group_ids.
 * \param[in] p_data                Pointer to the register data, like ::as7058_reg_group_led_t.
 * \param[in] size                  Sets the size of register data in bytes.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_PERMISSION         Access to the library is blocked, call ::as7058_initialize first.
 * \retval ::ERR_ARGUMENT           Register group id is not supported.
 * \retval ::ERR_POINTER            Detected NULL pointer for p_data.
 * \retval ::ERR_SIZE               Size of the data buffer is wrong.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 */
err_code_t as7058_set_reg_group(as7058_reg_group_ids_t id, const uint8_t *p_data, uint8_t size);

/*!
 * \brief Read a register group.
 *
 * Reads the actual register data into a register group structure.
 *
 * \param[in] id                    Identification number of the register group, see ::as7058_reg_group_ids.
 * \param[out] p_data               Pointer, where the data of the register group can be saved.
 * \param[inout] p_size             IN: Maximum buffer size, OUT: Size in byte of the register group data
 *                                  The maximum size is defined in ::AS7058_MAX_GROUP_SIZE.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_PERMISSION         Access to the library is blocked, call ::as7058_initialize at first.
 * \retval ::ERR_ARGUMENT           Register group id is not supported.
 * \retval ::ERR_POINTER            Detected NULL pointer on arguments.
 * \retval ::ERR_SIZE               Size of the data buffer is wrong.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 */
err_code_t as7058_get_reg_group(as7058_reg_group_ids_t id, uint8_t *p_data, uint8_t *p_size);

/*!
 * \brief Write register.
 *
 * This function sets the value of a single sensor register.
 *
 * \param[in] reg_addr              Register address of the sensor, see ::as7058_reg_addresses.
 * \param[in] reg_val               New register value, which will be written to the register address.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_PERMISSION         Access to the library is blocked, call ::as7058_initialize at first.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 */
err_code_t as7058_write_register(as7058_reg_addresses_t reg_addr, uint8_t reg_val);

/*!
 * \brief Read register.
 *
 * This function gets the value of a single sensor register.
 *
 * \param[in] reg_addr              Register address of the sensor, see ::as7058_reg_addresses.
 * \param[out] p_reg_val            Actual register value, which was read from the register address.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_PERMISSION         Access to the library is blocked, call ::as7058_initialize at first.
 * \retval ::ERR_POINTER            Detected NULL pointer for p_reg_val.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 */
err_code_t as7058_read_register(as7058_reg_addresses_t reg_addr, uint8_t *p_reg_val);

/*!
 * \brief Read the actual measurement configuration, which was set by the register groups.
 *
 * \note The measurement configuration can be changed after set of new register blocks or writting to single registers.
 * Therefore, read it back after finished configuration to get the actual values.
 *
 * \param[out] p_meas_config   Actual measurement configuration, See ::as7058_meas_config_t
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_PERMISSION         Access to the library is blocked, call ::as7058_initialize at first.
 * \retval ::ERR_POINTER            Detected NULL pointer for p_meas_config.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 */
err_code_t as7058_get_measurement_config(as7058_meas_config_t *p_meas_config);

/*!
 * \brief Sets the configuration for auto-gain-control (AGC)
 *
 * \param[in] p_agc_configs         Pointer to store AGC configuration information for up to 4 channels.
 * \param[in] agc_config_num        Number of given channels.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_ARGUMENT           At least one parameter is wrong.
 * \retval ::ERR_PERMISSION         Access to the library is blocked, call ::as7058_initialize at first.
 * \retval ::ERR_POINTER            Detected NULL pointer for p_agc_config.
 */
err_code_t as7058_set_agc_config(const agc_configuration_t *p_agc_configs, uint8_t agc_config_num);

/*!
 * \brief Gets the configuration for auto-gain-control (AGC)
 *
 * \param[out] p_agc_configs        Pointer to store AGC configuration for activated channels.
 * \param[inout] p_agc_config_num   Number of channels. IN: Defines how how many AGC channel configurations can be saved
 *                                  inside p_agc_configs. OUT: number of enabled AGC channels.
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_PERMISSION         Access to the library is blocked, call ::as7058_initialize at first.
 * \retval ::ERR_POINTER            Detected NULL pointer for p_agc_config.
 */
err_code_t as7058_get_agc_config(agc_configuration_t *p_agc_configs, uint8_t *p_agc_config_num);

/*!
 * \brief Starts a measurement.
 *
 * \param[in] mode                  Measurement mode, see ::as7058_meas_mode.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_ARGUMENT           Invalid measurement mode provided.
 * \retval ::ERR_PERMISSION         Access to the library is blocked, call ::as7058_initialize at first.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 * \retval ::ERR_CONFIG             No sub-sample is enabled, AOC and AGC are enabled in parallel, or sensor is not
 *                                  properly configured for impedance scaling.
 */
err_code_t as7058_start_measurement(as7058_meas_mode_t mode);

/*!
 * \brief Stops a measurement.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_PERMISSION         Access to the library is blocked, call ::as7058_initialize at first.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 */
err_code_t as7058_stop_measurement(void);

/*!
 * \brief Requests the version information.
 *
 * \return Version string.
 */
const char *as7058_get_version(void);

/*!
 * \brief Configures a special measurement mode.
 *
 * Before starting a measurement of mode ::AS7058_MEAS_MODE_SPECIAL_BIOZ or ::AS7058_MEAS_MODE_SPECIAL_SCALING_EDA, the
 * corresponding measurement mode needs to be configured.
 *
 * \param[in] mode                  Measurement mode. See ::as7058_meas_mode.
 * \param[in] p_config              Pointer to the configuration structure for the special measurement mode.
 *                                  See ::as7058_eda_scaling_config_t and ::as7058_bioz_meas_config_t.
 * \param[in] size                  Size of the configuration structure.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_PERMISSION         Access to this function is blocked. Depending on the current state of the library,
 *                                  call ::as7058_initialize or ::as7058_stop_measurement.
 * \retval ::ERR_ARGUMENT           Provided configuration contains an invalid value.
 * \retval ::ERR_POINTER            Detected NULL pointer for p_config.
 * \retval ::ERR_SIZE               The size of the configuration does not fit to the mode.
 * \retval ::ERR_CONFIG             Special measurement callback was not set when ::as7058_initialize was called.
 */
err_code_t as7058_set_special_measurement_config(as7058_meas_mode_t mode, const void *p_config, uint16_t size);

#ifdef __cplusplus
}
#endif // __cplusplus

/*! @} */

#endif /* __AS7058_CHIP_LIB_H__ */
