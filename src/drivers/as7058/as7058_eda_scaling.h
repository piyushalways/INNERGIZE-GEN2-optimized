/******************************************************************************
 * Copyright © 2022 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

#ifndef __AS7058_EDA_SCALING_H__
#define __AS7058_EDA_SCALING_H__

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

/*!
 * \file        as7058_eda_scaling.h
 * \authors     ARIT
 * \copyright   ams OSRAM
 * \addtogroup  chiplib_group ChipLib Functions
 *
 * \brief Special EDA impedance scaling measurement mode.
 *
 * @{
 */

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

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
 * \brief Initialization of AS7058 EDA scaling module.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 */
err_code_t as7058_eda_scaling_initialize(void);

/*!
 * \brief Configures the module with the needed configuration.
 *
 * \param[in] p_special_config      Pointer to configuration structure.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_ARGUMENT           Given arguments are not valid.
 * \retval ::ERR_POINTER            p_special_config must not be null.
 */
err_code_t as7058_eda_scaling_configure(const as7058_eda_scaling_config_t *p_special_config);

/*!
 * \brief Prepares the measurement.
 *
 * \param[in] meas_config           Global measurement configuration of the sensor. Needed to extract the FIFO mapping.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_ARGUMENT           Given arguments are not valid.
 * \retval ::ERR_CONFIG             Module or sensor is configured incorrectly.
 */
err_code_t as7058_eda_scaling_start(as7058_meas_config_t meas_config);

/*!
 * \brief Stops the calculation and resets all modified sensor settings.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 */
err_code_t as7058_eda_scaling_stop(void);

/*!
 * \brief Processes FIFO data received during EDA scaling. Needs to be called whenever FIFO data becomes available while
 *        EDA scaling is running.
 *
 * \param[in] p_fifo_data           Buffer to FIFO data from the sensor.
 * \param[in] fifo_data_size        Size of the FIFO data.
 * \param[out] pp_scaling_result    Is updated to point to the scaling result when one becomes available.
 *
 * \retval ::ERR_SUCCESS            Scaling result is available.
 * \retval ::ERR_NO_DATA            Scaling result is not available.
 * \retval ::ERR_POINTER            Pointer is invalid.
 * \retval ::ERR_PERMISSION         Scaling has not been started or measurement mode has not been configured.
 */
err_code_t as7058_eda_scaling_process(const uint8_t *p_fifo_data, uint16_t fifo_data_size,
                                      const as7058_eda_scaling_result_t **pp_scaling_result);

/*!
 * \brief Shutdown of AS7058 EDA scaling module.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 */
err_code_t as7058_eda_scaling_shutdown(void);

#ifdef __cplusplus
}
#endif // __cplusplus

/*! @} */

#endif /* __AS7058_EDA_SCALING_H__ */
