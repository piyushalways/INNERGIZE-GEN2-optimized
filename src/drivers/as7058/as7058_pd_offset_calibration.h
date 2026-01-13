/******************************************************************************
 * Copyright © 2022 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

#ifndef __AS7058_PD_OFFSET_CALIBRATION_H__
#define __AS7058_PD_OFFSET_CALIBRATION_H__

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

/*!
 * \file        as7058_pd_offset_calibration.h
 * \authors     PKRN
 * \copyright   ams OSRAM
 * \addtogroup  chiplib_pd_offset_calibration_group PD Offset Calibration
 *
 * \brief Implements the special measurement mode for photodiode offset current calibration.
 *
 * @{
 */

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include "as7058_typedefs.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

/******************************************************************************
 *                                 FUNCTIONS                                  *
 ******************************************************************************/

/*!
 * \brief Initializes the AS7058 PD offset calibration module.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 */
err_code_t as7058_pd_offset_calibration_initialize(void);

/*!
 * \brief Configures the AS7058 PD offset calibration module.
 *
 * \param[in] p_config              Pointer to configuration structure.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_ARGUMENT           Given arguments are not valid.
 * \retval ::ERR_POINTER            Pointer is invalid.
 * \retval ::ERR_PERMISSION         Module is not initialized or in measurement mode.
 */
err_code_t as7058_pd_offset_calibration_configure(const as7058_pd_offset_calibration_config_t *p_config);

/*!
 * \brief Starts the calibration measurements.
 *
 * \param[in] meas_config           Global measurement configuration of the sensor. Needed to extract the FIFO mapping.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_ARGUMENT           Given arguments are not valid.
 * \retval ::ERR_SENSOR_CONFIG      Sensor configuration is not suitable for PD offset calibration.
 * \retval ::ERR_PERMISSION         Module is not configured or in measurement mode.
 */
err_code_t as7058_pd_offset_calibration_start(as7058_meas_config_t meas_config);

/*!
 * \brief Stops the calibration measurements and resets all modified sensor settings.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_PERMISSION         Module is not initialized.
 */
err_code_t as7058_pd_offset_calibration_stop(void);

/*!
 * \brief Handles data acquired during calibration measurement and progresses the calibration process.
 *
 * \param[in] p_fifo_data           Buffer to FIFO data from the sensor.
 * \param[in] fifo_data_size        Size of the FIFO data.
 * \param[out] pp_result            Is updated to point to the calibration result when the calibration is completed.
 *
 * \retval ::ERR_SUCCESS            Calibration is completed and pp_result is updated to point to the calibration
 *                                  results.
 * \retval ::ERR_NO_DATA            Calibration is not finished yet or calibration is finished and calibration results
 *                                  have already been provided.
 * \retval ::ERR_POINTER            Pointer is invalid.
 * \retval ::ERR_PERMISSION         Module is not in measurement mode.
 */
err_code_t as7058_pd_offset_calibration_process(uint8_t *p_fifo_data, uint16_t fifo_data_size,
                                                const as7058_pd_offset_calibration_result_t **const pp_result);

/*!
 * \brief De-initializes the AS7058 PD offset calibration module.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 */
err_code_t as7058_pd_offset_calibration_shutdown(void);

#ifdef __cplusplus
}
#endif // __cplusplus

/*! @} */

#endif /* __AS7058_PD_OFFSET_CALIBRATION_H__ */
