/******************************************************************************
 * Copyright © 2022 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

#ifndef __AS7058_OSAL_H__
#define __AS7058_OSAL_H__

/*!
 * \file      as7058_osal_chiplib.h
 * \authors   ARIT
 * \copyright ams OSRAM
 * \addtogroup osal_group OSAL Functions
 *
 * \brief This is the abstraction layer for the chip library.
 *
 * Some functions of the chip library are dependent on the operating system. These functions concern initialization,
 * shutdown, I2C transfers, and interrupt handling. They need to be implemented specifically for each application.
 *
 * @{
 */

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include "error_codes.h"
#include "std_inc.h"

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/
/*!
 * \brief Callback function which will be called if a new interrupt notification is available.
 *
 * This callback function is registered using the function ::as7058_osal_register_int_handler.
 *
 */
typedef err_code_t (*as7058_osal_interrupt_t)(void);

/******************************************************************************
 *                                 FUNCTIONS                                  *
 ******************************************************************************/

/*!
 * \brief Initialization of the hardware abstraction layer.
 *
 * - Initialization of global parameters.
 * - Opens the interface to the sensor.
 *
 * \note This function must be called first!
 *
 * \param[in] p_interface_desc      Can be used to transfer special initialization data like interface description.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_ARGUMENT           Argument content is not supported.
 * \retval ::ERR_COM_INTERFACE      The interface to the sensor is faulty.
 */
err_code_t as7058_osal_initialize(void);

/*!
 * \brief Shutdown of the hardware abstraction layer.
 *
 * - Closes the interface to the sensor
 * - Deactivates the ENABLE-Pin
 *
 * \note This function must be called for cleanup
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_COM_INTERFACE      The interface to the sensor is faulty.
 */
err_code_t as7058_osal_shutdown(void);

/*!
 * \brief Set register values inside the chip.
 *
 * \param[in] address               Register address of the first register to write.
 * \param[in] number                Number of registers to write. The register address is auto-incremented by the
 *                                  sensor.
 * \param[in] p_values              Pointer to register values.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_POINTER            NULL pointer detected.
 * \retval ::ERR_DATA_TRANSFER      Data transfer error, like bus error or timeout.
 * \retval ::ERR_PERMISSION         Library was not initialized using ::as7058_osal_initialize.
 */
err_code_t as7058_osal_write_registers(uint8_t address, uint16_t number, const uint8_t *p_values);

/*!
 * \brief Get register values from the chip.
 *
 * \param[in] address               Register address of the first register to read.
 * \param[in] number                Number of registers to read. The register address is auto-incremented by the sensor.
 * \param[out] p_values             Pointer to buffer where the read register values are written to.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_POINTER            NULL pointer detected.
 * \retval ::ERR_DATA_TRANSFER      Data transfer error, like bus error or timeout.
 * \retval ::ERR_PERMISSION         Library was not initialized using ::as7058_osal_initialize.
 */
err_code_t as7058_osal_read_registers(uint8_t address, uint16_t number, uint8_t *p_values);

/*!
 * \brief Registers and unregisters an interrupt handler.
 *
 * If the function pointer is NULL, then the old callback will be unregistered.
 *
 * \param[in] callback_function     Pointer to callback function or NULL.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_PERMISSION         Library was not initialized using ::as7058_osal_initialize.
 */
err_code_t as7058_osal_register_int_handler(const as7058_osal_interrupt_t callback_function);

#ifdef __cplusplus
}
#endif // __cplusplus

/*! @} */

#endif /* __AS7058_OSAL_H__ */
