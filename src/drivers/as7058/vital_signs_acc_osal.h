/******************************************************************************
 * Copyright by ams AG                                                        *
 * All rights are reserved.                                                   *
 *                                                                            *
 * IMPORTANT - PLEASE READ CAREFULLY BEFORE COPYING, INSTALLING OR USING      *
 * THE SOFTWARE.                                                              *
 *                                                                            *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS        *
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT          *
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS          *
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT   *
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,      *
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT           *
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,      *
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY      *
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT        *
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE      *
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.       *
 ******************************************************************************/

#ifndef __VITAL_SIGNS_ACC_OSAL_H__
#define __VITAL_SIGNS_ACC_OSAL_H__

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

/*!
 * \file      vital_signs_acc_osal.h
 * \authors   ARIT
 * \copyright ams
 * \addtogroup accelerometer
 *
 * \brief This module describes the hardware dependencies of the accelerometer.
 *
 * The current implementation of the accelerometer requires two hardware dependencies.
 * The first one is the access to the I2C bus where the accelerometer is connected.
 * Initialisation and shutdown of the I2C bus is not part of this module and must be done externally.
 * To get simulated accelerometer data (real accelerometer is not connected) the system needs a timebase. This is the
 * task of the second OSAL function.
 *
 * @{
 */

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include <stdint.h>

#include "error_codes.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

/******************************************************************************
 *                                 FUNCTIONS                                  *
 ******************************************************************************/

/*!
 * \brief Transfers an I2C sequence to a specific i2c address.
 *
 * \param[in] p_config          Optional pointer to hardware-dependent description.
 * \param[in] dev_addr          I2C device address.
 * \param[in] p_send_data       Pointer to send data buffer.
 * \param[in] send_len          Number of bytes to send.
 * \param[out] p_recv_data      Pointer to receive data buffer.
 * \param[in] recv_len          Number of bytes to read.
 *
 * \retval ::ERR_SUCCESS        Function returns without error.
 * \retval ::ERR_I2C            I2C transfer error (e.g. no acknowledge received) occurred.
 * \retval ::ERR_POINTER        NULL pointer detected.
 */
err_code_t vs_acc_osal_transfer_i2c(const char *p_config, uint8_t dev_addr, const uint8_t *p_send_data,
                                    uint16_t send_len, uint8_t *p_recv_data, uint16_t recv_len);

/*!
 * \brief Gets the current millisecond timestamp.
 *
 * \param[in] p_config          Optional pointer to hardware-dependent description.
 * \param[in] p_ms_tick         Pointer where the millisecond timestamp shall be saved.
 *
 * \retval ::ERR_SUCCESS        Function returns without error.
 * \retval ::ERR_POINTER        NULL pointer detected.
 */
err_code_t vs_acc_osal_get_tick(const char *p_config, uint32_t *p_ms_tick);

#ifdef __cplusplus
}
#endif // __cplusplus

/*! @} */

#endif /* __VITAL_SIGNS_ACC_OSAL_H__ */
