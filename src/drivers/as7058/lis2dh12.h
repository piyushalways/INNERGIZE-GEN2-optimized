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

#ifndef __LIS2DH12_H__
#define __LIS2DH12_H__

/*!
 * \file        lis2dh12.h
 * \authors     SSHW
 * \copyright   ams
 * \addtogroup  i2c_group
 *
 * \brief I2C driver for accelerometer sensor lis2dh12
 *
 * This driver depends on the LIS2DH12 standard C driver from ST. The necessary i2c
 * transfer function will be commited on initialization via callback function.
 *
 * \see dependency https://github.com/STMicroelectronics/STMems_Standard_C_drivers/tree/master/lis2dh12_STdC
 * \see datasheet https://www.st.com/resource/en/datasheet/lis2dh12.pdf
 *
 *  @{
 */

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include <stdint.h>

#include "error_codes.h"
#include "lis2dh12_reg.h"

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

/*! Configuration information of the driver */
typedef struct lis2dh12_config {
    lis2dh12_odr_t odr;     /*! Sample rate */
    lis2dh12_fs_t fs;       /*! Scale */
    lis2dh12_op_md_t op_md; /*! Resolution */
    uint8_t fifo_en;        /*! Flag enabling or disabling fifo mode */
} lis2dh12_config_t;

/*! Type describing one sample */
typedef union lis2dh12_data {
    int16_t i16bit[3]; /*! sample data described in 16bit format */
    uint8_t u8bit[6];  /*! sample data described in 8bit format */
} lis2dh12_data_t;

/*!
 * \brief Callback function to transfer a I2C sequence to a specific i2c address
 *
 * \param[in] p_param       optional pointer to application context
 * \param[in] dev_addr      I2C device address
 * \param[in] p_send_data   pointer to send data buffer
 * \param[in] send_len      number of bytes to send
 * \param[out] p_recv_data  pointer to receive data buffer
 * \param[in] recv_len      number of bytes to read
 *
 * \retval ::ERR_SUCCESS    Function returns without error
 * \retval ::ERR_I2C        I2C transfer error is occurred
 */
typedef err_code_t (*i2c_transfer_callback)(void *p_param, uint8_t dev_addr, uint8_t *p_send_data, uint16_t send_len,
                                            uint8_t *p_recv_data, uint16_t recv_len);

/******************************************************************************
 *                                 FUNCTIONS                                  *
 ******************************************************************************/

/*!
 * \brief Initialization of the accelerometer sensor.
 *
 * \note This function must be called at first!
 *
 * \param[in] i2c_addr                  I2C address of the sensor
 * \param[in] p_i2c_transfer            I2C transfer function
 * \param[in] p_callback_param          Pointer for optional parameter which will be commit via i2c callback function
 *
 * \retval ::ERR_SUCCESS                Function returns without error
 * \retval ::ERR_ARGUMENT               Argument not supported
 * \retval ::ERR_POINTER                Detected NULL pointer for p_i2c_transfer
 * \retval ::ERR_I2C                    I2C transfer error is occurred
 * \retval ::ERR_IDENTIFICATION         Identification of the sensor at the given address failed
 * \retval ::ERR_PERMISSION             Driver already initialized
 */
err_code_t lis2dh12_initialize(uint8_t i2c_addr, i2c_transfer_callback p_i2c_transfer, void *p_callback_param);

/*!
 * \brief Configuration of the accelerometer LIS2DH12
 *
 * \param[in] p_cfg                     Configuration information of the driver
 *
 * \retval ::ERR_SUCCESS                Function returns without error
 * \retval ::ERR_ARGUMENT               Argument not supported
 * \retval ::ERR_POINTER                Detected NULL pointer for p_i2c_transfer
 * \retval ::ERR_I2C                    I2C transfer error is occurred
 * \retval ::ERR_PERMISSION             Not initialized or data aquisition is already running
 */
err_code_t lis2dh12_configure(const lis2dh12_config_t *p_cfg);

/*!
 * \brief Readout of the actual sensor data.
 *
 * This function reads as many samples as possible depending on the requested amount of samples and
 * as long as data is available.
 *
 * \param[out] p_data                   Pointer to memory which can hold data from sensor
 * \param[inout] p_samples              Input: Amount of samples to read from sensor
 *                                      Output: Amount of samples read
 *
 * \retval ::ERR_SUCCESS                Function returns without error
 * \retval ::ERR_ARGUMENT               Argument id is not supported
 * \retval ::ERR_POINTER                Detected NULL pointer for p_millidegree
 * \retval ::ERR_PERMISSION             Initialization function was not called successfully
 * \retval ::ERR_DATA_TRANSFER          I2C transfer error is occurred
 * \retval ::ERR_OVERFLOW               Accelerometer FIFO is full
 */
err_code_t lis2dh12_read(lis2dh12_data_t *p_data, uint8_t *p_samples);

/*!
 * \brief Start measurement of the accelerometer sensor.
 *
 * \retval ::ERR_SUCCESS                Function returns without error
 * \retval ::ERR_POINTER                Detected NULL pointer for p_i2c_transfer
 * \retval ::ERR_DATA_TRANSFER          I2C transfer error is occurred
 */
err_code_t lis2dh12_start();

/*!
 * \brief Stop measurement of the accelerometer sensor.
 *
 * \retval ::ERR_SUCCESS                Function returns without error
 * \retval ::ERR_POINTER                Detected NULL pointer for p_i2c_transfer
 * \retval ::ERR_DATA_TRANSFER          I2C transfer error is occurred
 */
err_code_t lis2dh12_stop();

/*!
 * \brief Brings the device into power save mode and disable cyclic measurements
 *
 * \retval ::ERR_SUCCESS                Function returns without error
 */
err_code_t lis2dh12_shutdown();

#ifdef __cplusplus
}
#endif // __cplusplus

/*! @} */

#endif /* __LIS2DH12_H__ */
