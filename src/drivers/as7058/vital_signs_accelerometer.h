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

#ifndef __VITAL_SIGNS_ACC_H__
#define __VITAL_SIGNS_ACC_H__

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

/*!
 * \file      vital_signs_accelerometer.h
 * \authors   ARIT
 * \copyright ams
 * \addtogroup accelerometer
 *
 * \brief This is the default accelerometer interface description for vital signs applications.
 * It's a very simple interface which allows an abstraction of any accelerometer.
 *
 * By default two kinds of 'accelerometers' are supported. The first one will be used if no real accelerometer can be
 * found. This module sends cylcic accelerometer data to the caller module in dependency to the configured sample
 * period. The content of the data will be always zero.
 * The seconds device is the LIS2DH12 from ST Microelectronics.
 *
 * @{
 */

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include <stdint.h>

#include "error_codes.h"
#include "std_inc.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

/*! Accelerometer measurement sample */
typedef struct {
    int16_t x; /*!< Acceleration on x-axis. The unit is 0.5 mg/LSB. */
    int16_t y; /*!< Acceleration on y-axis. The unit is 0.5 mg/LSB. */
    int16_t z; /*!< Acceleration on z-axis. The unit is 0.5 mg/LSB. */
} vs_acc_data_t;

/******************************************************************************
 *                                 FUNCTIONS                                  *
 ******************************************************************************/

/*!
 * \brief Initialisation of any accelerometer.
 *
 * \param[in] p_config          Optional configuration parameter for future implementations.
 *                              This is forwarded to the OSAL functions.
 *
 * \retval ::ERR_SUCCESS        Function returns without error.
 * \retval ::ERR_ACCELEROMETER  Any error regarding the accelerometer.
 */
err_code_t vs_acc_initialize(const char *p_config);

/*!
 * \brief Configuration of the sample period.
 *
 * \param[in] sample_period_us  Sample period of the accelerometer in microseconds.
 *
 * \retval ::ERR_SUCCESS        Function returns without error.
 * \retval ::ERR_ACCELEROMETER  Any error regarding the accelerometer.
 * \retval ::ERR_PERMISSION     Access to driver is blocked. Call ::vs_acc_initialize first
 */
err_code_t vs_acc_set_sample_period(uint32_t sample_period_us);

/*!
 * \brief Shutdown of the accelerometer driver.
 *
 * \retval ::ERR_SUCCESS        Function returns without error.
 * \retval ::ERR_ACCELEROMETER  Any error regarding the accelerometer.
 */
err_code_t vs_acc_shutdown(void);

/*!
 * \brief Starts the cyclic accelerometer measurement.
 *
 * \retval ::ERR_SUCCESS        Function returns without error.
 * \retval ::ERR_ACCELEROMETER  Any error regarding the accelerometer.
 * \retval ::ERR_PERMISSION     Access to driver is blocked. Call ::vs_acc_initialize first.
 */
err_code_t vs_acc_start(void);

/*!
 * \brief Stops the cyclic accelerometer measurement.
 *
 * \retval ::ERR_SUCCESS        Function returns without error.
 * \retval ::ERR_ACCELEROMETER  Any error regarding the accelerometer.
 * \retval ::ERR_PERMISSION     Access to driver is blocked. Call ::vs_acc_initialize first.
 */
err_code_t vs_acc_stop(void);

/*!
 * \brief Request of measured sensor data.
 *
 * This function handles more than one coordinate triplet.
 *
 * \param[out] p_acc_data       Pointer to memory where measured coordinates can be saved.
 * \param[inout] p_num_acc_data Input: Contains the maximum number of coordinate triplets.
 *                              Output: Pointer to memory where number of the measured coordinate triplets can be saved.
 *
 * \retval ::ERR_SUCCESS        Function returns without error.
 * \retval ::ERR_ACCELEROMETER  Any error regarding the accelerometer.
 * \retval ::ERR_PERMISSION     Access to driver is blocked. Call ::vs_acc_initialize first.
 * \retval ::ERR_ARGUMENT       Content of p_num_acc_data must not be zero.
 */
err_code_t vs_acc_get_data(vs_acc_data_t *p_acc_data, uint8_t *p_num_acc_data);

/******************************************************************************
 *                            TYPE SIZE VALIDATION                            *
 ******************************************************************************/

M_STATIC_ASSERT_TYPE_SIZE(vs_acc_data_t, 6);

#ifdef __cplusplus
}
#endif // __cplusplus

/*! @} */

#endif /* __VITAL_SIGNS_ACC_H__ */
