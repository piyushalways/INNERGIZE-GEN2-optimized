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

#ifndef __AGC_HAL_H__
#define __AGC_HAL_H__

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

/*!
 * \file      agc_hal.h
 * \authors   RSIN
 * \copyright ams
 * \addtogroup VITAL_SIGNS_AGC_HAL HAL Functions
 *
 * \brief This file consists of platform-dependent interface functions and definitions for AGC module. The HAL needs to
 *        be implemented for every chip using the AGC algorithm.
 * @{
 */

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/
#include "std_inc.h"

#include "agc_typedefs.h"
#include "error_codes.h"
/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

/******************************************************************************
 *                                 FUNCTIONS                                  *
 ******************************************************************************/

/*!
 * \brief Initializes the HAL interface for the AGC.
 *
 * \param[in] p_config                  Application-specific configuration.
 * \param[in] size                      Size of the configuration.
 *
 * \retval ::ERR_SUCCESS                Function returns without error.
 * \retval ::ERR_SIZE                   The size of the configuration does not match.
 * \retval ::ERR_POINTER                Detected NULL pointer for data.
 */
err_code_t agc_hal_initialize(void *p_config, uint16_t size);

/*!
 * \brief Sets the LED current.
 *
 * \param[in] channel_id                Channel number.
 * \param[in] led_current               New LED current value.
 *
 * \retval ::ERR_SUCCESS                Function returns without error.
 * \retval ::ERR_DATA_TRANSFER          Error during communication with sensor.
 * \retval ::ERR_PERMISSION             HAL/OSAL library is not initialized.
 * \retval ::ERR_ARGUMENT               LED current is wrong or channel ID is not supported.
 * \retval ::ERR_LED_ACCESS             Error on LED configuration or access.
 */
err_code_t agc_hal_set_led_current(agc_channel_id_t channel_id, uint8_t led_current);

/*!
 * \brief Gets the LED current.
 *
 * \note This function will be called often and it is recommended to cache
 *       the LED currents internally to avoid unneeded I2C traffic.
 *
 * \param[in] channel_id                Channel number.
 * \param[out] p_led_current            Pointer to memory where the LED current will be saved.
 *
 * \retval ::ERR_SUCCESS                Function returns without error.
 * \retval ::ERR_DATA_TRANSFER          Error during communication with sensor.
 * \retval ::ERR_PERMISSION             HAL/OSAL library is not initialized.
 * \retval ::ERR_ARGUMENT               Channel ID is not supported.
 * \retval ::ERR_LED_ACCESS             Error on LED configuration or access.
 * \retval ::ERR_POINTER                NULL pointer detected for p_led_current.
 */
err_code_t agc_hal_get_led_current(agc_channel_id_t channel_id, uint8_t *p_led_current);

/*!
 * \brief Sets the PD offset currents.
 *
 * \param[in] channel_id                Channel number.
 * \param[in] pd_offset                 New PD offset value.
 *
 * \retval ::ERR_SUCCESS                Function returns without error.
 * \retval ::ERR_DATA_TRANSFER          Error during communication with sensor.
 * \retval ::ERR_ARGUMENT               PD offset configuration is wrong or channel ID is not supported.
 * \retval ::ERR_PERMISSION             HAL/OSAL library is not initialized.
 */
err_code_t agc_hal_set_pd_offset(agc_channel_id_t channel_id, uint8_t pd_offset);

/*!
 * \brief Gets the PD offset currents.
 *
 * \param[in] channel_id                Channel number.
 * \param[out] p_pd_offset              Pointer to memory where the PD offset value will be saved.
 *
 * \retval ::ERR_SUCCESS                Function returns without error.
 * \retval ::ERR_DATA_TRANSFER          Error during communication with sensor.
 * \retval ::ERR_ARGUMENT               Channel ID is not supported.
 * \retval ::ERR_PERMISSION             HAL/OSAL library is not initialized.
 * \retval ::ERR_POINTER                NULL pointer detected for p_pd_offset.
 */
err_code_t agc_hal_get_pd_offset(agc_channel_id_t channel_id, uint8_t *p_pd_offset);

/*!
 * \brief Extract the requested samples from FIFO data stream.
 *
 * When the AGC module receives a new FIFO data stream, it calls this function for each enabled AGC instance to extract
 * the corresponding samples. When the function is called the first time after new FIFO data has been received, the
 * parameter fifo_data_changed is set to TRUE to indicate the FIFO data change.
 *
 * \param[in] channel_id                Channel number.
 * \param[in] p_fifo_data               FIFO data.
 * \param[in] fifo_data_size            Size of FIFO data.
 * \param[in] fifo_data_changed         Set to TRUE to signal that this is new FIFO data.
 * \param[out] p_chan_data              Pointer to buffer where the sub-sample data can be saved.
 * \param[inout] p_chan_data_num        Input: Number of provided p_chan_data elements; Output: Number of used
 *                                      p_chan_data elements.
 *
 * \retval ::ERR_SUCCESS                Function returns without error.
 * \retval ::ERR_ARGUMENT               At least one parameter is wrong.
 * \retval ::ERR_POINTER                Detected NULL pointer for data.
 * \retval ::ERR_PERMISSION             HAL/OSAL library is not initialized.
 */
err_code_t agc_hal_extract_samples(agc_channel_id_t channel_id, const uint8_t *p_fifo_data, uint16_t fifo_data_size,
                                   uint8_t fifo_data_changed, int32_t *p_chan_data, uint16_t *p_chan_data_num);

/*!
 * \brief Requests the sampling period for the given channel in microseconds.
 *
 * \param[in] channel_id                Channel number.
 * \param[out] p_sampling_period        Sampling period of the PPG signal in microseconds.
 *
 * \retval ::ERR_SUCCESS                Function returns without error.
 * \retval ::ERR_POINTER                If the argument is NULL.
 * \retval ::ERR_PERMISSION             HAL/OSAL library is not initialized.
 */
err_code_t agc_hal_get_sampling_period_us(agc_channel_id_t channel_id, uint32_t *p_sampling_period);

/*!
 * \brief Disables this library and block the functions calls.
 *
 * \retval ::ERR_SUCCESS                Function returns without error.
 */
err_code_t agc_hal_shutdown(void);

#ifdef __cplusplus
}
#endif // __cplusplus

/*! @} */

#endif /* __AGC_hal_H__ */
