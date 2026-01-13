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

#ifndef __AGC_FUNCTIONS_H__
#define __AGC_FUNCTIONS_H__

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

/*!
 * \file      agc.h
 * \authors   RSIN
 * \copyright ams
 * \addtogroup VITAL_SIGNS_AGC Vital Signs AGC
 *
 * \brief The Automatic Gain Compensation (AGC) module implements an algorithm to keep PPG signals within a configured
 *        range by continiously adjusting the photodiode (PD) offset current and the LED current.
 *
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

/*!
 * \brief Initializes the AGC module.
 *
 * AGC module transitions to Configuration state after initialization.
 *
 * \retval ::ERR_SUCCESS Function returns without error.
 */
err_code_t agc_initialize(void);

/*!
 * \brief Sets the configuration of the AGC module.
 *
 * All previous AGC configurations are discarded when this function is called. This function can only be called when the
 * AGC module is in Configuration state.
 *
 * \param[in] p_agc_configs   Pointer to an array of AGC configurations. A configuration needs to provided for each AGC
 *                            instance that shall be enabled.
 * \param[in] agc_config_num  Number of AGC configurations in the p_agc_configs array.
 *
 * \retval ::ERR_SUCCESS    Function returns without error.
 * \retval ::ERR_ARGUMENT   At least one parameter is wrong.
 * \retval ::ERR_POINTER    Detected NULL pointer.
 * \retval ::ERR_PERMISSION Invalid state.
 */
err_code_t agc_set_configuration(const agc_configuration_t *p_agc_configs, uint8_t agc_config_num);

/*!
 * \brief Gets the configuration of the AGC module.
 *
 * This function can only be called when the AGC module is not in Uninitialized state.
 *
 * \param[out]   p_agc_configs    Pointer to where the AGC configurations are written to. The configuration for each
 *                                enabled AGC instance is provided.
 * \param[inout] p_agc_config_num Pointer to a variable containing the maximum number of AGC configurations that can be
 *                                written to the p_agc_configs array. After writing the AGC configurations, the variable
 *                                is updated to contain the number of written AGC configurations.
 *
 * \retval ::ERR_SUCCESS    Function returns without error.
 * \retval ::ERR_SIZE       Destination buffer is too small.
 * \retval ::ERR_POINTER    Detected NULL pointer.
 * \retval ::ERR_PERMISSION Invalid state.
 */
err_code_t agc_get_configuration(agc_configuration_t *p_agc_configs, uint8_t *p_agc_config_num);

/*!
 * \brief Prepares the AGC algorithm for execution.
 *
 * This function can only be called when the AGC module is in Configuration state. The AGC module transitions to
 * Processing state when this function executes successfully.
 *
 * \param[in] p_config Chip-specific configuration information, which is forwarded to the HAL.
 * \param[in] size     Size of the p_config configuration information.
 *
 * \retval ::ERR_SUCCESS       Function returns without error.
 * \retval ::ERR_POINTER       Detected NULL pointer.
 * \retval ::ERR_SYSTEM_CONFIG Invalid sample period provided by HAL.
 * \retval ::ERR_CONFIG        AGC mode is not correctly configured.
 * \retval ::ERR_PERMISSION    Invalid state.
 */
err_code_t agc_start_processing(void *p_config, uint16_t size);

/*!
 * \brief Executes the AGC algorithm by processing the provided FIFO data.
 *
 * This function can only be called when the AGC module is in Processing state.
 *
 * \param[in] p_fifo_data    FIFO data.
 * \param[in] fifo_data_size Size of FIFO data.
 *
 * \retval ::ERR_SUCCESS     Function returns without error.
 * \retval ::ERR_SIZE        Size of FIFO data is zero.
 * \retval ::ERR_POINTER     Detected NULL pointer.
 * \retval ::ERR_PERMISSION  Invalid state.
 */
err_code_t agc_execute(const uint8_t *p_fifo_data, uint16_t fifo_data_size);

/*!
 * \brief Gets the AGC status information for all enabled AGC instances.
 *
 * This function can only be called when the AGC module is in Processing state.
 *
 * \param[out]   p_agc_status     Pointer to where the AGC status informations are written to. The AGC status
 *                                information for each enabled AGC instance is provided. The order of the AGC status
 *                                informations is identical to the order used for the configuration of the AGC
 *                                instances.
 * \param[inout] p_agc_status_num Pointer to a variable containing the maximum number of AGC status informations that
 *                                can be written to the p_agc_status array. After writing the AGC status informations,
 *                                the variable is updated to contain the number of written AGC status informations.
 *
 * \retval ::ERR_SUCCESS    Function returns without error.
 * \retval ::ERR_SIZE       Destination buffer is too small.
 * \retval ::ERR_POINTER    Detected NULL pointer.
 * \retval ::ERR_PERMISSION Invalid state.
 */
err_code_t agc_get_status(agc_status_t *p_agc_status, uint8_t *p_agc_status_num);

/*!
 * \brief Exits the Processing state of the AGC algorithm.
 *
 * This function can only be called when the AGC module is not in Uninitialized state. The AGC module transitions to
 * Configuration state when this function executes successfully.
 *
 * \retval ::ERR_SUCCESS    Function returns without error.
 * \retval ::ERR_PERMISSION Invalid state.
 */
err_code_t agc_stop_processing(void);

/*!
 * \brief De-initializes the AGC module.
 *
 * \retval ::ERR_SUCCESS Function returns without error.
 */
err_code_t agc_shutdown(void);

/*!
 * \brief Gets the version of AGC module.
 *
 * \param[out] p_agc_version Pointer to where the version is written to.
 *
 * \retval ::ERR_SUCCESS Function returns without error.
 * \retval ::ERR_POINTER Detected NULL pointer.
 */
err_code_t agc_get_version(agc_version_t *p_agc_version);

#ifdef __cplusplus
}
#endif // __cplusplus

/*! @} */

#endif /* __AGC_FUNCTIONS_H__ */
