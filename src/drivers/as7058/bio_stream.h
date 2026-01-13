/******************************************************************************
 * Copyright © 2022 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

#ifndef __BIO_STREAM_H__
#define __BIO_STREAM_H__

#ifdef __cplusplus
extern "C" {
#endif

/*!
 * \file       bio_stream.h
 * \authors    ARIT
 * \copyright  ams OSRAM
 * \addtogroup bio_stream_group
 *
 * \brief This application allows streaming of internal data in a generic way. It is configurable which data shall be
 *        streamed.
 *
 * \note  The API is not compatible with the app interface.
 *
 * \note  The library is not thread-safe.
 *
 * @{
 */

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include "bio_stream_typedefs.h"

/******************************************************************************
 *                                 FUNCTIONS                                  *
 ******************************************************************************/

/*!
 * \brief Initializes the app.
 *
 * \retval ::ERR_SUCCESS Initialized successfully.
 */
err_code_t bio_stream_initialize(void);

/*!
 * \brief Configures the app.
 *
 * This function can only be called when the app is initialized and not in a processing session.
 *
 * \param[in] p_config Pointer to the configuration structure, see ::bio_stream_configuration_t. It must not be NULL.
 * \param[in] size     Size of the configuration structure. It must be `sizeof(bio_stream_configuration_t)`.
 *
 * \retval ::ERR_SUCCESS    Updated successfully.
 * \retval ::ERR_ARGUMENT   Upper threshold is lower than the lower threshold.
 * \retval ::ERR_POINTER    Invalid pointer to configuration structure.
 * \retval ::ERR_SIZE       Size does not match expected size.
 * \retval ::ERR_PERMISSION Not initialized or in a processing session.
 */
err_code_t bio_stream_configure(const void *p_config, uint8_t size);

/*!
 * \brief Copies the current configuration of the app to the provided buffer.
 *
 * This function can only be called when the app is initialized and not in a processing session.
 *
 * The size of the configuration is `sizeof(bio_stream_configuration_t)`.
 *
 * \param[out] p_dest   Points to the start of the buffer where the configuration shall be copied to. This value must
 *                      not be NULL.
 * \param[inout] p_size Points to a variable containing the size of the buffer where the configuration shall be copied
 *                      to. After copying, the value of this variable is updated with the actual size of the copied
 *                      configuration. This value must not be NULL.
 *
 * \retval ::ERR_SUCCESS    Copying successful.
 * \retval ::ERR_NO_DATA    App is not configured.
 * \retval ::ERR_POINTER    At least one pointer argument is NULL which must not be NULL.
 * \retval ::ERR_SIZE       The size of the buffer is not sufficient.
 * \retval ::ERR_PERMISSION Not initialized or in a processing session.
 */
err_code_t bio_stream_get_configuration(void *p_dest, uint8_t *p_size);

/*!
 * \brief Starts a processing session and clears the internal queue.
 *
 * This function can only be called when the app is initialized and not in a processing session.
 *
 * \retval ::ERR_SUCCESS    Updated successfully.
 * \retval ::ERR_PERMISSION Not initialized or in a processing session.
 */
err_code_t bio_stream_start(void);

/*!
 * \brief Provides measurement data to the app.
 *
 * This function can only be called when the app is initialized and in a processing session.
 *
 * \param[in] id            ID of the given data.
 * \param[in] p_data        Payload of the ID.
 * \param[in] size          Size of the payload.
 * \param[in] option_flags  Option flags, see ::bio_stream_send_option_flags.
 * \param[out] p_result     The value pointed to by this argument is updated with information whether the app is ready
 *                          for execution. This value can be NULL.
 *
 * \retval ::ERR_SUCCESS    Data accepted.
 * \retval ::ERR_ARGUMENT   ID value is out of range.
 * \retval ::ERR_POINTER    Invalid pointer to data.
 * \retval ::ERR_SIZE       The provided buffer is zero or larger than the maximum supported packet size.
 * \retval ::ERR_PERMISSION Not initialized or not in a processing session.
 */
err_code_t bio_stream_set_input(uint8_t id, const void *p_data, uint16_t size, uint8_t option_flags,
                                bio_execution_status_t *p_result);

/*!
 * \brief Processes the data previously provided to the app.
 *
 * This function can be called once after ::bio_stream_set_input indicated via the p_result argument that the app is
 * executable. Afterwards, this function can be called again when a subsequent call of ::bio_stream_set_input indicated
 * that the app is executable. The app must be initialized and in a processing session when calling this function.
 *
 * \note This function is only implemented because of compatiblity reasons and does not calculate anything. It can be
 *       used to signal available output data.
 *
 * \param[out] p_result     The value pointed to by this argument is updated with information whether the app has data
 *                          available for output. This value must not be NULL.
 *
 * \retval ::ERR_SUCCESS    Processing successful.
 * \retval ::ERR_POINTER    p_result is NULL.
 * \retval ::ERR_PERMISSION Not initialized or not in a processing session.
 */
err_code_t bio_stream_execute(bio_output_status_t *p_result);

/*!
 * \brief Copies output data generated by the app to a buffer provided by the caller.
 *
 * This function needs to called repeatedly after calling ::bio_stream_start. To get all available data, the function
 * needs to be called until it returns ::ERR_NO_DATA.
 *
 * The size of the destination buffer must be at least the configured maximum package size.
 *
 * This function can only be called when the app is initialized.
 *
 * \param[out] p_dest   Points to the start of the buffer where the output data shall be copied to. This value must not
 *                      be NULL.
 * \param[inout] p_size Points to a variable containing the size of the buffer where the output data shall be copied to.
 *                      After copying, the value of this variable is updated with the actual size of the copied data.
 *                      This value must not be NULL.
 *
 * \retval ::ERR_SUCCESS    Copying successful.
 * \retval ::ERR_POINTER    At least one pointer argument is NULL which must not be NULL.
 * \retval ::ERR_SIZE       The size of the buffer is not sufficient.
 * \retval ::ERR_NO_DATA    No output data is available for copying.
 * \retval ::ERR_PERMISSION Not initialized.
 */
err_code_t bio_stream_get_output(void *p_dest, uint16_t *p_size);

/*!
 * \brief This function extracts the values of the compressed item header and creates a ::bio_stream_header_t structure.
 *
 * \param[in] bytes   Compressed header to extract.
 *
 * \return Extracted header.
 */
bio_stream_header_t bio_stream_extract_header_bytes(const uint8_t bytes[BIO_STREAM_ITEM_HEADER_SIZE]);

/*!
 * \brief Stops the current processing session of the app, allowing it to be reconfigured.
 *
 * This function can only be called when the app is initialized.
 *
 * After calling this function, pending packages can still be obtained by calling ::bio_stream_get_output.
 *
 * \retval ::ERR_SUCCESS    Stopping successful.
 * \retval ::ERR_PERMISSION Not initialized.
 */
err_code_t bio_stream_stop(void);

/*!
 * \brief De-initializes the app.
 *
 * \retval ::ERR_SUCCESS De-initialization successful.
 */
err_code_t bio_stream_shutdown(void);

/*!
 * \brief Gets the version of the app.
 *
 * \return Version string.
 */
const char *bio_stream_get_version(void);

#ifdef __cplusplus
}
#endif

/*! @} */

#endif /* __BIO_STREAM_H__ */
