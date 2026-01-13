/******************************************************************************
 * Copyright © 2022 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

#ifndef __AS7058_EXTRACT2_H__
#define __AS7058_EXTRACT2_H__

/*!
 * \file        as7058_extract2.h
 * \authors     PKRN
 * \copyright   ams OSRAM
 * \addtogroup  extract2_group Sub-sample extraction with SAR support
 *
 * \brief Module for extracting all samples in the FIFO data stream including their SAR photodiode offset currents.
 *
 *  @{
 */

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include "as7058_typedefs.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

#ifndef AS7058_EXTRACT2_FUNC_DECL
/*! Preprocessor macro that is placed in front of every internal function declaration with external linkage. By default
 * this macro is defined to expand to nothing, but it can be defined externally. Example use cases include setting
 * keywords. */
#define AS7058_EXTRACT2_FUNC_DECL
#endif

/*! Sample extracted from the FIFO buffer. */
typedef struct {
    uint32_t pd_offset : 8;   /*!< SAR-controlled value of the photodiode offset current. If SAR is enabled, this field
                                   contains the current photodiode offset current. SAR controls the upper four bits of
                                   the photodiode offset current. The lower four bits can be set to a constant value by
                                   writing to a register. In SAR transfer mode ::AS7058_SAR_TRANSFER_MODE_SEPARATE, the
                                   full photodiode offset current is provided. In SAR transfer mode
                                   ::AS7058_SAR_TRANSFER_MODE_INLINE, only the SAR-controlled bits are provided and the
                                   lower four bits are always set to zero. The full photodiode offset current can be
                                   obtained by combining the value of this field with the lower four bits of the value
                                   written to the register using a bitwise OR operation.  */
    uint32_t sar_enabled : 1; /*!< SAR is enabled if this field is non-zero. */
    uint32_t reserved : 3;    /*!< Reserved for future use. */
    uint32_t adc_value : 20;  /*!< ADC value of the acquired sample. */
} as7058_extract2_sample_t;

/*!
 * State of the sample extraction. During an ongoing measurement, all received FIFO data streams must be extracted in
 * the order they have been received using the same instance of this structure. Do not modify the members of this
 * structure directly.
 */
typedef struct {
    uint32_t fifo_map; /*!< Bitmask representing the sub-samples that are enabled in the AS7058 AFE for the current
                            measurement, see ::as7058_sub_sample_flags. */
    uint32_t sar_map;  /*!< Bitmask representing the sub-samples for which SAR is enabled in the AS7058 AFE, see
                            ::as7058_sub_sample_flags. In the AS7058 AFE, SAR can be enabled per PPG sub-sample but not
                            per modulator, i.e. it is not possible to enable SAR for sub-sample 1 on PPG modulator 1
                            but disable it for sub-sample 1 on PPG modulator 2. Despite this, this bitmask uses the
                            standard ::as7058_sub_sample_flags where there are separate bits for PPG modulator 1 and
                            PPG modulator 2 for each sub-sample. If SAR is enabled for a sub-sample, the bits
                            corresponding to this sub-sample on both PPG modulator 1 and PPG modulator 2 need to be set.
                            However, bits that are not set in the FIFO map do not necessarily need to be set in the SAR
                            map. For example, if SAR is enabled for PPG sub-sample 1 and
                            ::AS7058_SUB_SAMPLE_FLAG_PPG1_SUB1 and ::AS7058_SUB_SAMPLE_FLAG_PPG2_SUB1 are set in the
                            FIFO map, ::AS7058_SUB_SAMPLE_FLAG_PPG1_SUB1 and ::AS7058_SUB_SAMPLE_FLAG_PPG2_SUB1 also
                            need to be set in the SAR map. If either ::AS7058_SUB_SAMPLE_FLAG_PPG1_SUB1 or
                            ::AS7058_SUB_SAMPLE_FLAG_PPG2_SUB1 are not set in the FIFO map, the corresponding bit can
                            also be left unset in the SAR map. */
    uint8_t reserved;  /*!< Reserved for future use. */
    as7058_sar_transfer_mode_t sar_transfer_mode; /*!< Indicates how the AS7058 AFE is configured to provide the SAR
                                                       status information. */
    as7058_modulator_sub_sample_t last_ppg_sub_samples[AS7058_MODULATOR_NUM_PPG]; /*!< Contains to which sub-sample the
                                                                                       last received sample of a PPG
                                                                                       modulator belongs. */
    uint8_t last_pd_offsets[AS7058_MODULATOR_NUM_PPG][AS7058_MODULATOR_SUB_SAMPLE_NUM_PPG]; /*!< Contains the last
                                                                                                 received SAR photodiode
                                                                                                 offset current per
                                                                                                 sub-sample for each PPG
                                                                                                 modulator. */
    uint32_t last_pd_offsets_valid; /*!< Bitmask representing the sub-samples for which last_pd_offsets contains a valid
                                         value, see ::as7058_sub_sample_flags. */
} as7058_extract2_state_t;

/*!
 * Type for an array of pointers with `AS7058_SUB_SAMPLE_ID_NUM + 1` elements. The extracted samples of type
 * ::as7058_extract2_sample_t are stored in a separate buffer. Inside the separate buffer, the extracted samples of a
 * single sub-sample are stored in contiguous memory. The first `AS7058_SUB_SAMPLE_ID_NUM` elements of this array point
 * to the first extracted sample of the corresponding sub-sample. The subsequent array element always points past the
 * last extracted sample of the sub-sample. See the description of ::as7058_extract2 for more information.
 */
typedef const as7058_extract2_sample_t *as7058_extract2_sub_sample_samples_t[AS7058_SUB_SAMPLE_ID_NUM + 1];

/******************************************************************************
 *                                 FUNCTIONS                                  *
 ******************************************************************************/

/*!
 * \brief Prepares the ::as7058_extract2_state_t instance for a new measurement.
 *
 * During an ongoing measurement, all received FIFO data streams must be extracted in the order they have been received
 * using the same instance of ::as7058_extract2_state_t.
 *
 * \param[in] fifo_map          Bitmask representing the sub-samples that are enabled in the AS7058 AFE for the current
 *                              measurement, see ::as7058_sub_sample_flags.
 * \param[in] sar_map           Bitmask representing the sub-samples for which SAR is enabled in the AS7058 AFE, see
 *                              ::as7058_sub_sample_flags. In the AS7058 AFE, SAR can be enabled per PPG sub-sample but
 *                              not per modulator, i.e. it is not possible to enable SAR for sub-sample 1 on PPG
 *                              modulator 1 but disable it for sub-sample 1 on PPG modulator 2. Despite this, this
 *                              bitmask uses the standard ::as7058_sub_sample_flags where there are separate bits for
 *                              PPG modulator 1 and PPG modulator 2 for each sub-sample. If SAR is enabled for a
 *                              sub-sample, the bits corresponding to this sub-sample on both PPG modulator 1 and PPG
 *                              modulator 2 need to be set. However, bits that are not set in the FIFO map do not
 *                              necessarily need to be set in the SAR map. For example, if SAR is enabled for PPG
 *                              sub-sample 1 and ::AS7058_SUB_SAMPLE_FLAG_PPG1_SUB1 and
 *                              ::AS7058_SUB_SAMPLE_FLAG_PPG2_SUB1 are set in the FIFO map,
 *                              ::AS7058_SUB_SAMPLE_FLAG_PPG1_SUB1 and ::AS7058_SUB_SAMPLE_FLAG_PPG2_SUB1 also need to
 *                              be set in the SAR map. If either ::AS7058_SUB_SAMPLE_FLAG_PPG1_SUB1 or
 *                              ::AS7058_SUB_SAMPLE_FLAG_PPG2_SUB1 are not set in the FIFO map, the corresponding bit
 *                              can also be left unset in the SAR map.
 * \param[in] sar_transfer_mode Indicates how the AS7058 AFE is configured to provide the SAR status information.
 * \param[out] p_state          Pointer to the ::as7058_extract2_state_t instance to prepare.
 *
 * \retval ::ERR_SUCCESS  Function returns without error.
 * \retval ::ERR_POINTER  Invalid pointer argument.
 * \retval ::ERR_ARGUMENT Invalid FIFO map, invalid SAR map, or invalid SAR transfer mode.
 */
AS7058_EXTRACT2_FUNC_DECL err_code_t as7058_extract2_prepare_for_new_measurement(
    uint32_t fifo_map, uint32_t sar_map, as7058_sar_transfer_mode_t sar_transfer_mode,
    as7058_extract2_state_t *p_state);

/*!
 * \brief Extracts all samples from the provided FIFO data stream.
 *
 * During an ongoing measurement, all received FIFO data streams must be extracted in the order they have been received
 * using the same instance of ::as7058_extract2_state_t. When starting a measurement, first call
 * ::as7058_extract2_prepare_for_new_measurement to prepare the ::as7058_extract2_state_t instance.
 *
 * \htmlonly
 *
 * Graphical representation of the produced output in p_sub_sample_samples and p_sample_buffer, assuming there are three
 * PPG1 SUB1 samples, two PPG1 SUB2 samples, and one ECG SEC2 SUB1 sample. There are zero samples for all other
 * sub-samples.
 *
 * \code
 *                       p_sub_sample_samples          p_sample_buffer
 *                                │                           │
 *                                └──►┌───────────┐       ┌──►└──►┌────────────────────────┐ ───┐
 *      AS7058_SUB_SAMPLE_ID_DISABLED │ Undefined │       │       │   PPG1 SUB1 Sample 0   │    │
 *                                    ├───────────┤       │       ├────────────────────────┤    │
 *     AS7058_SUB_SAMPLE_ID_PPG1_SUB1 │           ├───────┘       │   PPG1 SUB1 Sample 1   │    │
 *                                    ├───────────┤               ├────────────────────────┤    │
 *     AS7058_SUB_SAMPLE_ID_PPG1_SUB2 │           ├───────┐       │   PPG1 SUB1 Sample 2   │    │
 *                                    ├───────────┤       └──────►├────────────────────────┤    │
 *     AS7058_SUB_SAMPLE_ID_PPG1_SUB3 │           ├────────────┐  │   PPG1 SUB2 Sample 0   │    │ sample_buffer_length
 *                                    ├───────────┤            │  ├────────────────────────┤    |
 *     AS7058_SUB_SAMPLE_ID_PPG1_SUB4 │           ├─────────┐  │  │   PPG1 SUB2 Sample 1   │    │
 *                                    ├───────────┤   ┌─►┌─►└─►└─►├────────────────────────┤    │
 *     ┌──────────────────────────┐                   │  │        │ ECG SEQ2 SUB1 Sample 1 │    │
 *     │    All array elements    │                   │  │  ┌────►├────────────────────────┤    │
 *     │ in-between also point to │        •••        │  │  │                 •••               │
 *     │  ECG SEQ2 SUB1 Sample 1  │                   │  │  │     └────────────────────────┘ ───┘
 *     └──────────────────────────┘                   │  │  │
 *                                    ├───────────┤   │  │  │
 * AS7058_SUB_SAMPLE_ID_ECG_SEQ1_SUB2 │           ├───┘  │  │
 *                                    ├───────────┤      │  │
 * AS7058_SUB_SAMPLE_ID_ECG_SEQ2_SUB1 │           ├──────┘  │
 *                                    ├───────────┤         │
 *           AS7058_SUB_SAMPLE_ID_NUM │           ├─────────┘
 *                                    └───────────┘
 *
 * \endcode
 * \endhtmlonly
 *
 * \param[in] p_fifo_data            Pointer to the start of the FIFO data stream to extract.
 * \param[in] fifo_data_size         Size of the FIFO data stream in bytes.
 * \param[out] pp_sub_sample_samples Pointer to an array with `AS7058_SUB_SAMPLE_ID_NUM + 1` elements where each item
 *                                   (excluding the last one) points to the first extracted sample of the corresponding
 *                                   sub-sample. The extracted samples are sorted in the order they occurred in the FIFO
 *                                   data stream. The subsequent array element always points past the last extracted
 *                                   sample of the sub-sample. Please refer to the drawing in the header file for more
 *                                   information.
 * \param[out] p_sample_buffer       Pointer to the buffer storing the extracted samples.
 * \param[out] sample_buffer_length  Number of elements that can be stored in the extracted samples buffer.
 * \param[inout] p_state             Instance of the ::as7058_extract2_state_t instance.
 *
 * \retval ::ERR_SUCCESS  Function returns without error.
 * \retval ::ERR_POINTER  Invalid pointer argument.
 * \retval ::ERR_SIZE     Invalid FIFO data stream size or extracted samples buffer length.
 * \retval ::ERR_DATA     Inconsistency detected in FIFO data stream or between configuration in
 *                        ::as7058_extract2_state_t instance and actual configuration of AS7058 AFE.
 * \retval ::ERR_ARGUMENT Invalid data in the ::as7058_extract2_state_t instance.
 */
AS7058_EXTRACT2_FUNC_DECL err_code_t as7058_extract2(const uint8_t *p_fifo_data, uint16_t fifo_data_size,
                                                     as7058_extract2_sub_sample_samples_t *pp_sub_sample_samples,
                                                     as7058_extract2_sample_t *p_sample_buffer,
                                                     uint16_t sample_buffer_length, as7058_extract2_state_t *p_state);

/******************************************************************************
 *                            TYPE SIZE VALIDATION                            *
 ******************************************************************************/

M_STATIC_ASSERT_TYPE_SIZE(as7058_extract2_state_t, 32);

#ifdef __cplusplus
}
#endif // __cplusplus

/*! @} */

#endif /* __AS7058_EXTRACT2_H__ */
