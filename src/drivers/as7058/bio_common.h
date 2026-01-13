/******************************************************************************
 * Copyright © 2022 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

#ifndef __BIO_COMMON_H__
#define __BIO_COMMON_H__

/*!
 * \file       bio_common.h
 * \authors    ARIT, PKRN
 * \copyright  ams OSRAM
 * \addtogroup bio_app_group
 *
 * \brief This module contains definitions used by all Bio Apps.
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

/*! Indicates whether the Bio App is executable. */
enum bio_execution_status {
    BIO_EXECUTION_STATUS_NOT_EXECUTABLE = 0, /*!< The Bio App has not yet received sufficient amounts of data to be
                                                  executed. */
    BIO_EXECUTION_STATUS_EXECUTABLE,         /*!< The execute function of the Bio App can be called as it has received
                                                  sufficient data. */
};

/*! Type definition for ::bio_execution_status. */
typedef uint8_t bio_execution_status_t;

/*! Indicates whether output data is available from the Bio App. */
enum bio_output_status {
    BIO_OUTPUT_STATUS_DATA_UNAVAILABLE = 0, /*!< No output data is available. */
    BIO_OUTPUT_STATUS_DATA_AVAILABLE,       /*!< The get output function of the Bio App can be called as output data is
                                                 available. */
};

/*! Type definition for ::bio_output_status. */
typedef uint8_t bio_output_status_t;

/*! Indicates the type of sensor signal samples. */
enum bio_signal_samples_type {
    BIO_SIGNAL_SAMPLES_TYPE_U16 = 0, /*!< Data is provided as an unsigned 16-bit integer. */
    BIO_SIGNAL_SAMPLES_TYPE_U32,     /*!< Data is provided as an unsigned 32-bit integer. */
    BIO_SIGNAL_SAMPLES_TYPE_I32,     /*!< Data is provided as a signed 32-bit integer. */
};

/*! Type definition for ::bio_signal_samples_type. */
typedef uint8_t bio_signal_samples_type_t;

/*! Contains a pointer to the samples of sensor signals and the corresponding sample count. */
typedef struct {
    union {
        const uint16_t *p_u16; /*!< Points to unsigned 16-bit signal samples. Use this pointer when the data type of the
                                    samples is ::BIO_SIGNAL_SAMPLES_TYPE_U16. */
        const uint32_t *p_u32; /*!< Points to unsigned 32-bit signal samples. Use this pointer when the data type of the
                                    samples is ::BIO_SIGNAL_SAMPLES_TYPE_U32. */
        const int32_t *p_i32;  /*!< Points to signed 32-bit signal samples. Use this pointer when the data type of the
                                    samples is ::BIO_SIGNAL_SAMPLES_TYPE_I32. */
    } samples;          /*!< Points to the start of an array containing the samples of this sensor signal. This union
                             contains pointers to different types. Check the ::bio_signal_samples_type_t used by the
                             app and use the corresponding union member. */
    unsigned int count; /*!< Contains the number of items in the signal samples array. */
} bio_signal_samples_t;

/*! @} */

#endif /* __BIO_COMMON_H__ */
