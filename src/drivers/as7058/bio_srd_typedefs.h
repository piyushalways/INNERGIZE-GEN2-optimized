/******************************************************************************
 * Copyright © 2022 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

#ifndef __BIO_SRD_TYPEDEFS_H__
#define __BIO_SRD_TYPEDEFS_H__

/*!
 * \file       bio_srd_typedefs.h
 * \authors    PKRN
 * \copyright  ams OSRAM
 * \addtogroup bio_srd_group Signal Range Detection
 *
 * @{
 */

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include "bio_common.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

/*! The signal data type required by the Signal Range Detection Bio App. */
#define BIO_SRD_SIGNAL_DATA_TYPE BIO_SIGNAL_SAMPLES_TYPE_I32

/*! Bitmask for the signal status bits in bio_srd_output_t::flags. */
#define BIO_SRD_OUTPUT_FLAGS_SIGNAL_STATUS_MASK 0x0F

/*! Bitmask for the output reason bit in bio_srd_output_t::flags. */
#define BIO_SRD_OUTPUT_FLAGS_REASON_MASK 0x10

/*! Values of the signal status bits in bio_srd_output_t::flags.*/
enum bio_srd_output_flags_signal_status {
    BIO_SRD_OUTPUT_FLAGS_SIGNAL_STATUS_LOWER = 0x00,  /*!< Input falls into the lower signal status region. */
    BIO_SRD_OUTPUT_FLAGS_SIGNAL_STATUS_CENTER = 0x01, /*!< Input falls into the center signal status region. */
    BIO_SRD_OUTPUT_FLAGS_SIGNAL_STATUS_UPPER = 0x02,  /*!< Input falls into the upper signal status region. */
};

/*!
 * Values of the output reason bits in bio_srd_output_t::flags. The values are already bit-shifted to the bit position
 * of the output reason bit.
 */
enum bio_srd_output_flags_reason {
    BIO_SRD_OUTPUT_FLAGS_REASON_PERIODIC = 0x00, /*!< Output is generated because of a periodic update. */
    BIO_SRD_OUTPUT_FLAGS_REASON_CHANGE = 0x10,   /*!< Output is generated because of a signal status change. */
};

/*! Contains the configuration options of the Signal Range Detection Bio App. */
typedef struct {
    int32_t lower_threshold;              /*!< Lower threshold of the center signal status region in raw counts. */
    int32_t upper_threshold;              /*!< Upper threshold of the center signal status region in raw counts. The
                                               upper threshold must not be lower than the lower threshold. */
    uint8_t change_detection_samples_num; /*!< Minimum number of consecutive samples that need to fall into the new
                                               signal status region before the signal status change may trigger. For
                                               example, if this value is set to three, the signal status changes once
                                               four consecutive samples that fall into the same new signal status region
                                               have been received. */
    uint8_t reserved[3];                  /*!< Reserved for future use. Always set to zero when configuring the
                                               application. */
} bio_srd_configuration_t;

/*! Describes the output of the Signal Range Detection Bio App. */
typedef struct {
    uint8_t flags; /*!< Contains the signal status and the output reason. */
} bio_srd_output_t;

/*! Sensor signals provided to the Signal Range Detection Bio App. */
enum bio_srd_signal {
    BIO_SRD_SIGNAL_MAIN = 0, /*!< Signal to monitor. */

    BIO_SRD_SIGNAL_NUM /*!< Number of sensor signals provided to the Bio App. */
};

/*! @} */

/******************************************************************************
 *                            TYPE SIZE VALIDATION                            *
 ******************************************************************************/

M_STATIC_ASSERT_TYPE_SIZE(bio_srd_configuration_t, 12);
M_STATIC_ASSERT_TYPE_SIZE(bio_srd_output_t, 1);

#endif /* __BIO_SRD_TYPEDEFS_H__ */
