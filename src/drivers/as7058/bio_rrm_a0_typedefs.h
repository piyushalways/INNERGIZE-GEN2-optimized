/******************************************************************************
 * Copyright © 2022 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

#ifndef __BIO_RRM_A0_TYPEDEFS_H__
#define __BIO_RRM_A0_TYPEDEFS_H__

/*!
 * \file      bio_rrm_a0_typedefs.h
 * \authors   RSIN
 * \copyright ams OSRAM
 * \addtogroup bio_rrm_a0_group Respiration Rate Bio App
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

/*! The signal data type required by the Respiration Rate Bio App. */
#define BIO_RRM_A0_SIGNAL_DATA_TYPE BIO_SIGNAL_SAMPLES_TYPE_I32

/*! Output data of the Respiration Rate Bio App. */
typedef struct {
    uint16_t respiratory_rate; /*!< Respiratory rate value is expressed in beats per minute multiplied by 100. Typical
                                    resting respiratory rate value for an adult is 12 to 20. */
    uint8_t confidence;        /*!< Confidence value associated with the respiratory rate value, which gives a hint of
                                    the certainty about the found respiratory rate. It varies between 0 and 100. Value
                                    100 is for the maximum certainty. */
    uint8_t reserved;          /*!< Reserved for future use. */
} bio_rrm_a0_output_t;

/*! Sensor signals provided to the Respiration Rate Bio App. */
enum bio_rrm_a0_signal {
    BIO_RRM_A0_SIGNAL_PPG = 0, /*!< PPG signal that is used for respiration rate monitoring. */
    BIO_RRM_A0_SIGNAL_NUM,     /*!< Number of sensor signals provided to the Bio App. */
};

/*! @} */

/******************************************************************************
 *                            TYPE SIZE VALIDATION                            *
 ******************************************************************************/

M_STATIC_ASSERT_TYPE_SIZE(bio_rrm_a0_output_t, 4);

#endif /* __BIO_RRM_A0_TYPEDEFS_H__ */
