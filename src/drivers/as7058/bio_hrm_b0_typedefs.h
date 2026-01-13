/******************************************************************************
 * Copyright © 2023 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

#ifndef __BIO_HRM_B0_TYPEDEFS_H__
#define __BIO_HRM_B0_TYPEDEFS_H__

/*!
 * \addtogroup bio_hrm_b0
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

/*! The signal data type required by the HRM Bio App. */
#define BIO_HRM_B0_SIGNAL_DATA_TYPE BIO_SIGNAL_SAMPLES_TYPE_I32

/*! Maximum number of PRV data items in a single ::bio_hrm_b0_output_t structure. */
#define BIO_HRM_B0_OUTPUT_PRV_DATA_NUM 5

/*! Contains the configuration options of the HRM Bio App. */
typedef struct {
    uint8_t enable_prv;             /*!< PRV data is included in the output when set to one. It is not included in the
                                         output when set to zero. */
    uint8_t reserved;               /*!< Reserved for future use. Must be set to zero. */
    uint8_t alpha_hr;               /*!< Smoothing coefficient for the heart rate value. Must be at least zero (no
                                         smoothing) and less than 100 (heavy smoothing). */
    uint8_t alpha_acc;              /*!< Smoothing coefficient for the processing of accelerometer inputs. Must be at
                                         least zero (no smoothing) and less than 100 (heavy smoothing). */
    int32_t compensation_threshold; /*!< Threshold in ADC counts for detection and correction of jumps in the green PPG
                                         signal. Compensation is disabled when set to zero. Must otherwise be at least
                                         zero. */
} bio_hrm_b0_configuration_t;

/*! Motion levels detected by the HRM Bio App. */
enum bio_hrm_b0_motion_level {
    BIO_HRM_B0_MOTION_LEVEL_UNKNOWN = 0, /*!< Motion level of the subject is unknown. */
    BIO_HRM_B0_MOTION_LEVEL_SEDENTARY,   /*!< Subject is sedentary. */
    BIO_HRM_B0_MOTION_LEVEL_MOVING,      /*!< Subject is moving. */
};

/*! Type for ::bio_hrm_b0_motion_level. */
typedef uint8_t bio_hrm_b0_motion_level_t;

/*! Describes the output of the HRM Bio App. */
typedef struct {
    uint16_t heart_rate;                             /*!< Contains the heart rate. The unit is 0.1 bpm. */
    uint8_t quality;                                 /*!< Contains information about the quality of the green PPG
                                                          signal. A value of 100 means best quality. */
    bio_hrm_b0_motion_level_t motion_level;          /*!< Motion level of the subject. */
    uint16_t prv_ms[BIO_HRM_B0_OUTPUT_PRV_DATA_NUM]; /*!< Contains PRV data. The unit is milliseconds. */
    uint8_t prv_ms_num;                              /*!< Contains the number of prv_ms fields that are used. */
    uint8_t reserved;                                /*!< Reserved field. Do not read. */
} bio_hrm_b0_output_t;

/*! Sensor signals provided to the HRM Bio App. */
enum bio_hrm_b0_signal {
    BIO_HRM_B0_SIGNAL_GREEN = 0,   /*!< Green PPG signal. */
    BIO_HRM_B0_SIGNAL_AMBIENT = 1, /*!< Ambient signal. */
    BIO_HRM_B0_SIGNAL_NUM,         /*!< Number of sensor signals provided to the Bio App. */
};

/*! @} */

/******************************************************************************
 *                            TYPE SIZE VALIDATION                            *
 ******************************************************************************/

M_STATIC_ASSERT_TYPE_SIZE(bio_hrm_b0_configuration_t, 8);
M_STATIC_ASSERT_TYPE_SIZE(bio_hrm_b0_output_t, 16);

#endif /* __BIO_HRM_B0_TYPEDEFS_H__ */
