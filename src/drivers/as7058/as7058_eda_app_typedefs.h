/******************************************************************************
 * Copyright © 2022 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

#ifndef __AS7058_EDA_APP_TYPEDEFS_H__
#define __AS7058_EDA_APP_TYPEDEFS_H__

/*!
 * \file       as7058_eda_app_typedefs.h
 * \authors    PKRN
 * \copyright  ams OSRAM
 * \addtogroup AS7058_EDA_APP EDA Application
 *
 * \brief The EDA application provides EDA measurements results acquired using the AS7058 analog front-end.
 *
 * @{
 */

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include "as7058_typedefs.h"
#include "bio_common.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

/*! Sensor signals provided to the AS7058 Electrodermal Activity application. */
enum as7058_eda_app_signal {
    AS7058_EDA_APP_SIGNAL_EDA_ALTERNATING = 0, /*!< Signal where EDA+ and EDA- samples are provided alternatingly. */
    AS7058_EDA_APP_SIGNAL_TEMPERATURE,         /*!< Temperature signal. */

    AS7058_EDA_APP_SIGNAL_NUM /*!< Number of sensor signals provided to the bio app. */
};

/*! Contains the configuration options of the AS7058 Electrodermal Activity application. */
typedef struct {
    as7058_eda_scaling_result_t scaling_result; /*!< Results of resistance scaling for the EDA application. */
    uint32_t eda_avg_num;                 /*!< Number of positive and negative EDA samples to average for a single EDA
                                               calculation. eda_avg_num positive EDA samples and eda_avg_num negative
                                               EDA samples are averaged. Must be at least 1. */
    uint32_t eda_drop_num;                /*!< Number of subsequent samples of positive and negative EDA samples to
                                               drop after an average has been calculated. eda_avg_num positive EDA
                                               samples and eda_avg_num negative EDA samples are dropped. This allows
                                               for sample rate reduction. */
    uint32_t temperature_delta_threshold; /*!< Temperature threshold in ADC counts for triggering a recalibration
                                               warning. Impedance scaling should be re-performed when
                                               ::AS7058_EDA_APP_OUTPUT_FLAGS_RECALIBRATION_WARNING is set in the flags
                                               field of ::as7058_eda_app_output_t. The warning is triggered when the
                                               current temperature is less than (scaling_results.temperature_adc -
                                               temperature_delta_threshold) or when the current temperature is greater
                                               than (scaling_results.temperature_adc + temperature_delta_threshold).
                                               */
} as7058_eda_app_configuration_t;

/*! Indicates that resistance scaling should be re-performed due to temperature change. */
#define AS7058_EDA_APP_OUTPUT_FLAGS_RECALIBRATION_WARNING 0x0001

/*! Contains the output of the AS7058 Electrodermal Activity application. */
typedef struct {
    uint32_t flags;              /*!< Status flags of the EDA application. The value of this field is either zero or
                                      ::AS7058_EDA_APP_OUTPUT_FLAGS_RECALIBRATION_WARNING.*/
    int32_t resistance;          /*!< Average of the positive and negative EDA resistance in ohm. */
    int32_t resistance_positive; /*!< Positive EDA resistance in ohm. */
    int32_t resistance_negative; /*!< Negative EDA resistance in ohm. */
} as7058_eda_app_output_t;

/*! Signal data type of the AS7058 Electrodermal Activity application. */
#define AS7058_EDA_APP_SIGNAL_DATA_TYPE BIO_SIGNAL_SAMPLES_TYPE_I32

/******************************************************************************
 *                            TYPE SIZE VALIDATION                            *
 ******************************************************************************/

M_STATIC_ASSERT_TYPE_SIZE(as7058_eda_app_configuration_t, 44);
M_STATIC_ASSERT_TYPE_SIZE(as7058_eda_app_output_t, 16);

/*! @} */

#endif /* __AS7058_EDA_APP_TYPEDEFS_H__ */
