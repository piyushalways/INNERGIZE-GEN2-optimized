/******************************************************************************
 * Copyright © 2022 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

#ifndef __BIO_SPO2_A0_TYPEDEFS_H__
#define __BIO_SPO2_A0_TYPEDEFS_H__

/*!
 * \file       bio_spo2_a0_typedefs.h
 * \authors    ARIT, PKRN
 * \copyright  ams OSRAM
 * \addtogroup bio_spo2_a0_group ams OSRAM SpO2 Algorithm
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

/*! The signal data type required by the SpO2 Bio App. */
#define BIO_SPO2_A0_SIGNAL_DATA_TYPE BIO_SIGNAL_SAMPLES_TYPE_U16

/*! Contains the configuration options of the SpO2 Bio App. */
typedef struct {
    uint16_t a;           /*!< Quadratic correction coefficient a. */
    uint16_t b;           /*!< Quadratic correction coefficient b. */
    uint16_t c;           /*!< Quadratic correction coefficient c. */
    uint16_t dc_comp_red; /*!< DC compensation for the red signal. */
    uint16_t dc_comp_ir;  /*!< DC compensation for the infrared signal. */
} bio_spo2_a0_configuration_t;

/*! Describes the output of the SpO2 Bio App. */
typedef struct {
    uint8_t status;      /*!< The value of the field is zero when the structure contains valid SpO2 data. It is one
                              when no result is present in the data. */
    uint8_t quality;     /*!< Contains the quality of the signal. The unit is 1%. */
    uint16_t spo2;       /*!< Contains the SpO2 measurement. The unit is 0.01%. */
    uint16_t heart_rate; /*!< Contains the heart rate. The unit is 0.1 bpm. */
    uint16_t pi;         /*!< Contains the Perfusion Index measurement. The unit is 0.01%. */
    uint16_t average_r;  /*!< Contains the average R-value. The unit is 10000. */

#ifdef BIO_SPO2_A0_EXTENDED_RESULT_STRUCT
    uint16_t reserved[4]; /*!< Reserved memory for backwards compatibility. Formerly AC/DC PPG components.*/
#endif

} bio_spo2_a0_output_t;

/*! Sensor signals provided to the SpO2 Bio App. */
enum bio_spo2_a0_signal {
    BIO_SPO2_A0_SIGNAL_PPG_RED = 0, /*!< Red PPG signal. */
    BIO_SPO2_A0_SIGNAL_PPG_IR = 1,  /*!< Infrared PPG signal. */
    BIO_SPO2_A0_SIGNAL_AMBIENT = 2, /*!< Ambient light signal. */

    BIO_SPO2_A0_SIGNAL_NUM /*!< Number of sensor signals provided to the Bio App. */
};

/*! @} */

/******************************************************************************
 *                            TYPE SIZE VALIDATION                            *
 ******************************************************************************/

M_STATIC_ASSERT_TYPE_SIZE(bio_spo2_a0_configuration_t, 10);
#ifdef BIO_SPO2_A0_EXTENDED_RESULT_STRUCT
M_STATIC_ASSERT_TYPE_SIZE(bio_spo2_a0_output_t, 18);
#else
M_STATIC_ASSERT_TYPE_SIZE(bio_spo2_a0_output_t, 10);
#endif /* OLD */
#endif /* __BIO_SPO2_A0_TYPEDEFS_H__ */
