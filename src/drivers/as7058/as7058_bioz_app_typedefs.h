/******************************************************************************
 * Copyright © 2022 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

#ifndef __AS7058_BIOZ_APP_TYPEDEFS_H__
#define __AS7058_BIOZ_APP_TYPEDEFS_H__

/*!
 * \file       as7058_bioz_app_typedefs.h
 * \authors    PKRN
 * \copyright  ams OSRAM
 * \addtogroup AS7058_BIOZ_APP BioZ Application
 *
 * \brief The BioZ application provides BioZ measurements results acquired using the AS7058 analog front-end.
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

/*! Indicates that no valid phase angle value is available. */
#define AS7058_BIOZ_APP_IMP_POLAR_INVALID_PHASE INT32_MAX

/*! Sensor signals provided to the AS7058 BioZ application. */
enum as7058_bioz_app_signal {
    AS7058_BIOZ_APP_SIGNAL_NUM = 0, /*!< Number of sensor signals provided to the bio app. */
};

/*! Indices of the different known impedances in the ::as7058_bioz_app_configuration_t::ref_known_imps array. */
enum as7058_bioz_app_configuration_known_imps_index {
    AS7058_BIOZ_APP_CONFIGURATION_KNOWN_IMPS_INDEX_BODY = 0, /*!< Index for the known body impedance. */
    AS7058_BIOZ_APP_CONFIGURATION_KNOWN_IMPS_INDEX_WRIST,    /*!< Index for the known wrist impedance. */
    AS7058_BIOZ_APP_CONFIGURATION_KNOWN_IMPS_INDEX_FINGER,   /*!< Index for the known finger impedance. */
    AS7058_BIOZ_APP_CONFIGURATION_KNOWN_IMPS_INDEX_NUM,      /*!< Number of known impedances indices. */
};

/*! Represents an impedance value in polar representation. */
typedef struct {
    uint32_t magnitude; /*!< Magnitude of the impedance scaled by 1000. For example, a magnitude of 15.2 is represented
                             using value 15200. */
    int32_t phase;      /*!< Phase angle of the impedance in degrees scaled by 1000. For example, 15.2 degrees is
                             represented using value 15200. When used inside an ::as7058_bioz_app_output_t structure,
                             value ::AS7058_BIOZ_APP_IMP_POLAR_INVALID_PHASE indicates that no valid phase angle value
                             is available. */
} as7058_bioz_app_imp_polar_t;

/*! Contains the configuration options of the AS7058 BioZ application. */
typedef struct {
    as7058_bioz_meas_result_t ref_meas_result; /*!< Results of the measurement of the reference BioZ sample. */
    as7058_bioz_app_imp_polar_t ref_known_imps[AS7058_BIOZ_APP_CONFIGURATION_KNOWN_IMPS_INDEX_NUM]; /*!< Known impedance
                                                                                                         values of the
                                                                                                         used reference
                                                                                                         BioZ sample. */
    uint8_t input_drop_num; /*!< Number of measurement data inputs to ignore after one measurement data input has been
                                 received. The rate of generated app outputs can be controlled using this setting. For
                                 example, if this field is set to 2, every third measurement data input is processed. */
    uint8_t reserved[3];    /*!< Padding bytes, reserved for future use. Always set to zero. */
    as7058_bioz_app_imp_polar_t safety_protection_imp; /*!< Known impedance value of the safety protection circuit. */
} as7058_bioz_app_configuration_t;

/*! Contains the output of the AS7058 BioZ application. */
typedef struct {
    as7058_bioz_app_imp_polar_t imp_body;   /*!< Body impedance. */
    as7058_bioz_app_imp_polar_t imp_wrist;  /*!< Wrist impedance. */
    as7058_bioz_app_imp_polar_t imp_finger; /*!< Finger impedance. */
} as7058_bioz_app_output_t;

/******************************************************************************
 *                            TYPE SIZE VALIDATION                            *
 ******************************************************************************/

M_STATIC_ASSERT_TYPE_SIZE(as7058_bioz_app_configuration_t, 100);
M_STATIC_ASSERT_TYPE_SIZE(as7058_bioz_app_output_t, 24);

/*! @} */

#endif /* __AS7058_BIOZ_APP_TYPEDEFS_H__ */
