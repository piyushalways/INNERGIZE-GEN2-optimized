/******************************************************************************
 * Copyright © 2022 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

#ifndef __AS7058_RAW_APP_TYPEDEFS_H__
#define __AS7058_RAW_APP_TYPEDEFS_H__

/*!
 * \file       as7058_raw_app_typedefs.h
 * \authors    PKRN
 * \copyright  ams OSRAM
 * \addtogroup AS7058_RAW_APP Raw Data Application
 *
 * \brief The Raw Data application provides measurement data acquired using AS7058 (and optionally using an
 * accelerometer) to a host system for evaluation and algorithm development purposes. It also contains the output of the
 * AGC algorithm.
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

/*! Contains the configuration options of the AS7058 Raw Data application. */
typedef struct {
    uint8_t include_acc; /*!< Accelerometer data is included in the output when set to a non-zero value. */
} as7058_raw_app_configuration_t;

/******************************************************************************
 *                            TYPE SIZE VALIDATION                            *
 ******************************************************************************/

M_STATIC_ASSERT_TYPE_SIZE(as7058_raw_app_configuration_t, 1);

/*! @} */

#endif /* __AS7058_RAW_APP_TYPEDEFS_H__ */
