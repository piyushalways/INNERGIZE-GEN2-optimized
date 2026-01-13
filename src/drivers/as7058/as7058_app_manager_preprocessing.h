/******************************************************************************
 * Copyright © 2023 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

#ifndef __AS7058_APP_MANAGER_PREPROCESSING_H__
#define __AS7058_APP_MANAGER_PREPROCESSING_H__

/*!
 * \file       as7058_app_manager_preprocessing.h
 * \authors    ARIT
 * \copyright  ams OSRAM
 * \addtogroup AS7058_APPMGR_PREPROCESSING Supported Signal Sample Preprocessing Feature
 *
 * Before signal samples are passed to Vital Signs Applications, the AS7058 Application Manager can perform
 * preprocessing operations on the samples.
 *
 * @{
 */

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include "std_inc.h"
#include "as7058_typedefs.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

/*! Identifiers of the signal sample pre-processing features. */
enum as7058_appmgr_preprocessing_id {
    AS7058_APPMGR_PREPROCESSING_ID_PD_OFFSET_COMPENSATION = 0, /*!< Represents PD offset compensation. */
};

/*! Type for ::as7058_appmgr_preprocessing_id_t. */
typedef uint8_t as7058_appmgr_preprocessing_id_t;

/*!
 * \brief Signal sample pre-processing features bitmasks.
 *
 * Use these definitions with bitwise operators to set, clear, or read the flag bit corresponding to a given signal
 * sample pre-processing feature.
 */
enum as7058_appmgr_preprocessing_flag {
    AS7058_APPMGR_PREPROCESSING_FLAG_PD_OFFSET_COMPENSATION = 0x00000001, /*!< Bitmask where the bit representing the PD
                                                                               offset compensation preprocessing feature
                                                                               is set. */
};

/*! Configuration structure for ::AS7058_APPMGR_PREPROCESSING_ID_PD_OFFSET_COMPENSATION. */
typedef struct {
    uint32_t compensation_table_ppg1[AS7058_PD_OFFSET_CALIBRATION_COMPENSATION_TABLE_ELEMENTS_NUM]; /*!< Compensation
                                                                                                         value table for
                                                                                                         PPG modulator
                                                                                                         1. */
    uint32_t compensation_table_ppg2[AS7058_PD_OFFSET_CALIBRATION_COMPENSATION_TABLE_ELEMENTS_NUM]; /*!< Compensation
                                                                                                         value table for
                                                                                                         PPG modulator
                                                                                                         2. */
} as7058_appmgr_preprocessing_configuration_pd_offset_compensation_t;

/*! @} */

/******************************************************************************
 *                            TYPE SIZE VALIDATION                            *
 ******************************************************************************/

M_STATIC_ASSERT_TYPE_SIZE(as7058_appmgr_preprocessing_id_t, 1);
M_STATIC_ASSERT_TYPE_SIZE(as7058_appmgr_preprocessing_configuration_pd_offset_compensation_t, 120);

#endif /* __AS7058_APP_MANAGER_PREPROCESSING_H__ */
