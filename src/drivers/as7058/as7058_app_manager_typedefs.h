/******************************************************************************
 * Copyright © 2022 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

#ifndef __AS7058_APP_MANAGER_TYPEDEFS_H__
#define __AS7058_APP_MANAGER_TYPEDEFS_H__

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

/*!
 * \file       as7058_app_manager_typedefs.h
 * \authors    PKRN
 * \copyright  ams OSRAM
 */

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include "as7058_app_manager_preprocessing.h"
#include "std_inc.h"

#ifndef AS7058_APPMGR_DISABLE_STREAM
#include "as7058_stream_app_ids.h"
#endif

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

/*!
 * \addtogroup AS7058_APPMGR_APPS Supported Vital Signs Applications
 *
 * The Application Manager supports the following Vital Signs Applications:
 *  - \ref AS7058_RAW_APP
 *  - \ref bio_hrm_b0
 *  - \ref bio_spo2_a0_group
 *  - \ref bio_srd_group
 *  - \ref AS7058_BIOZ_APP
 *  - \ref AS7058_EDA_APP
 *  - \ref bio_stream_group
 *  - \ref bio_rrm_a0_group
 *
 * The Application Manager provides a common API to all supported Vital Signs Applications. Each application is assigned
 * an ::as7058_appmgr_app_id identifier, which is used in the Application Manager APIs.
 *
 * @{ */

/*! Identifiers of Vital Signs Applications. */
enum as7058_appmgr_app_id {
    AS7058_APPMGR_APP_ID_RAW = 0, /*!< Identifies the Raw Data application. */
    AS7058_APPMGR_APP_ID_HRM_B0,  /*!< Identifies the HRM application. */
    AS7058_APPMGR_APP_ID_SPO2_A0, /*!< Identifies the SpO2 application. */
    AS7058_APPMGR_APP_ID_SRD,     /*!< Identifies the Signal Range Detection application. */
    AS7058_APPMGR_APP_ID_BIOZ,    /*!< Identifies the BioZ application. */
    AS7058_APPMGR_APP_ID_EDA,     /*!< Identifies the Electrodermal Activity application. */
    AS7058_APPMGR_APP_ID_STREAM,  /*!< Identifies the Streaming application. */
    AS7058_APPMGR_APP_ID_RRM_A0,  /*!< Identifies the Respiration Rate application. */

    AS7058_APPMGR_APP_ID_NUM, /*!< Number of Vital Signs Applications. */
};

/*! Type for ::as7058_appmgr_app_id. */
typedef uint8_t as7058_appmgr_app_id_t;

/*! Macro to create a application flag bitmask value with the bit for the given ::as7058_appmgr_app_id set. */
#define M_AS7058_APPMGR_APP_FLAG(app) (1 << (app))

/*!
 * \brief Application flags bitmasks.
 *
 * Use these definitions with bitwise operators to set, clear, or read the flag bit corresponding to a given Vital Signs
 * Application.
 */
enum as7058_appmgr_app_flag {
    AS7058_APPMGR_APP_FLAG_RAW = M_AS7058_APPMGR_APP_FLAG(AS7058_APPMGR_APP_ID_RAW),         /*!< Bitmask where the bit
                                                                                                  representing the Raw
                                                                                                  Data Streaming
                                                                                                  application is set. */
    AS7058_APPMGR_APP_FLAG_HRM_B0 = M_AS7058_APPMGR_APP_FLAG(AS7058_APPMGR_APP_ID_HRM_B0),   /*!< Bitmask where the bit
                                                                                                  representing the HRM
                                                                                                  application is set. */
    AS7058_APPMGR_APP_FLAG_SPO2_A0 = M_AS7058_APPMGR_APP_FLAG(AS7058_APPMGR_APP_ID_SPO2_A0), /*!< Bitmask where the bit
                                                                                                  representing the SpO2
                                                                                                  application is set. */
    AS7058_APPMGR_APP_FLAG_SRD = M_AS7058_APPMGR_APP_FLAG(AS7058_APPMGR_APP_ID_SRD),         /*!< Bitmask where the bit
                                                                                                  representing the
                                                                                                  Signal Range Detection
                                                                                                  application is set. */
    AS7058_APPMGR_APP_FLAG_BIOZ = M_AS7058_APPMGR_APP_FLAG(AS7058_APPMGR_APP_ID_BIOZ),       /*!< Bitmask where the bit
                                                                                                  representing the BioZ
                                                                                                  application is set. */
    AS7058_APPMGR_APP_FLAG_EDA = M_AS7058_APPMGR_APP_FLAG(AS7058_APPMGR_APP_ID_EDA),         /*!< Bitmask where the bit
                                                                                                  representing the EDA
                                                                                                  application is set. */
    AS7058_APPMGR_APP_FLAG_STREAM = M_AS7058_APPMGR_APP_FLAG(AS7058_APPMGR_APP_ID_STREAM),   /*!< Bitmask where the bit
                                                                                                  representing the
                                                                                                  Streaming application
                                                                                                  is set. */
    AS7058_APPMGR_APP_FLAG_RRM_A0 = M_AS7058_APPMGR_APP_FLAG(AS7058_APPMGR_APP_ID_RRM_A0),   /*!< Bitmask where the bit
                                                                                                  representing the
                                                                                                  Respiration Rate
                                                                                                  application is set. */
};

/*! @} */

/******************************************************************************
 *                            TYPE SIZE VALIDATION                            *
 ******************************************************************************/

M_STATIC_ASSERT_TYPE_SIZE(as7058_sub_sample_ids_t, 1);
M_STATIC_ASSERT_TYPE_SIZE(as7058_appmgr_app_id_t, 1);

#ifdef __cplusplus
}
#endif // __cplusplus

#endif /* __AS7058_APP_MANAGER_TYPEDEFS_H__ */
