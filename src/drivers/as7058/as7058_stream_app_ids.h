/******************************************************************************
 * Copyright © 2023 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

#ifndef __AS7058_STREAM_APP_IDS_H__
#define __AS7058_STREAM_APP_IDS_H__

/*!
 * \file       as7058_stream_app_ids.h
 * \authors    ARIT
 * \copyright  ams OSRAM
 * \addtogroup AS7058_APPMGR_STREAM_IDS Supported Streaming App Item IDs
 *
 * @{
 */

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

/*! Identifiers of streaming app items. */
enum as7058_appmgr_stream_app_ids {
    AS7058_APPMGR_STREAM_APP_ID_FIFO = 0,                   /*!< FIFO data stream. */
    AS7058_APPMGR_STREAM_APP_ID_AGC = 1,                    /*!< AGC statuses. */
    AS7058_APPMGR_STREAM_APP_ID_ACC = 2,                    /*!< Accelerometer data. */
    AS7058_APPMGR_STREAM_APP_ID_SENSOR_EVENTS = 3,          /*!< Sensor events. */
    AS7058_APPMGR_STREAM_APP_ID_EXT_EVENTS = 4,             /*!< External events. */
    AS7058_APPMGR_STREAM_APP_ID_SAMPLES_PPG1_SUB1 = 5,      /*!< Samples of PPG modulator 1, sub-sample 1. */
    AS7058_APPMGR_STREAM_APP_ID_SAMPLES_PPG1_SUB2 = 6,      /*!< Samples of PPG modulator 1, sub-sample 2. */
    AS7058_APPMGR_STREAM_APP_ID_SAMPLES_PPG1_SUB3 = 7,      /*!< Samples of PPG modulator 1, sub-sample 3. */
    AS7058_APPMGR_STREAM_APP_ID_SAMPLES_PPG1_SUB4 = 8,      /*!< Samples of PPG modulator 1, sub-sample 4. */
    AS7058_APPMGR_STREAM_APP_ID_SAMPLES_PPG1_SUB5 = 9,      /*!< Samples of PPG modulator 1, sub-sample 5. */
    AS7058_APPMGR_STREAM_APP_ID_SAMPLES_PPG1_SUB6 = 10,     /*!< Samples of PPG modulator 1, sub-sample 6. */
    AS7058_APPMGR_STREAM_APP_ID_SAMPLES_PPG1_SUB7 = 11,     /*!< Samples of PPG modulator 1, sub-sample 7. */
    AS7058_APPMGR_STREAM_APP_ID_SAMPLES_PPG1_SUB8 = 12,     /*!< Samples of PPG modulator 1, sub-sample 8. */
    AS7058_APPMGR_STREAM_APP_ID_SAMPLES_PPG2_SUB1 = 13,     /*!< Samples of PPG modulator 2, sub-sample 1. */
    AS7058_APPMGR_STREAM_APP_ID_SAMPLES_PPG2_SUB2 = 14,     /*!< Samples of PPG modulator 2, sub-sample 2. */
    AS7058_APPMGR_STREAM_APP_ID_SAMPLES_PPG2_SUB3 = 15,     /*!< Samples of PPG modulator 2, sub-sample 3. */
    AS7058_APPMGR_STREAM_APP_ID_SAMPLES_PPG2_SUB4 = 16,     /*!< Samples of PPG modulator 2, sub-sample 4. */
    AS7058_APPMGR_STREAM_APP_ID_SAMPLES_PPG2_SUB5 = 17,     /*!< Samples of PPG modulator 2, sub-sample 5. */
    AS7058_APPMGR_STREAM_APP_ID_SAMPLES_PPG2_SUB6 = 18,     /*!< Samples of PPG modulator 2, sub-sample 6. */
    AS7058_APPMGR_STREAM_APP_ID_SAMPLES_PPG2_SUB7 = 19,     /*!< Samples of PPG modulator 2, sub-sample 7. */
    AS7058_APPMGR_STREAM_APP_ID_SAMPLES_PPG2_SUB8 = 20,     /*!< Samples of PPG modulator 2, sub-sample 8. */
    AS7058_APPMGR_STREAM_APP_ID_SAMPLES_ECG_SEQ1_SUB1 = 21, /*!< Samples of ECG modulator, sequence 1, sub-sample 1. */
    AS7058_APPMGR_STREAM_APP_ID_SAMPLES_ECG_SEQ1_SUB2 = 22, /*!< Samples of ECG modulator, sequence 1, sub-sample 2. */
    AS7058_APPMGR_STREAM_APP_ID_SAMPLES_ECG_SEQ2_SUB1 = 23, /*!< Samples of ECG modulator, sequence 2, sub-sample 1. */

    AS7058_APPMGR_STREAM_APP_ID_NUM = 24, /*!< Number of supported streaming app item IDs. */
};

/*! @} */

#endif /* __AS7058_STREAM_APP_IDS_H__ */
