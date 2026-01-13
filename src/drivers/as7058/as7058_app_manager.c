/******************************************************************************
 * Copyright © 2022 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include <string.h>

#include "as7058_app_manager.h"
#include "as7058_app_manager_version.h"

#include "as7058_extract2.h"
#include "bio_common.h"


#define AS7058_APPMGR_DISABLE_SPO2_A0 1
#define AS7058_APPMGR_DISABLE_RRM_A0 1
#define AS7058_APPMGR_DISABLE_HRM_B0 1



#ifndef AS7058_APPMGR_DISABLE_RAW
#include "as7058_raw_app.h"
#endif
#ifndef AS7058_APPMGR_DISABLE_HRM_B0
#include "bio_hrm_b0.h"
#endif
#ifndef AS7058_APPMGR_DISABLE_SPO2_A0
#include "bio_spo2_a0.h"
#endif
#ifndef AS7058_APPMGR_DISABLE_SRD
#include "bio_srd.h"
#endif
#ifndef AS7058_APPMGR_DISABLE_BIOZ
#include "as7058_bioz_app.h"
#endif
#ifndef AS7058_APPMGR_DISABLE_EDA
#include "as7058_eda_app.h"
#endif
#ifndef AS7058_APPMGR_DISABLE_STREAM
#include "bio_stream.h"
#endif
#ifndef AS7058_APPMGR_DISABLE_RRM_A0
#include "bio_rrm_a0.h"
#endif

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

#ifndef AS7058_APPMGR_FUNC_DEFN
/*! Preprocessor macro that is placed in front of every definition of a public function with external linkage. By
 *  default this macro is defined to expand to nothing, but it can be defined externally. Example use cases include
 *  setting keywords. */
#define AS7058_APPMGR_FUNC_DEFN
#endif

/*!
 * \brief Size of the converted samples buffer of a signal in bytes. If all converted samples of a signal do not fit in
 *        the buffer, the set input function of the app is called multiple times to provide the samples in batches.
 */
#define AS7058_APPMGR_CONVERTED_SAMPLES_SIZE_PER_SIGNAL 256

/*! Maximum number of unsigned 16-bit samples that can be stored in a converted samples buffer. */
#define AS7058_APPMGR_CONVERTED_SAMPLES_MAX_U16 ((AS7058_APPMGR_CONVERTED_SAMPLES_SIZE_PER_SIGNAL) / sizeof(uint16_t))

/*! Maximum number of unsigned 32-bit samples that can be stored in a converted samples buffer. */
#define AS7058_APPMGR_CONVERTED_SAMPLES_MAX_U32 ((AS7058_APPMGR_CONVERTED_SAMPLES_SIZE_PER_SIGNAL) / sizeof(uint32_t))

/*! Maximum number of signed 32-bit samples that can be stored in a converted samples buffer. */
#define AS7058_APPMGR_CONVERTED_SAMPLES_MAX_I32 ((AS7058_APPMGR_CONVERTED_SAMPLES_SIZE_PER_SIGNAL) / sizeof(int32_t))

/*! Maximum number of signals that can be used by a bio app. */
#define AS7058_APPMGR_MAX_APP_SIGNAL_NUM 3

/*! Indicates that AGC is not enabled for a given channel. */
#define AS7058_APPMGR_AGC_MAPPING_DISABLED UINT8_MAX

/*! Chip-specific channel identifier that represents a disabled channel. */
#define AS7058_APPMGR_CHANNEL_ID_DISABLED AS7058_SUB_SAMPLE_ID_DISABLED

/*! Lower bound of the chip-specific range of valid channel identifiers. */
#define AS7058_APPMGR_CHANNEL_ID_FIRST AS7058_SUB_SAMPLE_ID_PPG1_SUB1

/*! Upper bound of the chip-specific range of valid channel identifiers. */
#define AS7058_APPMGR_CHANNEL_ID_LAST AS7058_SUB_SAMPLE_ID_ECG_SEQ2_SUB1

/*! Lower bound of the chip-specific range of valid channel identifiers that support AGC. */
#define AS7058_APPMGR_CHANNEL_ID_AGC_FIRST AS7058_SUB_SAMPLE_ID_PPG1_SUB1

/*! Upper bound of the chip-specific range of valid channel identifiers that support AGC. */
#define AS7058_APPMGR_CHANNEL_ID_AGC_LAST AS7058_SUB_SAMPLE_ID_PPG2_SUB8

/*! Chip-specific number of channels that support AGC. */
#define AS7058_APPMGR_CHANNEL_AGC_NUM ((AS7058_APPMGR_CHANNEL_ID_AGC_LAST) - (AS7058_APPMGR_CHANNEL_ID_AGC_FIRST) + 1)

/*! Chip-specific size of an acquired sample in bits before preprocessing. */
#define AS7058_APPMGR_SAMPLE_BIT_SIZE 20

/*! Chip-specific maximum value of an acquired sample before preprocessing. */
#define AS7058_APPMGR_SAMPLE_MAX ((1 << (AS7058_APPMGR_SAMPLE_BIT_SIZE)) - 1)

/*! Magic number used in ::g_agc_statuses_num when the number of AGC statuses is not yet known. */
#define AS7058_APPMGR_AGC_STATUSES_NUM_UNKNOWN 0xFF

/*! Chip-specific number of PD offset current bits controlled by SAR. SAR controls the most significant bits. */
#define AS7058_APPMGR_PD_OFFSET_SAR_BITS_NUM 4

/*! Chip-specific number of PD offset current bits not controlled by SAR. SAR controls the most significant bits. */
#define AS7058_APPMGR_PD_OFFSET_PROGRAMMABLE_BITS_NUM 4

/*! Chip-specific bitmask for the non-SAR-controlled bits of the PD offset current. */
#define AS7058_APPMGR_PD_OFFSET_PROGRAMMABLE_BITS_MASK ((uint8_t)0x0F)

/*!
 * \brief Chip-specific maximum value of a PD offset compensation calibration table entry.
 *
 * The calibration table has 15 entries. The AS7058 Chip Library calculates each entry by performing two measurements
 * and by adding the difference of the two measurements to the preceding entry of the calibration table. The maximum
 * value of an individual measurement is ::AS7058_APPMGR_SAMPLE_MAX and the minimum value of an individual measurement
 * is zero, i.e. the maximum value of the difference is ::AS7058_APPMGR_SAMPLE_MAX. If the difference of all 15
 * calibration tables entries is ::AS7058_APPMGR_SAMPLE_MAX, the entry of the calibration table at index 14 has this
 * value.
 */
#define AS7058_APPMGR_PD_OFFSET_COMPENSATION_CALIBRATION_TABLE_ENTRY_MAX                                               \
    ((AS7058_APPMGR_SAMPLE_MAX) * (AS7058_PD_OFFSET_CALIBRATION_COMPENSATION_TABLE_ELEMENTS_NUM))

/*! Chip-specific bitmask for the ADC value in sample items of the streaming app. */
#define AS7058_APPMGR_STREAM_APP_SAMPLE_ADC_VALUE_BITS_MASK ((uint32_t)0xFFFFFF)

/*! Chip-specific value for left-shifting the 8-bit PD offset in sample items of the streaming app. */
#define AS7058_APPMGR_STREAM_APP_SAMPLE_PD_OFFSET_BITS_SHIFT 24

/*! States of the Application Manager. */
typedef enum {
    AS7058_APPMGR_STATE_UNINITIALIZED = 0, /*!< Uninitialized state. */
    AS7058_APPMGR_STATE_CONFIGURATION,     /*!< Configuration state. */
    AS7058_APPMGR_STATE_PROCESSING         /*!< Processing state. */
} as7058_appmgr_state_t;

/*!
 * \brief Chip-specific type which is used to store a sample internally in the Application Manager. It is also used to
 *        store preprocessed samples, i.e. values of this type may be larger than ::AS7058_APPMGR_SAMPLE_MAX.
 */
typedef uint32_t as7058_appmgr_sample_t;

/*! Metadata of a sample. */
typedef struct {
    struct {
        uint8_t pd_offset_current_valid : 1;
        uint8_t led_current_valid : 1;
    } flags;
    uint8_t pd_offset_current; /*!< PD offset current register value when the sample was acquired. */
    uint8_t led_current;       /*!< LED current register value when the sample was acquired. */
} as7058_appmgr_sample_metadata_t;

/*! Holds a single excess sample of a signal. */
typedef struct {
    uint8_t has_data;                         /*!< Is non-zero when an excess sample is stored. */
    as7058_appmgr_sample_t sample;            /*!< Sample value. */
    as7058_appmgr_sample_metadata_t metadata; /*!< Sample metadata. */
} as7058_appmgr_excess_sample_t;

/*! Definition of a Vital Signs Application. */
typedef struct {
    err_code_t (*p_initialize)(void);                           /*!< Function called by ::as7058_appmgr_initialize. */
    err_code_t (*p_shutdown)(void);                             /*!< Function called by ::as7058_appmgr_shutdown. */
    err_code_t (*p_configure)(const void *, uint8_t);           /*!< Function called by
                                                                     ::as7058_appmgr_configure_app. */
    err_code_t (*p_start)(const uint32_t *, uint8_t, uint32_t); /*!< Function called by
                                                                     ::as7058_appmgr_start_processing. */
    err_code_t (*p_stop)(void);                                 /*!< Function called by
                                                                     ::as7058_appmgr_stop_processing. */
    err_code_t (*p_set_input)(bio_signal_samples_type_t, const bio_signal_samples_t *, const agc_status_t *const *,
                              uint8_t, const vs_acc_data_t *, uint8_t,
                              bio_execution_status_t *); /*!< Function called by ::as7058_appmgr_set_input. */
    err_code_t (*p_execute)(bio_output_status_t *);      /*!< Function called by ::as7058_appmgr_execute. */
    err_code_t (*p_get_output)(void *, uint16_t *);      /*!< Function called by ::as7058_appmgr_get_output. */
    as7058_sub_sample_ids_t *p_signal_mapping;           /*!< Pointer to the begin of the array containing the signal
                                                              mapping. The size of the array must be ::signals_num. */
    as7058_appmgr_excess_sample_t *p_excess_samples;     /*!< Pointer to the begin of the array containing the excess
                                                              sample storage. The size of the array must be
                                                              ::signals_num. */
    bio_signal_samples_type_t data_type;                 /*!< Signal data type expected by the app. */
    uint8_t signals_num;                                 /*!< Number of signals used by the app. */
    uint32_t excluded_apps;                              /*!< Flags of apps that cannot be enabled concurrently with
                                                              this app, see ::as7058_appmgr_app_flag. */
    uint32_t *p_enabled_preprocessing;                   /*!< Flags of the enabled preprocessing features, see
                                                              ::as7058_appmgr_preprocessing_flag. Can be NULL if
                                                              preprocessing features should not be supported for this
                                                              app. */
    as7058_appmgr_sample_metadata_t *p_last_metadata;    /*!< Pointer to the begin of the array containing the metadata
                                                              of the samples that were last passed to the set input
                                                              function of the app. One metadata instance is stored per
                                                              channel, i.e. the size of the array must be ::signals_num.
                                                              All samples of a channel passed to the set input function
                                                              at once have the same metadata. */
    uint8_t *p_last_metadata_valid;                      /*!< Pointer to a bitfield indicating whether the stored last
                                                              metadata of channel is valid. Bit 0 corresponds to signal
                                                              0. The stored metadata of a channel is valid when the
                                                              corresponding bit is set. */
} as7058_appmgr_app_definition_t;

/*!
 * \brief Application input buffer for different sample input data types. Can only be used for a single data type at a
 *        time.
 */
typedef union {
    uint16_t u16[AS7058_APPMGR_MAX_APP_SIGNAL_NUM][AS7058_APPMGR_CONVERTED_SAMPLES_MAX_U16]; /*!< Buffer for unsigned
                                                                                                  16-bit application
                                                                                                  input. */
    uint32_t u32[AS7058_APPMGR_MAX_APP_SIGNAL_NUM][AS7058_APPMGR_CONVERTED_SAMPLES_MAX_U32]; /*!< Buffer for unsigned
                                                                                                 32-bit application
                                                                                                 input. */
    int32_t i32[AS7058_APPMGR_MAX_APP_SIGNAL_NUM][AS7058_APPMGR_CONVERTED_SAMPLES_MAX_I32];  /*!< Buffer for signed
                                                                                                  32-bit application
                                                                                                  input. */
} as7058_appmgr_converted_samples_t;

/*! Definition of the internally used application IDs. They are only defined for applications that have not been
 *  disabled at compile-time. The IDs are a contigious sequence of integers. */
enum as7058_appmgr_internal_app_id {
#ifndef AS7058_APPMGR_DISABLE_RAW
    AS7058_APPMGR_INTERNAL_APP_ID_RAW, /*!< Internally identifies the Raw Data application. */
#endif
#ifndef AS7058_APPMGR_DISABLE_HRM_B0
    AS7058_APPMGR_INTERNAL_APP_ID_HRM_B0, /*!< Internally identifies the HRM application. */
#endif
#ifndef AS7058_APPMGR_DISABLE_SPO2_A0
    AS7058_APPMGR_INTERNAL_APP_ID_SPO2_A0, /*!< Internally identifies the SpO2 application. */
#endif
#ifndef AS7058_APPMGR_DISABLE_SRD
    AS7058_APPMGR_INTERNAL_APP_ID_SRD, /*!< Internally identifies the Signal Range Detection application. */
#endif
#ifndef AS7058_APPMGR_DISABLE_BIOZ
    AS7058_APPMGR_INTERNAL_APP_ID_BIOZ, /*!< Internally identifies the BioZ application. */
#endif
#ifndef AS7058_APPMGR_DISABLE_EDA
    AS7058_APPMGR_INTERNAL_APP_ID_EDA, /*!< Internally identifies the Electrodermal Activity application. */
#endif
#ifndef AS7058_APPMGR_DISABLE_STREAM
    AS7058_APPMGR_INTERNAL_APP_ID_STREAM, /*!< Internally identifies the Streaming application. */
#endif
#ifndef AS7058_APPMGR_DISABLE_RRM_A0
    AS7058_APPMGR_INTERNAL_APP_ID_RRM_A0, /*!< Internally identifies the Respiration Rate application. */
#endif
    AS7058_APPMGR_INTERNAL_APP_ID_NUM, /*!< Number of apps that have not been disabled at compile-time. */
};

/*! Type for ::as7058_appmgr_internal_app_id. */
typedef uint8_t as7058_appmgr_internal_app_id_t;

/*! Chip-specific type used to store the result of sample extraction. */
typedef as7058_extract2_sub_sample_samples_t as7058_appmgr_extract_result_t;

/*! Converts an ID value to a flag value suitable for a bitfield. */
#define M_ID_TO_FLAG(id) (1 << (id))

/*! Returns whether the flag corresponding to an ID is set in a bitfield. */
#define M_ID_SET_IN_BITFIELD(id, bitfield) (M_ID_TO_FLAG((id)) & (bitfield))

/*! Returns whether the app with a given ::as7058_appmgr_internal_app_id is enabled. */
#define M_INTERNAL_APP_ID_IS_ENABLED(id) M_ID_SET_IN_BITFIELD((id), g_enabled_apps)

/*! Checks whether an ::as7058_appmgr_app_id is valid. */
#define M_CHECK_PUBLIC_APP_ID(app) M_CHECK_ARGUMENT_LOWER((app), AS7058_APPMGR_APP_ID_NUM)

/*! Checks whether the Application Manager is in the given state. */
#define M_CHECK_STATE(expected)                                                                                        \
    do {                                                                                                               \
        if (g_state != (expected)) {                                                                                   \
            return ERR_PERMISSION;                                                                                     \
        }                                                                                                              \
    } while (0)

/*! Checks whether the Application Manager is not in the given state. */
#define M_CHECK_STATE_NOT(expected)                                                                                    \
    do {                                                                                                               \
        if ((expected) == g_state) {                                                                                   \
            return ERR_PERMISSION;                                                                                     \
        }                                                                                                              \
    } while (0)

/*!
 * \brief Checks whether a value evaluates to true and returns ::ERR_CONFIG otherwise. Intended to be used for
 *        validating ::g_app_table at runtime.
 */
#define M_CHECK_APP_DEFINITION(value)                                                                                  \
    do {                                                                                                               \
        if (!(value)) {                                                                                                \
            return ERR_CONFIG;                                                                                         \
        }                                                                                                              \
    } while (0)

/******************************************************************************
 *                            FORWARD DECLARATIONS                            *
 ******************************************************************************/

#ifndef AS7058_APPMGR_DISABLE_RAW
static err_code_t handle_raw_app_start(const uint32_t *p_signal_sample_periods_us, uint8_t signal_num,
                                       uint32_t acc_sample_period_us);
#endif

#ifndef AS7058_APPMGR_DISABLE_STREAM
static err_code_t handle_bio_stream_start(const uint32_t *p_signal_sample_periods_us, uint8_t signal_num,
                                          uint32_t acc_sample_period_us);
#endif

/******************************************************************************
 *                                  GLOBALS                                   *
 ******************************************************************************/

/*! State of the Application Manager. */
static volatile as7058_appmgr_state_t g_state = AS7058_APPMGR_STATE_UNINITIALIZED;

/*! Bitfield storing which apps are enabled. It stores ::as7058_appmgr_internal_app_id values converted to flags using
 *  ::M_ID_TO_FLAG. */
static uint32_t g_enabled_apps;

/*!
 * \brief Bitfield storing which signal sample preprocessing features are configured. (see
 * ::as7058_appmgr_preprocessing_flag)
 */
static uint32_t g_configured_preprocessing;

/*!
 * \brief Array containing the index of the AGC status for each channel of the chip that supports AGC. This index is
 *        used to look up the corresponding AGC status in the p_agc_statuses array provided to
 *        ::as7058_appmgr_set_input. When AGC is disabled for a channel, this array contains
 *        ::AS7058_APPMGR_AGC_MAPPING_DISABLED at the corresponding index.
 */
static uint8_t g_agc_mapping[AS7058_APPMGR_CHANNEL_AGC_NUM];

#ifndef AS7058_APPMGR_DISABLE_HRM_B0
/*! Signal mapping configuration for the HRM app. */
static as7058_sub_sample_ids_t g_signal_mapping_hrm[BIO_HRM_B0_SIGNAL_NUM];
/*! Excess sample storage for the HRM app. */
static as7058_appmgr_excess_sample_t g_excess_samples_hrm[BIO_HRM_B0_SIGNAL_NUM];
/*! Metadata of each signal's samples that were last passed to the HRM app. */
static as7058_appmgr_sample_metadata_t g_last_metadata_hrm[BIO_HRM_B0_SIGNAL_NUM];
/*! Bitfield indicating for which signals ::g_last_metadata_hrm contains valid data. */
static uint8_t g_last_metadata_valid_hrm;
/*! Bitfield storing which preprocessing features are enabled for the HRM app. (see ::as7058_appmgr_preprocessing_flag)
 */
static uint32_t g_enabled_preprocessing_hrm;
#endif

#ifndef AS7058_APPMGR_DISABLE_SPO2_A0
/*! Signal mapping configuration for the SpO2 app. */
static as7058_sub_sample_ids_t g_signal_mapping_spo2[BIO_SPO2_A0_SIGNAL_NUM];
/*! Excess sample storage for the SpO2 app. */
static as7058_appmgr_excess_sample_t g_excess_samples_spo2[BIO_SPO2_A0_SIGNAL_NUM];
/*! Metadata of each signal's samples that were last passed to the SpO2 app. */
static as7058_appmgr_sample_metadata_t g_last_metadata_spo2[BIO_SPO2_A0_SIGNAL_NUM];
/*! Bitfield indicating for which signals ::g_last_metadata_spo2 contains valid data. */
static uint8_t g_last_metadata_valid_spo2;
/*! Bitfield storing which preprocessing features are enabled for the SpO2 app. (see ::as7058_appmgr_preprocessing_flag)
 */
static uint32_t g_enabled_preprocessing_spo2;
#endif

#ifndef AS7058_APPMGR_DISABLE_SRD
/*! Signal mapping configuration for the Signal Range Detection app. */
static as7058_sub_sample_ids_t g_signal_mapping_srd[BIO_SRD_SIGNAL_NUM];
/*! Metadata of each signal's samples that were last passed to the SRD app. */
static as7058_appmgr_sample_metadata_t g_last_metadata_srd[BIO_SRD_SIGNAL_NUM];
/*! Bitfield indicating for which signals ::g_last_metadata_srd contains valid data. */
static uint8_t g_last_metadata_valid_srd;
/*! Bitfield storing which preprocessing features are enabled for the SRD app. (see ::as7058_appmgr_preprocessing_flag)
 */
static uint32_t g_enabled_preprocessing_srd;
#endif

#ifndef AS7058_APPMGR_DISABLE_EDA
/*! Signal mapping configuration for the Electrodermal Activity app. */
static as7058_sub_sample_ids_t g_signal_mapping_eda[AS7058_EDA_APP_SIGNAL_NUM];
/*! Metadata of each signal's samples that were last passed to the EDA app. */
static as7058_appmgr_sample_metadata_t g_last_metadata_eda[AS7058_EDA_APP_SIGNAL_NUM];
/*! Bitfield indicating for which signals ::g_last_metadata_eda contains valid data. */
static uint8_t g_last_metadata_valid_eda;
#endif

#ifndef AS7058_APPMGR_DISABLE_STREAM
/*! Bitfield storing which preprocessing features are enabled for the streaming app. (see
 *  ::as7058_appmgr_preprocessing_flag) */
static uint32_t g_enabled_preprocessing_stream;
/*! The AGC statuses that were provided to the module previously. See ::g_agc_statuses_num for the number of valid items
 *  in the array. */
static agc_status_t g_last_agc_statuses[AGC_MAX_CHANNEL_CNT];
/*! The number of enabled AGC channels. When the number is not known yet, it is set to
 *  ::AS7058_APPMGR_AGC_STATUSES_NUM_UNKNOWN. In this case, ::g_last_agc_statuses contains no valid data. Otherwise,
 *  this variable contains the number of valid items in the ::g_last_agc_statuses array. */
static uint8_t g_agc_statuses_num;
#endif

#ifndef AS7058_APPMGR_DISABLE_RRM_A0
/*! Signal mapping configuration for the Respiration Rate app. */
static as7058_sub_sample_ids_t g_signal_mapping_rrm[BIO_RRM_A0_SIGNAL_NUM];
/*! Metadata of each signal's samples that were last passed to the Respiration Rate app. */
static as7058_appmgr_sample_metadata_t g_last_metadata_rrm[BIO_RRM_A0_SIGNAL_NUM];
/*! Bitfield indicating for which signals ::g_last_metadata_rrm contains valid data. */
static uint8_t g_last_metadata_valid_rrm;
/*! Bitfield storing which preprocessing features are enabled for the Respiration Rate app. (see
 *  ::as7058_appmgr_preprocessing_flag) */
static uint32_t g_enabled_preprocessing_rrm;
#endif

/*! Bitfield storing which apps are ready for execution. It stores ::as7058_appmgr_internal_app_id values converted to
 *  flags using ::M_ID_TO_FLAG. */
static volatile uint32_t g_executable_apps;

/*! Number of external events that need to be provided to the applications. */
static volatile uint8_t g_pending_ext_event_count;

/*! Mapping of ::as7058_appmgr_app_id values to ::as7058_appmgr_internal_app_id values. If an
 * ::as7058_appmgr_internal_app_id value is not available for a ::as7058_appmgr_app_id value, the corresponding array
 * item is set to ::AS7058_APPMGR_INTERNAL_APP_ID_NUM. */
static as7058_appmgr_internal_app_id_t g_app_id_mapping_public_to_internal[AS7058_APPMGR_APP_ID_NUM] = {
#ifdef AS7058_APPMGR_DISABLE_RAW
    [AS7058_APPMGR_APP_ID_RAW] = AS7058_APPMGR_INTERNAL_APP_ID_NUM,
#else
    [AS7058_APPMGR_APP_ID_RAW] = AS7058_APPMGR_INTERNAL_APP_ID_RAW,
#endif
#ifdef AS7058_APPMGR_DISABLE_HRM_B0
    [AS7058_APPMGR_APP_ID_HRM_B0] = AS7058_APPMGR_INTERNAL_APP_ID_NUM,
#else
    [AS7058_APPMGR_APP_ID_HRM_B0] = AS7058_APPMGR_INTERNAL_APP_ID_HRM_B0,
#endif
#ifdef AS7058_APPMGR_DISABLE_SPO2_A0
    [AS7058_APPMGR_APP_ID_SPO2_A0] = AS7058_APPMGR_INTERNAL_APP_ID_NUM,
#else
    [AS7058_APPMGR_APP_ID_SPO2_A0] = AS7058_APPMGR_INTERNAL_APP_ID_SPO2_A0,
#endif
#ifdef AS7058_APPMGR_DISABLE_SRD
    [AS7058_APPMGR_APP_ID_SRD] = AS7058_APPMGR_INTERNAL_APP_ID_NUM,
#else
    [AS7058_APPMGR_APP_ID_SRD] = AS7058_APPMGR_INTERNAL_APP_ID_SRD,
#endif
#ifdef AS7058_APPMGR_DISABLE_BIOZ
    [AS7058_APPMGR_APP_ID_BIOZ] = AS7058_APPMGR_INTERNAL_APP_ID_NUM,
#else
    [AS7058_APPMGR_APP_ID_BIOZ] = AS7058_APPMGR_INTERNAL_APP_ID_BIOZ,
#endif
#ifdef AS7058_APPMGR_DISABLE_EDA
    [AS7058_APPMGR_APP_ID_EDA] = AS7058_APPMGR_INTERNAL_APP_ID_NUM,
#else
    [AS7058_APPMGR_APP_ID_EDA] = AS7058_APPMGR_INTERNAL_APP_ID_EDA,
#endif
#ifdef AS7058_APPMGR_DISABLE_STREAM
    [AS7058_APPMGR_APP_ID_STREAM] = AS7058_APPMGR_INTERNAL_APP_ID_NUM,
#else
    [AS7058_APPMGR_APP_ID_STREAM] = AS7058_APPMGR_INTERNAL_APP_ID_STREAM,
#endif
#ifdef AS7058_APPMGR_DISABLE_RRM_A0
    [AS7058_APPMGR_APP_ID_RRM_A0] = AS7058_APPMGR_INTERNAL_APP_ID_NUM,
#else
    [AS7058_APPMGR_APP_ID_RRM_A0] = AS7058_APPMGR_INTERNAL_APP_ID_RRM_A0,
#endif
};

/*! Mapping of ::as7058_appmgr_internal_app_id values to ::as7058_appmgr_app_id values. */
static as7058_appmgr_app_id_t g_app_id_mapping_internal_to_public[AS7058_APPMGR_INTERNAL_APP_ID_NUM] = {
#ifndef AS7058_APPMGR_DISABLE_RAW
    [AS7058_APPMGR_INTERNAL_APP_ID_RAW] = AS7058_APPMGR_APP_ID_RAW,
#endif
#ifndef AS7058_APPMGR_DISABLE_HRM_B0
    [AS7058_APPMGR_INTERNAL_APP_ID_HRM_B0] = AS7058_APPMGR_APP_ID_HRM_B0,
#endif
#ifndef AS7058_APPMGR_DISABLE_SPO2_A0
    [AS7058_APPMGR_INTERNAL_APP_ID_SPO2_A0] = AS7058_APPMGR_APP_ID_SPO2_A0,
#endif
#ifndef AS7058_APPMGR_DISABLE_SRD
    [AS7058_APPMGR_INTERNAL_APP_ID_SRD] = AS7058_APPMGR_APP_ID_SRD,
#endif
#ifndef AS7058_APPMGR_DISABLE_BIOZ
    [AS7058_APPMGR_INTERNAL_APP_ID_BIOZ] = AS7058_APPMGR_APP_ID_BIOZ,
#endif
#ifndef AS7058_APPMGR_DISABLE_EDA
    [AS7058_APPMGR_INTERNAL_APP_ID_EDA] = AS7058_APPMGR_APP_ID_EDA,
#endif
#ifndef AS7058_APPMGR_DISABLE_STREAM
    [AS7058_APPMGR_INTERNAL_APP_ID_STREAM] = AS7058_APPMGR_APP_ID_STREAM,
#endif
#ifndef AS7058_APPMGR_DISABLE_RRM_A0
    [AS7058_APPMGR_INTERNAL_APP_ID_RRM_A0] = AS7058_APPMGR_APP_ID_RRM_A0,
#endif
};

/*! Definition of the applications. This array only contains definitions for applications that have not been disabled at
 *  compile-time. */
static const as7058_appmgr_app_definition_t g_app_table[AS7058_APPMGR_INTERNAL_APP_ID_NUM] = {
#ifndef AS7058_APPMGR_DISABLE_RAW
    [AS7058_APPMGR_INTERNAL_APP_ID_RAW] =
        {
            .p_initialize = as7058_raw_app_initialize,
            .p_shutdown = as7058_raw_app_shutdown,
            .p_configure = as7058_raw_app_configure,
            .p_start = handle_raw_app_start,
            .p_stop = as7058_raw_app_stop,
            .p_set_input = NULL,
            .p_execute = as7058_raw_app_execute,
            .p_get_output = as7058_raw_app_get_output,
            .p_signal_mapping = NULL,
            .p_excess_samples = NULL,
            .data_type = BIO_SIGNAL_SAMPLES_TYPE_U16, /* Placeholder value, has no effect since p_set_input is NULL. */
            .signals_num = 0,
            .excluded_apps = 0,
            .p_enabled_preprocessing = NULL,
            .p_last_metadata = NULL,
            .p_last_metadata_valid = NULL,
        },
#endif
#ifndef AS7058_APPMGR_DISABLE_HRM_B0
    [AS7058_APPMGR_INTERNAL_APP_ID_HRM_B0] =
        {
            .p_initialize = bio_hrm_b0_initialize,
            .p_shutdown = bio_hrm_b0_shutdown,
            .p_configure = bio_hrm_b0_configure,
            .p_start = bio_hrm_b0_start,
            .p_stop = bio_hrm_b0_stop,
            .p_set_input = bio_hrm_b0_set_input,
            .p_execute = bio_hrm_b0_execute,
            .p_get_output = bio_hrm_b0_get_output,
            .p_signal_mapping = g_signal_mapping_hrm,
            .p_excess_samples = g_excess_samples_hrm,
            .data_type = BIO_SIGNAL_SAMPLES_TYPE_I32,
            .signals_num = BIO_HRM_B0_SIGNAL_NUM,
            .excluded_apps = 0,
            .p_enabled_preprocessing = &g_enabled_preprocessing_hrm,
            .p_last_metadata = g_last_metadata_hrm,
            .p_last_metadata_valid = &g_last_metadata_valid_hrm,
        },
#endif
#ifndef AS7058_APPMGR_DISABLE_SPO2_A0
    [AS7058_APPMGR_INTERNAL_APP_ID_SPO2_A0] =
        {
            .p_initialize = bio_spo2_a0_initialize,
            .p_shutdown = bio_spo2_a0_shutdown,
            .p_configure = bio_spo2_a0_configure,
            .p_start = bio_spo2_a0_start,
            .p_stop = bio_spo2_a0_stop,
            .p_set_input = bio_spo2_a0_set_input,
            .p_execute = bio_spo2_a0_execute,
            .p_get_output = bio_spo2_a0_get_output,
            .p_signal_mapping = g_signal_mapping_spo2,
            .p_excess_samples = g_excess_samples_spo2,
            .data_type = BIO_SIGNAL_SAMPLES_TYPE_U16,
            .signals_num = BIO_SPO2_A0_SIGNAL_NUM,
            .excluded_apps = 0,
            .p_enabled_preprocessing = &g_enabled_preprocessing_spo2,
            .p_last_metadata = g_last_metadata_spo2,
            .p_last_metadata_valid = &g_last_metadata_valid_spo2,
        },
#endif
#ifndef AS7058_APPMGR_DISABLE_SRD
    [AS7058_APPMGR_INTERNAL_APP_ID_SRD] =
        {
            .p_initialize = bio_srd_initialize,
            .p_shutdown = bio_srd_shutdown,
            .p_configure = bio_srd_configure,
            .p_start = bio_srd_start,
            .p_stop = bio_srd_stop,
            .p_set_input = bio_srd_set_input,
            .p_execute = bio_srd_execute,
            .p_get_output = bio_srd_get_output,
            .p_signal_mapping = g_signal_mapping_srd,
            .p_excess_samples = NULL,
            .data_type = BIO_SIGNAL_SAMPLES_TYPE_I32,
            .signals_num = BIO_SRD_SIGNAL_NUM,
            .excluded_apps = 0,
            .p_enabled_preprocessing = &g_enabled_preprocessing_srd,
            .p_last_metadata = g_last_metadata_srd,
            .p_last_metadata_valid = &g_last_metadata_valid_srd,
        },
#endif
#ifndef AS7058_APPMGR_DISABLE_BIOZ
    [AS7058_APPMGR_INTERNAL_APP_ID_BIOZ] =
        {
            .p_initialize = as7058_bioz_app_initialize,
            .p_shutdown = as7058_bioz_app_shutdown,
            .p_configure = as7058_bioz_app_configure,
            .p_start = as7058_bioz_app_start,
            .p_stop = as7058_bioz_app_stop,
            .p_set_input = NULL,
            .p_execute = as7058_bioz_app_execute,
            .p_get_output = as7058_bioz_app_get_output,
            .p_signal_mapping = NULL,
            .p_excess_samples = NULL,
            .data_type = BIO_SIGNAL_SAMPLES_TYPE_U16, /* Placeholder value, has no effect since p_set_input is NULL. */
            .signals_num = 0,
            .excluded_apps = AS7058_APPMGR_APP_FLAG_RAW | AS7058_APPMGR_APP_FLAG_HRM_B0 |
                             AS7058_APPMGR_APP_FLAG_SPO2_A0 | AS7058_APPMGR_APP_FLAG_SRD | AS7058_APPMGR_APP_FLAG_EDA |
                             AS7058_APPMGR_APP_FLAG_RRM_A0,
            .p_enabled_preprocessing = NULL,
            .p_last_metadata = NULL,
            .p_last_metadata_valid = NULL,
        },
#endif
#ifndef AS7058_APPMGR_DISABLE_EDA
    [AS7058_APPMGR_INTERNAL_APP_ID_EDA] =
        {
            .p_initialize = as7058_eda_app_initialize,
            .p_shutdown = as7058_eda_app_shutdown,
            .p_configure = as7058_eda_app_configure,
            .p_start = as7058_eda_app_start,
            .p_stop = as7058_eda_app_stop,
            .p_set_input = as7058_eda_app_set_input,
            .p_execute = as7058_eda_app_execute,
            .p_get_output = as7058_eda_app_get_output,
            .p_signal_mapping = g_signal_mapping_eda,
            .p_excess_samples = NULL,
            .data_type = BIO_SIGNAL_SAMPLES_TYPE_I32,
            .signals_num = AS7058_EDA_APP_SIGNAL_NUM,
            .excluded_apps = 0,
            .p_enabled_preprocessing = NULL,
            .p_last_metadata = g_last_metadata_eda,
            .p_last_metadata_valid = &g_last_metadata_valid_eda,
        },
#endif
#ifndef AS7058_APPMGR_DISABLE_STREAM
    [AS7058_APPMGR_INTERNAL_APP_ID_STREAM] =
        {
            .p_initialize = bio_stream_initialize,
            .p_shutdown = bio_stream_shutdown,
            .p_configure = bio_stream_configure,
            .p_start = handle_bio_stream_start,
            .p_stop = bio_stream_stop,
            .p_set_input = NULL,
            .p_execute = bio_stream_execute,
            .p_get_output = bio_stream_get_output,
            .p_signal_mapping = NULL,
            .p_excess_samples = NULL,
            .data_type = BIO_SIGNAL_SAMPLES_TYPE_U16, /* Placeholder value, has no effect since p_set_input is NULL. */
            .signals_num = 0,
            .excluded_apps = 0,
            .p_enabled_preprocessing = &g_enabled_preprocessing_stream,
            .p_last_metadata = NULL,
            .p_last_metadata_valid = NULL,
        },
#endif
#ifndef AS7058_APPMGR_DISABLE_RRM_A0
    [AS7058_APPMGR_INTERNAL_APP_ID_RRM_A0] =
        {
            .p_initialize = bio_rrm_a0_initialize,
            .p_shutdown = bio_rrm_a0_shutdown,
            .p_configure = bio_rrm_a0_configure,
            .p_start = bio_rrm_a0_start,
            .p_stop = bio_rrm_a0_stop,
            .p_set_input = bio_rrm_a0_set_input,
            .p_execute = bio_rrm_a0_execute,
            .p_get_output = bio_rrm_a0_get_output,
            .p_signal_mapping = g_signal_mapping_rrm,
            .p_excess_samples = NULL,
            .data_type = BIO_SIGNAL_SAMPLES_TYPE_U32,
            .signals_num = BIO_RRM_A0_SIGNAL_NUM,
            .excluded_apps = 0,
            .p_enabled_preprocessing = &g_enabled_preprocessing_rrm,
            .p_last_metadata = g_last_metadata_rrm,
            .p_last_metadata_valid = &g_last_metadata_valid_rrm,
        },
#endif
};

/*! Chip Library extraction state. */
static as7058_extract2_state_t g_extract_state;

/*! PPG sample period as received from Chip Library. */
static uint32_t g_ppg_sample_period_us;

/*! ECG SEQ1 sample period as received from Chip Library. */
static uint32_t g_ecg_seq1_sample_period_us;

/*! ECG SEQ2 sample period as received from Chip Library. */
static uint32_t g_ecg_seq2_sample_period_us;

/*! PD offset compensation values per PPG modulator for the SAR-controlled PD offset bits. */
static as7058_appmgr_sample_t
    g_pd_offset_compensation_table[AS7058_MODULATOR_NUM_PPG]
                                  [AS7058_PD_OFFSET_CALIBRATION_COMPENSATION_TABLE_ELEMENTS_NUM];

/*! Base PD offset compensation value per PPG modulator for the programmable PD offset bits. */
static as7058_appmgr_sample_t g_pd_offset_compensation_programmable[AS7058_MODULATOR_NUM_PPG];

/******************************************************************************
 *                              LOCAL FUNCTIONS                               *
 ******************************************************************************/

/*!
 * \brief Chip-specific function called when the Application Manager enters state ::AS7058_APPMGR_STATE_PROCESSING. It
 *        shall store required information from the measurement configuration which is needed by other chip-specific
 *        functions that are called while the Application Manager is entering state ::AS7058_APPMGR_STATE_PROCESSING or
 *        is in state ::AS7058_APPMGR_STATE_PROCESSING.
 *
 * This function is called before any other chip-specific function while the Application Manager is entering state
 * ::AS7058_APPMGR_STATE_PROCESSING or is in state ::AS7058_APPMGR_STATE_PROCESSING.
 */
static err_code_t process_measurement_config(as7058_meas_config_t measurement_config)
{
    M_CHECK_SUCCESS(as7058_extract2_prepare_for_new_measurement(
        measurement_config.fifo_map, measurement_config.sar_map,
        (as7058_sar_transfer_mode_t)measurement_config.sar_transfer_mode, &g_extract_state));

    g_ppg_sample_period_us = measurement_config.ppg_sample_period_us;
    g_ecg_seq1_sample_period_us = measurement_config.ecg_seq1_sample_period_us;
    g_ecg_seq2_sample_period_us = measurement_config.ecg_seq2_sample_period_us;

    return ERR_SUCCESS;
}

/*!
 * \brief Chip-specific function called when the Application Manager leaves ::AS7058_APPMGR_STATE_PROCESSING.
 */
static err_code_t clear_measurement_config(void)
{
    memset(&g_extract_state, 0x00, sizeof(g_extract_state));

    g_ppg_sample_period_us = 0;
    g_ecg_seq1_sample_period_us = 0;
    g_ecg_seq2_sample_period_us = 0;

    return ERR_SUCCESS;
}

/*!
 * \brief Chip-specific function called when the Application Manager enters state ::AS7058_APPMGR_STATE_PROCESSING.
 *        It shall provide the sample period of the given channel. If the channel is not sampled according to the
 *        measurement configuration provided to ::process_measurement_config, an error code that is not ::ERR_SUCCESS
 *        shall be returned.
 */
static err_code_t get_sample_period_for_channel(as7058_sub_sample_ids_t id, uint32_t *p_sample_period_us)
{
    if (AS7058_SUB_SAMPLE_ID_DISABLED == id || id > AS7058_SUB_SAMPLE_ID_ECG_SEQ2_SUB1) {
        return ERR_CONFIG;
    }

    as7058_sub_sample_flags_t channel_flag = M_AS7058_SUB_SAMPLE_ID_TO_FLAG(id);
    if (!(channel_flag & g_extract_state.fifo_map)) {
        return ERR_CONFIG;
    }

    if (id <= AS7058_SUB_SAMPLE_ID_PPG2_SUB8) {
        *p_sample_period_us = g_ppg_sample_period_us;
    } else if (id <= AS7058_SUB_SAMPLE_ID_ECG_SEQ1_SUB2) {
        *p_sample_period_us = g_ecg_seq1_sample_period_us;
    } else {
        *p_sample_period_us = g_ecg_seq2_sample_period_us;
    }

    return ERR_SUCCESS;
}

/*!
 * \brief Chip-specific function extracting all samples from the provided FIFO data.
 *
 * \param[in] p_fifo_data        Points to the FIFO data.
 * \param[in] fifo_data_size     Size of the FIFO data in bytes.
 * \param[out] pp_extract_result Points to the ::as7058_appmgr_extract_result_t instance that will hold the extraction
 *                               results. ::get_sample_count_for_channel, ::get_adc_value_of_sample, and
 *                               ::get_sar_pd_offset_of_sample are called to get values from the
 *                               ::as7058_appmgr_extract_result_t instance.
 *
 * \retval ERR_SUCCESS Samples extracted.
 */
static err_code_t extract_samples_from_fifo_data(const uint8_t *p_fifo_data, uint16_t fifo_data_size,
                                                 as7058_appmgr_extract_result_t *pp_extract_result)
{
    static as7058_extract2_sample_t sample_buffer[AS7058_FIFO_DATA_BUFFER_SIZE / AS7058_FIFO_SAMPLE_SIZE];

    return as7058_extract2(p_fifo_data, fifo_data_size, pp_extract_result, sample_buffer,
                           AS7058_FIFO_DATA_BUFFER_SIZE / AS7058_FIFO_SAMPLE_SIZE, &g_extract_state);
}

/*!
 * \brief Chip-specific function returning the number of extracted samples for a given channel.
 *
 * \param[in] channel            Channel.
 * \param[in] pp_extract_result  Points to the ::as7058_appmgr_extract_result_t instance holding the extraction results.
 *
 * \returns Number of extracted samples for the given channel.
 */
static uint16_t get_sample_count_for_channel(as7058_sub_sample_ids_t channel,
                                             const as7058_appmgr_extract_result_t *pp_extract_result)
{
    if (channel >= AS7058_SUB_SAMPLE_ID_NUM) {
        return 0;
    }

    const as7058_extract2_sample_t *p_channel_samples = (*pp_extract_result)[channel];
    const as7058_extract2_sample_t *p_channel_samples_after_last = (*pp_extract_result)[channel + 1];

    return p_channel_samples_after_last - p_channel_samples;
}

/*!
 * \brief Chip-specific function providing the extracted ADC value of a sample of the given channel at the given index.
 */
static err_code_t get_adc_value_of_sample(as7058_sub_sample_ids_t channel, uint16_t sample_idx,
                                          const as7058_appmgr_extract_result_t *pp_extract_result,
                                          as7058_appmgr_sample_t *p_sample)
{
    if (channel >= AS7058_SUB_SAMPLE_ID_NUM) {
        return ERR_ARGUMENT;
    }

    const as7058_extract2_sample_t *p_channel_samples = (*pp_extract_result)[channel];
    const as7058_extract2_sample_t *p_channel_samples_after_last = (*pp_extract_result)[channel + 1];

    if (p_channel_samples + sample_idx >= p_channel_samples_after_last) {
        return ERR_ARGUMENT;
    }

    *p_sample = p_channel_samples[sample_idx].adc_value;

    return ERR_SUCCESS;
}

/*!
 * \brief Chip-specific function providing the extracted PD offset current of a sample of the given channel at the given
 *        index.
 */
static err_code_t get_pd_offset_of_sample(as7058_sub_sample_ids_t channel, uint16_t sample_idx,
                                          const as7058_appmgr_extract_result_t *pp_extract_result, uint8_t *p_pd_offset)
{
    if (channel >= AS7058_SUB_SAMPLE_ID_NUM) {
        return ERR_ARGUMENT;
    }

    const as7058_extract2_sample_t *p_channel_samples = (*pp_extract_result)[channel];
    const as7058_extract2_sample_t *p_channel_samples_after_last = (*pp_extract_result)[channel + 1];

    if (p_channel_samples + sample_idx >= p_channel_samples_after_last) {
        return ERR_ARGUMENT;
    }

    if (!p_channel_samples[sample_idx].sar_enabled) {
        return ERR_NO_DATA;
    }

    *p_pd_offset = p_channel_samples[sample_idx].pd_offset;

    return ERR_SUCCESS;
}

/*!
 * \brief Chip-specific function called in state ::AS7058_APPMGR_STATE_CONFIGURATION to process and store a PD offset
 *        compensation configuration.
 *
 * \param[in] p_config Points to the PD offset compensation configuration to store.
 *
 * \retval ERR_SUCCESS  PD offset compensation performed.
 * \retval ERR_ARGUMENT Invalid configuration data.
 */
static err_code_t
configure_pd_offset_compensation(const as7058_appmgr_preprocessing_configuration_pd_offset_compensation_t *p_config)
{
    for (uint8_t element_idx = 0; element_idx < AS7058_PD_OFFSET_CALIBRATION_COMPENSATION_TABLE_ELEMENTS_NUM;
         element_idx++) {
        if (p_config->compensation_table_ppg1[element_idx] >
                AS7058_APPMGR_PD_OFFSET_COMPENSATION_CALIBRATION_TABLE_ENTRY_MAX ||
            p_config->compensation_table_ppg2[element_idx] >
                AS7058_APPMGR_PD_OFFSET_COMPENSATION_CALIBRATION_TABLE_ENTRY_MAX) {
            /* Compensation table value exceeds the maximum valid value. */
            return ERR_ARGUMENT;
        }

        g_pd_offset_compensation_table[AS7058_MODULATOR_PPG1][element_idx] =
            (as7058_appmgr_sample_t)p_config->compensation_table_ppg1[element_idx];
        g_pd_offset_compensation_table[AS7058_MODULATOR_PPG2][element_idx] =
            (as7058_appmgr_sample_t)p_config->compensation_table_ppg2[element_idx];
    }

    for (uint8_t ppg_modulator_idx = 0; ppg_modulator_idx < AS7058_MODULATOR_NUM_PPG; ppg_modulator_idx++) {
        /* The base compensation value for the programmable PD offset steps is determined by the average of the
         * differences of consecutive compensation table entries divided by the number of programmable PD offset steps.
         * It is later multiplied with the actual value of the programmable PD offset bits to obtain the compensation
         * value for the programmable bits. The compensation value for the programmable bits is then added to the
         * compensation value for the SAR-controlled bits. */

        as7058_appmgr_sample_t compensation_value_diff_avg = g_pd_offset_compensation_table[ppg_modulator_idx][0];
        for (uint8_t element_idx = 1; element_idx < AS7058_PD_OFFSET_CALIBRATION_COMPENSATION_TABLE_ELEMENTS_NUM;
             element_idx++) {
            compensation_value_diff_avg += g_pd_offset_compensation_table[ppg_modulator_idx][element_idx] -
                                           g_pd_offset_compensation_table[ppg_modulator_idx][element_idx - 1];
        }
        compensation_value_diff_avg /= AS7058_PD_OFFSET_CALIBRATION_COMPENSATION_TABLE_ELEMENTS_NUM;

        g_pd_offset_compensation_programmable[ppg_modulator_idx] =
            compensation_value_diff_avg / (1 << AS7058_APPMGR_PD_OFFSET_SAR_BITS_NUM);
    }

    return ERR_SUCCESS;
}

/*!
 * \brief Chip-specific function called in state ::AS7058_APPMGR_STATE_PROCESSING to perform PD offset compensation on
 *        a provided sample value.
 *
 * \param[in] channel        Channel which was used to acquire the sample.
 * \param[inout] p_sample    Points to the sample value. The PD offset compensation is performed on the pointee. The
 *                           pointee is updated to the sample value after compensation.
 * \param[inout] p_pd_offset Points to the PD offset current that was set when the sample was acquired. The PD offset
 *                           compensation is performed using the pointee. The pointee is updated to the effective PD
 *                           offset current after compensation.
 *
 * \retval ERR_SUCCESS  PD offset compensation performed.
 * \retval ERR_ARGUMENT Invalid parameter value provided.
 */
static err_code_t perform_pd_offset_compensation(as7058_sub_sample_ids_t channel, as7058_appmgr_sample_t *p_sample,
                                                 uint8_t *p_pd_offset)
{
    uint8_t sar_pd_offset = (*p_pd_offset) >> AS7058_APPMGR_PD_OFFSET_PROGRAMMABLE_BITS_NUM;
    uint8_t programmable_pd_offset = (*p_pd_offset) & AS7058_APPMGR_PD_OFFSET_PROGRAMMABLE_BITS_MASK;

    /* Get PPG modulator associated to the provided sub-sample. */
    as7058_modulator_t modulator;
    if (channel <= AS7058_SUB_SAMPLE_ID_PPG1_SUB8) {
        /* PPG modulator 1. */
        modulator = AS7058_MODULATOR_PPG1;
    } else if (channel <= AS7058_SUB_SAMPLE_ID_PPG2_SUB8) {
        /* PPG modulator 2. */
        modulator = AS7058_MODULATOR_PPG2;
    } else {
        /* Sub-sample ID is not a PPG sub-sample ID. */
        return ERR_ARGUMENT;
    }

    /* Calculate the compensation value. */
    as7058_appmgr_sample_t compensation_value;
    /* Compensate the SAR-controlled PD offset bits by using a value from the compensation table. */
    if (sar_pd_offset > 0) {
        compensation_value = g_pd_offset_compensation_table[modulator][sar_pd_offset - 1];
    } else {
        /* When the value of the SAR-controlled PD offset bits is zero, use a fixed compensation value of zero as the
         * compensation tables only include entries for non-zero SAR-controlled PD offset bits. */
        compensation_value = 0;
    }
    /* Compensate the programmable PD offset bits by scaling the base compensation value of the programmable PD offset
     * bits. */
    compensation_value += g_pd_offset_compensation_programmable[modulator] * programmable_pd_offset;

    /* Apply the compensation value to the sample. */
    *p_sample += compensation_value;

    /* Sample value is now compensated for the PD offset, so the PD offset current is cleared. */
    *p_pd_offset = 0;

    return ERR_SUCCESS;
}

/*!
 * \brief Chip-specific function called in state ::AS7058_APPMGR_STATE_PROCESSING to convert a potentially preprocessed
 *        sample to an unsigned 16-bit integer.
 */
static uint16_t convert_sample_u16(as7058_appmgr_sample_t input)
{
    if (input > AS7058_APPMGR_SAMPLE_MAX) {
        /* After preprocessing, the value of a sample may exceed AS7058_APPMGR_SAMPLE_MAX. */
        return UINT16_MAX;
    } else {
        return (uint16_t)(input >> (AS7058_APPMGR_SAMPLE_BIT_SIZE - 16));
    }
}

/*!
 * \brief Chip-specific function called in state ::AS7058_APPMGR_STATE_PROCESSING to convert a potentially preprocessed
 *        sample to an unsigned 32-bit integer.
 */
static uint32_t convert_sample_u32(as7058_appmgr_sample_t input)
{
    return input;
}

/*!
 * \brief Chip-specific function called in state ::AS7058_APPMGR_STATE_PROCESSING to convert a potentially preprocessed
 *        sample to a signed 32-bit integer.
 */
static int32_t convert_sample_i32(as7058_appmgr_sample_t input)
{
    if (input > INT32_MAX) {
        return INT32_MAX;
    } else {
        return (int32_t)input;
    }
}

/*! Gets the ::as7058_appmgr_internal_app_id for a given ::as7058_appmgr_app_id. Returns ::ERR_ERR_ARGUMENT if the
 *  ::as7058_appmgr_app_id value is invalid or ::ERR_NOT_SUPPORTED if the app has been disabled at compile-time. */
static err_code_t get_internal_app_id_for_public_app_id(as7058_appmgr_app_id_t public_id,
                                                        as7058_appmgr_internal_app_id_t *p_internal_id)
{
    if (public_id >= AS7058_APPMGR_APP_ID_NUM) {
        return ERR_ARGUMENT;
    }

    uint8_t internal_id = g_app_id_mapping_public_to_internal[public_id];
    if (AS7058_APPMGR_INTERNAL_APP_ID_NUM == internal_id) {
        /* App has been disabled at compile-time. */
        return ERR_NOT_SUPPORTED;
    }

    *p_internal_id = internal_id;
    return ERR_SUCCESS;
}

/*!
 * \brief Generates an ::agc_change_state_t by comparing two current values.
 *
 * \param[in] current          Current current value.
 * \param[in] previous_current Pointer to the current value to compare against.
 *
 * \retval AGC_STATE_UNCHANGED Current current is identical to previous current.
 * \retval AGC_STATE_INCREASED Current current is greater than the previous current.
 * \retval AGC_STATE_DECREASED Current current is less than the previous current.
 */
static agc_change_state_t generate_agc_change_state(uint8_t current, uint8_t previous_current)
{
    if (current == previous_current) {
        return AGC_STATE_UNCHANGED;
    } else if (current > previous_current) {
        return AGC_STATE_INCREASED;
    } else { /* current < previous_current */
        return AGC_STATE_DECREASED;
    }
}

/*!
 * \brief Generates an ::agc_status_t from metadata.
 *
 * \param[in] metadata            Current metadata.
 * \param[in] p_previous_metadata Pointer to previous metadata used to generate change states. Can be NULL.
 * \param[out] p_agc_status       Generated AGC status is written to the pointee, provided that an AGC status is
 *                                generated.
 *
 * \retval ERR_SUCCESS AGC status generated.
 * \retval ERR_NO_DATA No AGC status generated.
 * \retval ERR_DATA    Inconsistent sample metadata detected.
 */
static err_code_t generate_agc_status(as7058_appmgr_sample_metadata_t metadata,
                                      const as7058_appmgr_sample_metadata_t *p_previous_metadata,
                                      agc_status_t *p_agc_status)
{
    if (p_previous_metadata &&
        ((metadata.flags.pd_offset_current_valid != p_previous_metadata->flags.pd_offset_current_valid) ||
         (metadata.flags.led_current_valid != p_previous_metadata->flags.led_current_valid))) {
        /* Metadata field validity flags are expected not to change during the measurement. */
        return ERR_DATA;
    } else if (!metadata.flags.pd_offset_current_valid && !metadata.flags.led_current_valid) {
        /* Generate no AGC status as neither PD offset current nor LED current is available. */
        return ERR_NO_DATA;
    } else {
        if (metadata.flags.pd_offset_current_valid) {
            p_agc_status->pd_offset_current = metadata.pd_offset_current;

            if (p_previous_metadata) {
                /* Metadata of previously passed samples available, use it for generating change state. */
                p_agc_status->pd_offset_change =
                    generate_agc_change_state(metadata.pd_offset_current, p_previous_metadata->pd_offset_current);
            } else {
                /* No metadata of previously passed samples available. */
                p_agc_status->pd_offset_change = AGC_STATE_UNCHANGED;
            }
        } else {
            /* No PD offset current available. */
            p_agc_status->pd_offset_current = 0;
            p_agc_status->pd_offset_change = AGC_STATE_UNDEFINED;
        }

        if (metadata.flags.led_current_valid) {
            p_agc_status->led_current = metadata.led_current;

            if (p_previous_metadata) {
                /* Metadata of previously passed samples available, use it for generating change state. */
                p_agc_status->led_change =
                    generate_agc_change_state(metadata.led_current, p_previous_metadata->led_current);
            } else {
                /* No metadata of previously passed samples available. */
                p_agc_status->led_change = AGC_STATE_UNCHANGED;
            }
        } else {
            /* No LED current available. */
            p_agc_status->led_current = 0;
            p_agc_status->led_change = AGC_STATE_UNDEFINED;
        }

        return ERR_SUCCESS;
    }
}

/*!
 * \brief Generates sample metadata from the AGC status and the SAR PD offset current.
 *
 * The LED current in the metadata is taken from the AGC status. If no SAR PD offset current is provided, the PD offset
 * current is also taken from the AGC status. If an SAR PD offset current is provided, the PD offset current in the
 * metadata is the combination of the PD offset currents of the AGC status and the SAR PD offset current (SAR-controlled
 * bits are taken from SAR PD offset current, remaining bits are taken from AGC status). The LED current and PD offset
 * current values of the AGC status are only considered if the corresponding change states indicate that the values are
 * valid.
 *
 * \param[in] p_agc_status            Points to the AGC status. Can be NULL.
 * \param[in] p_sar_pd_offset_current Points to the SAR PD offset current. Can be NULL.
 *
 * \returns Generated metadata.
 */
static as7058_appmgr_sample_metadata_t generate_metadata(const agc_status_t *p_agc_status,
                                                         const uint8_t *p_sar_pd_offset_current)
{
    as7058_appmgr_sample_metadata_t metadata;

    if (p_agc_status && p_agc_status->pd_offset_change != AGC_STATE_UNDEFINED && p_sar_pd_offset_current) {
        /* AGC status (with valid PD offset current) and SAR PD offset current provided. */
        metadata.pd_offset_current = (*p_sar_pd_offset_current & (~AS7058_APPMGR_PD_OFFSET_PROGRAMMABLE_BITS_MASK)) |
                                     (p_agc_status->pd_offset_current & AS7058_APPMGR_PD_OFFSET_PROGRAMMABLE_BITS_MASK);
        metadata.flags.pd_offset_current_valid = TRUE;
    } else if (p_agc_status && p_agc_status->pd_offset_change != AGC_STATE_UNDEFINED) {
        /* AGC status (with valid PD offset current) provided only. */
        metadata.pd_offset_current = p_agc_status->pd_offset_current;
        metadata.flags.pd_offset_current_valid = TRUE;
    } else if (p_sar_pd_offset_current) {
        /* SAR PD offset current provided only. */
        metadata.pd_offset_current = *p_sar_pd_offset_current;
        metadata.flags.pd_offset_current_valid = TRUE;
    } else {
        /* Neither AGC status (with valid PD offset current) nor SAR PD offset current provided. */
        metadata.pd_offset_current = 0;
        metadata.flags.pd_offset_current_valid = FALSE;
    }

    if (p_agc_status && p_agc_status->led_change != AGC_STATE_UNDEFINED) {
        /* AGC status (with valid LED current) provided. */
        metadata.led_current = p_agc_status->led_current;
        metadata.flags.led_current_valid = TRUE;
    } else {
        /* No AGC status (with valid LED current) provided. */
        metadata.led_current = 0;
        metadata.flags.led_current_valid = FALSE;
    }

    return metadata;
}

/*!
 * \brief Gets the AGC status of a given channel from the Chip Library-provided AGC statuses array.
 *
 * \param[in] channel                Channel.
 * \param[in] p_agc_statuses         Points to the begin of the Chip Library-provided AGC statuses array.
 * \param[in] agc_statuses_num       Number of Chip Library-provided AGC statuses.
 * \param[out] pp_channel_agc_status Pointee is updated to point to the AGC status corresponding to the given channel.
 *
 * \retval ERR_SUCCESS  AGC status found for the given channel.
 * \retval ERR_NO_DATA  AGC status is not available for the given channel.
 * \retval ERR_SIZE     According to configuration, an AGC status is available for the given channel, but the Chip
 *                      Library-provided AGC statuses array does not contain it.
 */
static err_code_t get_agc_status_of_channel(as7058_sub_sample_ids_t channel, const agc_status_t *p_agc_statuses,
                                            uint8_t agc_statuses_num, const agc_status_t **pp_channel_agc_status)
{
    if (channel < AS7058_APPMGR_CHANNEL_ID_AGC_FIRST || channel > AS7058_APPMGR_CHANNEL_ID_AGC_LAST) {
        /* Channel does not support AGC. */
        return ERR_NO_DATA;
    }

    uint8_t agc_idx = g_agc_mapping[channel - AS7058_APPMGR_CHANNEL_ID_AGC_FIRST];

    if (AS7058_APPMGR_AGC_MAPPING_DISABLED == agc_idx) {
        /* No AGC status is available for the given channel. */
        return ERR_NO_DATA;
    }

    if (agc_idx >= agc_statuses_num) {
        /* No AGC status is provided for the mapped AGC instance. */
        return ERR_SIZE;
    }

    *pp_channel_agc_status = &p_agc_statuses[agc_idx];
    return ERR_SUCCESS;
}

/*!
 * \brief Gets a sample and corresponding metadata (if available) from the extract results and the Chip Library-provided
 *        AGC statuses array.
 *
 * \param[in] channel                Channel.
 * \param[in] sample_idx             Index of the channel's s gample to extract.
 * \param[in] pp_extract_result      Points to the extract results.
 * \param[in] p_agc_statuses         Points to the begin of the Chip Library-provided AGC statuses array.
 * \param[in] agc_statuses_num       Number of Chip Library-provided AGC statuses.
 * \param[out] p_sample              Pointee is updated with the extracted sample.
 * \param[out] p_metadata            Pointee is updated with the metadata of the extracted sample.
 *
 * \retval ERR_SUCCESS Got data successfully.
 */
static err_code_t get_sample_with_metadata(as7058_sub_sample_ids_t channel, uint16_t sample_idx,
                                           const as7058_appmgr_extract_result_t *pp_extract_result,
                                           const agc_status_t *p_agc_statuses, uint8_t agc_statuses_num,
                                           as7058_appmgr_sample_t *p_sample,
                                           as7058_appmgr_sample_metadata_t *p_metadata)
{
    as7058_appmgr_sample_t sample;
    uint8_t sample_pd_offset;
    const agc_status_t *p_agc_status;
    M_CHECK_SUCCESS(get_adc_value_of_sample(channel, sample_idx, pp_extract_result, &sample));
    err_code_t pd_offset_result = get_pd_offset_of_sample(channel, sample_idx, pp_extract_result, &sample_pd_offset);
    if (pd_offset_result != ERR_NO_DATA) {
        M_CHECK_SUCCESS(pd_offset_result);
    }
    err_code_t agc_result = get_agc_status_of_channel(channel, p_agc_statuses, agc_statuses_num, &p_agc_status);
    if (agc_result != ERR_NO_DATA) {
        M_CHECK_SUCCESS(agc_result);
    }

    *p_sample = sample;
    *p_metadata = generate_metadata((ERR_SUCCESS == agc_result ? p_agc_status : NULL),
                                    (ERR_SUCCESS == pd_offset_result ? &sample_pd_offset : NULL));

    return ERR_SUCCESS;
}

/*! Performs the preprocessing operations enabled for a given application on a given sample. */
static err_code_t perform_enabled_preprocessing(as7058_appmgr_sample_t *p_sample,
                                                as7058_appmgr_sample_metadata_t *p_metadata,
                                                as7058_sub_sample_ids_t channel,
                                                const as7058_appmgr_app_definition_t *p_app)
{
    if (!p_app->p_enabled_preprocessing) {
        /* App does not support preprocessing. */
        return ERR_SUCCESS;
    }

    if ((*p_app->p_enabled_preprocessing & AS7058_APPMGR_PREPROCESSING_FLAG_PD_OFFSET_COMPENSATION) &&
        p_metadata->flags.pd_offset_current_valid) {
        /* Perform PD offset compensation. */
        M_CHECK_SUCCESS(perform_pd_offset_compensation(channel, p_sample, &p_metadata->pd_offset_current));
    }

    return ERR_SUCCESS;
}

/*!
 * \brief Passes the sample extraction results to the set input function of the app. Depending on the extracted data,
 *        the set input of the app may be called several times.
 *
 * \param[in] pp_extract_result   Points to the extracted data.
 * \param[in] p_agc_statuses      Points to the begin of the AGC statuses array.
 * \param[in] agc_statuses_num    Number of AGC statuses in the AGC statuses array.
 * \param[in] p_agc_statuses      Points to the begin of the accelerometer samples array.
 * \param[in] acc_samples_num     Number of samples in the accelerometer samples array.
 * \param[in] p_app               Points the definition of the app to which the data shall be passed.
 * \param[out] p_execution_status Pointee is set to the new execution status of the app.

 * \retval ERR_SUCCESS  Samples passed to application successfully.
 * \retval ERR_DATA     Inconsistent sample metadata detected.
 * \retval ERR_OVERFLOW Sample was attempted to be added to extracted sample storage, but it already contained a sample.
 */
static err_code_t process_samples(const as7058_appmgr_extract_result_t *pp_extract_result,
                                  const agc_status_t *p_agc_statuses, uint8_t agc_statuses_num,
                                  const vs_acc_data_t *p_acc_samples, uint16_t acc_samples_num,
                                  const as7058_appmgr_app_definition_t *p_app,
                                  bio_execution_status_t *p_execution_status)
{
    *p_execution_status = BIO_EXECUTION_STATUS_NOT_EXECUTABLE;

    M_CHECK_APP_DEFINITION(BIO_SIGNAL_SAMPLES_TYPE_U16 == p_app->data_type ||
                           BIO_SIGNAL_SAMPLES_TYPE_U32 == p_app->data_type ||
                           BIO_SIGNAL_SAMPLES_TYPE_I32 == p_app->data_type);
    M_CHECK_APP_DEFINITION(p_app->signals_num <= AS7058_APPMGR_MAX_APP_SIGNAL_NUM);
    M_CHECK_APP_DEFINITION(p_app->p_signal_mapping);
    M_CHECK_APP_DEFINITION(p_app->p_last_metadata);
    M_CHECK_APP_DEFINITION(p_app->p_last_metadata_valid);

    /* Prepare the signal_data array that is used to provides samples to the application. For each signal, a separate
     * buffer exists in converted_samples that stores the samples of the corresponding signal. */
    bio_signal_samples_t signal_data[AS7058_APPMGR_MAX_APP_SIGNAL_NUM];
    as7058_appmgr_converted_samples_t converted_samples;
    for (uint8_t signal_idx = 0; signal_idx < p_app->signals_num; signal_idx++) {
        if (BIO_SIGNAL_SAMPLES_TYPE_U16 == p_app->data_type) {
            signal_data[signal_idx].samples.p_u16 = converted_samples.u16[signal_idx];
        } else if (BIO_SIGNAL_SAMPLES_TYPE_U32 == p_app->data_type) {
            signal_data[signal_idx].samples.p_u32 = converted_samples.u32[signal_idx];
        } else { /* BIO_SIGNAL_SAMPLES_TYPE_I32 == p_app->data_type */
            signal_data[signal_idx].samples.p_i32 = converted_samples.i32[signal_idx];
        }
        signal_data[signal_idx].count = 0;
    }

    /* Process all available samples. */
    const uint8_t samples_available_for_all_signals = ((1 << p_app->signals_num) - 1);
    uint8_t samples_available = samples_available_for_all_signals;
    uint16_t signal_sample_idx[AS7058_APPMGR_MAX_APP_SIGNAL_NUM] = {0};
    uint8_t first_iteration_done = FALSE;
    uint8_t accelerometer_data_passed = FALSE;
    uint8_t signal_data_has_data = FALSE;
    uint8_t converted_samples_full = FALSE;
    as7058_appmgr_sample_metadata_t signal_data_metadata[AS7058_APPMGR_MAX_APP_SIGNAL_NUM];
    while (samples_available) {
        /* During each iteration of this loop, a maximum of 1 sample is processed per signal. For each signal, the
         * sample is either read from excess sample storage, read from the extracted sample data, or no more samples are
         * available for the signal. For samples read from the extracted sample data, signal sample preprocessing (if
         * enabled) and the generation of a metadata instance (containing the PD offset and LED currents) are performed.
         * (For samples stored in the excess sample storage, these steps have already performed before they ware added
         * to the storage.)
         *
         * The newly processed data is first stored in temporary buffers (new_samples/new_samples_metadata) before it is
         * added to signal_data/converted_samples as it may be necessary to first send the existing samples in
         * signal_data/converted_samples to the application and clear the buffers before the new samples can be added.
         * This is the case when the newly processed data has different metadata (i.e. different PD offset or LED
         * currents), when a buffer of converted_samples is full, or when the loop is about to stop iterating because no
         * more samples are available for any signal. (The metadata of the samples currently stored in
         * signal_data/converted_samples are stored in signal_data_metadata.)
         *
         * Once signal_data/converted_samples is cleared if needed, the newly processed data can be added to it. (If the
         * newly processed data does not contain a sample for every signal, the data is put in excess sample storage
         * instead, provided that the feature is available for the application). */

        uint8_t metadata_changed = FALSE;
        as7058_appmgr_sample_t new_samples[AS7058_APPMGR_MAX_APP_SIGNAL_NUM] = {0, 0, 0};
        as7058_appmgr_sample_metadata_t new_samples_metadata[AS7058_APPMGR_MAX_APP_SIGNAL_NUM];
        for (uint8_t signal_idx = 0; signal_idx < p_app->signals_num; signal_idx++) {
            as7058_sub_sample_ids_t channel = p_app->p_signal_mapping[signal_idx];

            if (!first_iteration_done && p_app->p_excess_samples && p_app->p_excess_samples[signal_idx].has_data) {
                /* During the first iteration of the while loop, process the excess sample of the signal, if one is
                 * stored. Since there can only be one excess sample per signal, all excess samples (that were present
                 * at the time the function was invoked) are guaranteed to have been consumed after the first while loop
                 * iteration. */
                new_samples[signal_idx] = p_app->p_excess_samples[signal_idx].sample;
                new_samples_metadata[signal_idx] = p_app->p_excess_samples[signal_idx].metadata;
                p_app->p_excess_samples[signal_idx].has_data = FALSE;
            } else if (signal_sample_idx[signal_idx] < get_sample_count_for_channel(channel, pp_extract_result)) {
                /* If not processing an excess sample, take the next sample of the signal from the extracted samples
                 * buffer. */
                M_CHECK_SUCCESS(get_sample_with_metadata(channel, signal_sample_idx[signal_idx], pp_extract_result,
                                                         p_agc_statuses, agc_statuses_num, &new_samples[signal_idx],
                                                         &new_samples_metadata[signal_idx]));

                /* Perform signal sample preprocessing. */
                M_CHECK_SUCCESS(perform_enabled_preprocessing(&new_samples[signal_idx],
                                                              &new_samples_metadata[signal_idx], channel, p_app));

                signal_sample_idx[signal_idx]++;
            } else {
                /* No more samples exist for the current signal. */
                samples_available &= ~(1 << signal_idx);
                continue;
            }

            if (signal_data_has_data) {
                /* Check if the valid metadata fields of the samples currently stored in signal_data/converted_samples
                 * are different from the metadata fields of the newly processed data. If there is a change, the data
                 * currently stored in signal_data/converted_samples needs to be provided to the app before the new data
                 * can be inserted. */
                if ((new_samples_metadata[signal_idx].flags.pd_offset_current_valid !=
                     signal_data_metadata[signal_idx].flags.pd_offset_current_valid) ||
                    (new_samples_metadata[signal_idx].flags.led_current_valid !=
                     signal_data_metadata[signal_idx].flags.led_current_valid)) {
                    /* Metadata field validity flags are expected not to change during the measurement. */
                    return ERR_DATA;
                }
                if ((new_samples_metadata[signal_idx].flags.pd_offset_current_valid &&
                     (new_samples_metadata[signal_idx].pd_offset_current !=
                      signal_data_metadata[signal_idx].pd_offset_current)) ||
                    (new_samples_metadata[signal_idx].flags.led_current_valid &&
                     (new_samples_metadata[signal_idx].led_current != signal_data_metadata[signal_idx].led_current))) {
                    metadata_changed = TRUE;
                }
            }
        }

        if (signal_data_has_data && (metadata_changed || converted_samples_full || !samples_available)) {
            /* Send the data currently stored in signal_data/converted_samples to the app. The data needs to be sent in
             * three cases: When the newly processed data has different metadata than the samples current stored in
             * signal_data. When one of the buffers of converted_samples is full. When the while loop is about to
             * terminate. */

            /* Create AGC statuses pointer array for app. */
            agc_status_t app_agc_statuses[AS7058_APPMGR_MAX_APP_SIGNAL_NUM];
            const agc_status_t *p_app_agc_statuses[AS7058_APPMGR_MAX_APP_SIGNAL_NUM];
            for (uint8_t signal_idx = 0; signal_idx < p_app->signals_num; signal_idx++) {
                if (signal_data[signal_idx].count > 0) {
                    /* Generate status using previously passed current values (if available). */
                    err_code_t agc_status_result = generate_agc_status(
                        signal_data_metadata[signal_idx],
                        ((*p_app->p_last_metadata_valid & (1 << signal_idx)) ? &p_app->p_last_metadata[signal_idx]
                                                                             : NULL),
                        &app_agc_statuses[signal_idx]);
                    if (agc_status_result != ERR_NO_DATA) {
                        M_CHECK_SUCCESS(agc_status_result);
                        p_app_agc_statuses[signal_idx] = &app_agc_statuses[signal_idx];
                    } else {
                        p_app_agc_statuses[signal_idx] = NULL;
                    }
                } else {
                    /* Do not generate an AGC status for signals that do not have a sample stored in
                     * signal_data/converted_samples as signal_data_metadata[signal_idx] is invalid for signals without
                     * samples. */
                    p_app_agc_statuses[signal_idx] = NULL;
                }
            }

            /* Pass data to app. */
            M_CHECK_SUCCESS(p_app->p_set_input(p_app->data_type, signal_data, p_app_agc_statuses, p_app->signals_num,
                                               (!accelerometer_data_passed ? p_acc_samples : NULL),
                                               (!accelerometer_data_passed ? acc_samples_num : 0), p_execution_status));
            accelerometer_data_passed = TRUE;

            for (uint8_t signal_idx = 0; signal_idx < p_app->signals_num; signal_idx++) {
                if (signal_data[signal_idx].count > 0) {
                    /* If the metadata of the signal is valid (i.e. there are samples for this signal stored in
                     * signal_data/converted_samples), store the passed current values for later generation of AGC
                     * change states. */
                    p_app->p_last_metadata[signal_idx] = signal_data_metadata[signal_idx];
                    (*p_app->p_last_metadata_valid) |= (1 << signal_idx);
                }

                /* Reset signal_data/converted_samples. */
                signal_data[signal_idx].count = 0;
            }

            /* signal_data/converted_samples has been reset. */
            signal_data_has_data = FALSE;
            converted_samples_full = FALSE;
        }

        if (samples_available) {
            if (samples_available_for_all_signals == samples_available || !p_app->p_excess_samples) {
                /* Add all samples to signal_data/converted_samples since an equal number of samples is present for all
                 * signals or since the excess sample functionality is unavailable for this app. */
                for (uint8_t signal_idx = 0; signal_idx < p_app->signals_num; signal_idx++) {
                    if (!(samples_available & (1 << signal_idx))) {
                        /* Skip signals which do not have samples available. If the excess sample functionality is
                         * unavailable, there might be signals that do not have samples available. */
                        continue;
                    }

                    /* Perform data type conversion and store the converted value in signal_data/converted_samples. */
                    if (BIO_SIGNAL_SAMPLES_TYPE_U16 == p_app->data_type) {
                        converted_samples.u16[signal_idx][signal_data[signal_idx].count] =
                            convert_sample_u16(new_samples[signal_idx]);
                    } else if (BIO_SIGNAL_SAMPLES_TYPE_U32 == p_app->data_type) {
                        converted_samples.u32[signal_idx][signal_data[signal_idx].count] =
                            convert_sample_u32(new_samples[signal_idx]);
                    } else { /* BIO_SIGNAL_SAMPLES_TYPE_I32 == p_app->data_type */
                        converted_samples.i32[signal_idx][signal_data[signal_idx].count] =
                            convert_sample_i32(new_samples[signal_idx]);
                    }
                    signal_data[signal_idx].count++;

                    /* Save the current values of the inserted sample in signal_data_metadata. All samples of a signal
                     * present in signal_data/converted_samples at a time are guaranteed to have the same associated
                     * current values. */
                    signal_data_metadata[signal_idx] = new_samples_metadata[signal_idx];

                    /* signal_data/converted_samples now contains data to send. */
                    signal_data_has_data = TRUE;
                    if ((BIO_SIGNAL_SAMPLES_TYPE_U16 == p_app->data_type &&
                         AS7058_APPMGR_CONVERTED_SAMPLES_MAX_U16 == signal_data[signal_idx].count) ||
                        (BIO_SIGNAL_SAMPLES_TYPE_U32 == p_app->data_type &&
                         AS7058_APPMGR_CONVERTED_SAMPLES_MAX_U32 == signal_data[signal_idx].count) ||
                        (/* BIO_SIGNAL_SAMPLES_TYPE_I32 == p_app->data_type */
                         AS7058_APPMGR_CONVERTED_SAMPLES_MAX_I32 == signal_data[signal_idx].count)) {
                        /* The corresponding converted_samples buffer is full and needs to be cleared before further
                         * samples can be added. */
                        converted_samples_full = TRUE;
                    }
                }
            } else {
                /* Store samples in excess samples, since functionality is available for this app and the number of
                 * samples present is not equal for all signals. */
                for (uint8_t signal_idx = 0; signal_idx < p_app->signals_num; signal_idx++) {
                    if (samples_available & (1 << signal_idx)) {
                        if (p_app->p_excess_samples[signal_idx].has_data) {
                            /* Excess sample storage can only hold one item per signal. */
                            return ERR_OVERFLOW;
                        }
                        p_app->p_excess_samples[signal_idx].sample = new_samples[signal_idx];
                        p_app->p_excess_samples[signal_idx].metadata = new_samples_metadata[signal_idx];
                        p_app->p_excess_samples[signal_idx].has_data = TRUE;
                    }
                }
            }
        }

        /* Whenever reaching this point, the first iteration of the loop has been done. */
        first_iteration_done = TRUE;
    }

    /* Pass accelerometer data if there are any accelerometer samples and they have not been passed yet. This only
     * occurs when there are no PPG samples. */
    if (acc_samples_num > 0 && !accelerometer_data_passed) {
        const agc_status_t *p_app_agc_statuses[AS7058_APPMGR_MAX_APP_SIGNAL_NUM];
        for (uint8_t signal_idx = 0; signal_idx < p_app->signals_num; signal_idx++) {
            signal_data[signal_idx].count = 0;
            p_app_agc_statuses[signal_idx] = NULL;
        }
        M_CHECK_SUCCESS(p_app->p_set_input(p_app->data_type, signal_data, p_app_agc_statuses, p_app->signals_num,
                                           p_acc_samples, acc_samples_num, p_execution_status));
    }

    return ERR_SUCCESS;
}

#ifndef AS7058_APPMGR_DISABLE_STREAM
/*!
 * \brief Checks whether the AGC statuses changed in a way that require transmission of the AGC statuses.
 *
 * \note This function is copied from as7058_raw_app.c
 *
 * \param[in] p_new_agc_statuses Pointer to the array containing the current AGC statuses.
 * \param[in] agc_statuses_num   Number of items in the AGC statuses array.
 *
 * \retval ::TRUE  AGC statuses transmission required.
 * \retval ::FALSE AGC statuses transmission not required.
 */
static uint8_t check_agc_statuses_change(const agc_status_t *p_new_agc_statuses, uint8_t agc_statuses_num)
{
    if (NULL == p_new_agc_statuses || agc_statuses_num > AGC_MAX_CHANNEL_CNT) {
        return FALSE;
    }

    uint8_t agc_statuses_changed = FALSE;
    if (g_agc_statuses_num != AS7058_APPMGR_AGC_STATUSES_NUM_UNKNOWN) {
        /* When g_agc_statuses_num is not set to AS7058_APPMGR_AGC_STATUSES_NUM_UNKNOWN, AGC status information has
         * been received before and g_last_agc_statuses contains valid data. */

        if (agc_statuses_num != g_agc_statuses_num) {
            /* Number of AGC statuses should never change during a measurement, so this should never happen. */
            return FALSE;
        }

        for (uint8_t i = 0; i < agc_statuses_num; i++) {
            const agc_status_t *p_new = &p_new_agc_statuses[i];
            const agc_status_t *p_last = &g_last_agc_statuses[i];

            /* For detecting an AGC status change, all fields of the AGC status are looked at separately. If the value
             * of a current field changes, the AGC status is always considered to have changed. If a change state
             * changes to a value other than AGC_STATE_UNCHANGED, the AGC status is also considered to have changed.
             * The check for AGC_STATE_UNCHANGED is implemented to suppress AGC status changes that contain no
             * information. (For example, when the PD offset current is increased, the AGC status of that AGC execution
             * contains the increased PD offset current and its PD offset change state is set to AGC_STATE_INCREASED.
             * Assuming no further PD offset current changes, the AGC status of the next AGC execution contains the same
             * PD offset current as before, but the change state changes to AGC_STATE_UNCHANGED. If the check for
             * AGC_STATE_UNCHANGED hadn't been implemented, this would also have been considered an AGC status change.
             *
             * No special handling for AGC_STATE_NOT_CONTROLLED and AGC_STATE_UNDEFINED is required as if one of these
             * statuses is present in a change state field, it is also present in that field in each other AGC status
             * that is generated throughout the entire measurement. The corresponding current value also remains set to
             * a constant value throughout the entire measurement.
             *
             * This information is valid for version 2.0.0 of the AGC algorithm. */

            uint8_t led_status_changed =
                (p_new->led_change != p_last->led_change) && (p_new->led_change != AGC_STATE_UNCHANGED);
            uint8_t led_current_changed = p_new->led_current != p_last->led_current;
            uint8_t pd_offset_status_changed = (p_new->pd_offset_change != p_last->pd_offset_change) &&
                                               (p_new->pd_offset_change != AGC_STATE_UNCHANGED);
            uint8_t pd_offset_current_changed = p_new->pd_offset_current != p_last->pd_offset_current;

            if (led_status_changed || led_current_changed || pd_offset_status_changed || pd_offset_current_changed) {
                agc_statuses_changed = TRUE;
                break;
            }
        }
    } else {
        /* When g_agc_statuses_num is still set to AS7058_APPMGR_AGC_STATUSES_NUM_UNKNOWN, this is the first time we
         * receive AGC status information. */

        g_agc_statuses_num = agc_statuses_num;

        /* Always send first AGC statuses if data is available. */
        if (agc_statuses_num > 0) {
            agc_statuses_changed = TRUE;
        }
    }

    if (agc_statuses_changed) {
        memcpy(&g_last_agc_statuses, p_new_agc_statuses, sizeof(agc_status_t) * agc_statuses_num);
    }

    return agc_statuses_changed;
}

/*!
 * \brief Checks whether the status event changed.
 *
 * \note This function is copied from as7058_raw_app.c
 *
 * \param[in] new_status_events Current status event.
 *
 * \retval ::TRUE  Status event transmission required.
 * \retval ::FALSE Status event transmission not required.
 */
static uint8_t check_status_events_change(as7058_status_events_t new_status_events)
{
    const as7058_status_events_t empty_status_events = {
        .status_seq = 0,
        .status_led = 0,
        .status_asata = 0,
        .status_asatb = 0,
        .status_vcsel = 0,
        .status_vcsel_vss = 0,
        .status_vcsel_vdd = 0,
        .status_leadoff = 0,
        .status_iir = 0,
    };
    uint8_t status_events_set =
        (memcmp(&new_status_events, &empty_status_events, sizeof(as7058_status_events_t)) ? TRUE : FALSE);

    return status_events_set;
}
#endif

#ifndef AS7058_APPMGR_DISABLE_RAW
/*!
 * \brief Chip-specific wrapper function that is registered as the start function of the raw app. Calls the actual start
 *        function of the raw app, which does not conform to the standard bio app function interface.
 */
static err_code_t handle_raw_app_start(const uint32_t *p_signal_sample_periods_us, uint8_t signal_num,
                                       uint32_t acc_sample_period_us)
{
    M_UNUSED_PARAM(p_signal_sample_periods_us);
    M_UNUSED_PARAM(signal_num);
    M_UNUSED_PARAM(acc_sample_period_us);

    return as7058_raw_app_start(g_ppg_sample_period_us, g_ecg_seq1_sample_period_us, g_ecg_seq2_sample_period_us,
                                g_extract_state.fifo_map);
}

/*!
 * \brief Chip-specific function called in state ::AS7058_APPMGR_STATE_PROCESSING to provide data to the chip-specific
 *        raw data app.
 */
static err_code_t handle_raw_app_set_input(const uint8_t *p_fifo_data, uint16_t fifo_data_size,
                                           as7058_status_events_t status_events, const agc_status_t *p_agc_statuses,
                                           uint16_t agc_statuses_num, const vs_acc_data_t *p_acc_samples,
                                           uint16_t acc_samples_num, uint8_t ext_event_count,
                                           bio_execution_status_t *p_result)
{
    return as7058_raw_app_set_input(p_fifo_data, fifo_data_size, status_events, p_agc_statuses, agc_statuses_num,
                                    p_acc_samples, acc_samples_num, ext_event_count, p_result);
}
#endif

#ifndef AS7058_APPMGR_DISABLE_STREAM
/*!
 * \brief Chip-specific wrapper function that is registered as the start function of the streaming app. Calls the actual
 *        start function of the streaming app, which does not conform to the standard bio app function interface.
 */
static err_code_t handle_bio_stream_start(const uint32_t *p_signal_sample_periods_us, uint8_t signal_num,
                                          uint32_t acc_sample_period_us)
{
    M_UNUSED_PARAM(p_signal_sample_periods_us);
    M_UNUSED_PARAM(signal_num);
    M_UNUSED_PARAM(acc_sample_period_us);

    return bio_stream_start();
}

/*!
 * \brief Chip-specific function called in state ::AS7058_APPMGR_STATE_PROCESSING to provide to the streaming app.
 */
static err_code_t handle_bio_stream_set_input(const as7058_appmgr_extract_result_t *pp_extract_result,
                                              const uint8_t *p_fifo_data, uint16_t fifo_data_size,
                                              as7058_status_events_t status_events, const agc_status_t *p_agc_statuses,
                                              uint16_t agc_statuses_num, const vs_acc_data_t *p_acc_samples,
                                              uint16_t acc_samples_num, uint8_t ext_event_count,
                                              bio_execution_status_t *p_result)
{
    if (check_agc_statuses_change(p_agc_statuses, agc_statuses_num)) {
        /* Create AGC statuses item. */
        M_CHECK_SUCCESS(bio_stream_set_input(AS7058_APPMGR_STREAM_APP_ID_AGC, p_agc_statuses,
                                             agc_statuses_num * sizeof(agc_status_t), BIO_STREAM_SEND_OPTION_FLAG_NONE,
                                             p_result));
    }

    if (fifo_data_size) {
        /* Create FIFO data item. */
        // TODO: Add support for BIO_STREAM_SEND_OPTION_FLAG_CLOSE_PACKAGE after a time of 1sec
        M_CHECK_SUCCESS(bio_stream_set_input(AS7058_APPMGR_STREAM_APP_ID_FIFO, p_fifo_data, fifo_data_size,
                                             BIO_STREAM_SEND_OPTION_FLAG_ALLOW_EXTENSION, p_result));
    }

    if (check_status_events_change(status_events)) {
        /* Create sensor events item. */
        M_CHECK_SUCCESS(bio_stream_set_input(AS7058_APPMGR_STREAM_APP_ID_SENSOR_EVENTS, &status_events,
                                             sizeof(status_events), BIO_STREAM_SEND_OPTION_FLAG_NONE, p_result));
    }

    if (acc_samples_num) {
        /* Create accelerometer samples item. */
        M_CHECK_SUCCESS(bio_stream_set_input(AS7058_APPMGR_STREAM_APP_ID_ACC, p_acc_samples,
                                             acc_samples_num * sizeof(vs_acc_data_t),
                                             BIO_STREAM_SEND_OPTION_FLAG_ALLOW_EXTENSION, p_result));
    }

    if (ext_event_count) {
        /* Create external event count item. */
        M_CHECK_SUCCESS(bio_stream_set_input(AS7058_APPMGR_STREAM_APP_ID_EXT_EVENTS, &ext_event_count,
                                             sizeof(ext_event_count), BIO_STREAM_SEND_OPTION_FLAG_NONE, p_result));
    }

    /* Create items for each extracted samples (after preprocessing, if enabled). */
    for (as7058_sub_sample_ids_t channel = AS7058_SUB_SAMPLE_ID_PPG1_SUB1; channel < AS7058_SUB_SAMPLE_ID_NUM;
         channel++) {
        uint16_t sample_count = get_sample_count_for_channel(channel, pp_extract_result);

        for (uint16_t sample_idx = 0; sample_idx < sample_count; sample_idx++) {
            /* Get ADC value and SAR PD offset from extraction results. */
            as7058_appmgr_sample_t sample;
            as7058_appmgr_sample_metadata_t metadata;
            M_CHECK_SUCCESS(get_sample_with_metadata(channel, sample_idx, pp_extract_result, p_agc_statuses,
                                                     agc_statuses_num, &sample, &metadata));

            /* Perform signal sample preprocessing. */
            M_CHECK_SUCCESS(perform_enabled_preprocessing(&sample, &metadata, channel,
                                                          &g_app_table[AS7058_APPMGR_INTERNAL_APP_ID_STREAM]));

            as7058_appmgr_sample_t masked_sample = sample & AS7058_APPMGR_STREAM_APP_SAMPLE_ADC_VALUE_BITS_MASK;
            if (masked_sample != sample) {
                /* In unlikely edge cases, a PD offset compensated-sample may not be representable using 24 bits. */
                return ERR_ARGUMENT;
            }

            /* Create item. */
            uint32_t item = masked_sample | ((metadata.flags.pd_offset_current_valid ? metadata.pd_offset_current : 0)
                                             << AS7058_APPMGR_STREAM_APP_SAMPLE_PD_OFFSET_BITS_SHIFT);
            uint8_t item_id =
                (channel - AS7058_SUB_SAMPLE_ID_PPG1_SUB1) + AS7058_APPMGR_STREAM_APP_ID_SAMPLES_PPG1_SUB1;
            M_CHECK_SUCCESS(bio_stream_set_input(item_id, &item, sizeof(item),
                                                 BIO_STREAM_SEND_OPTION_FLAG_ALLOW_EXTENSION, p_result));
        }
    }

    return ERR_SUCCESS;
}
#endif

/******************************************************************************
 *                              GLOBAL FUNCTIONS                              *
 ******************************************************************************/

AS7058_APPMGR_FUNC_DEFN err_code_t as7058_appmgr_initialize(void)
{
    /* Reset global variables. */
    g_enabled_apps = 0;
    g_configured_preprocessing = 0;
    for (uint8_t mapping_idx = 0; mapping_idx < AS7058_APPMGR_CHANNEL_AGC_NUM; mapping_idx++) {
        g_agc_mapping[mapping_idx] = AS7058_APPMGR_AGC_MAPPING_DISABLED;
    }
    g_executable_apps = 0;
    g_pending_ext_event_count = 0;
#ifndef AS7058_APPMGR_DISABLE_STREAM
    g_agc_statuses_num = AS7058_APPMGR_AGC_STATUSES_NUM_UNKNOWN;
#endif

    M_CHECK_SUCCESS(clear_measurement_config());

    /* Initialize all apps. */
    for (as7058_appmgr_internal_app_id_t internal_id = 0; internal_id < AS7058_APPMGR_INTERNAL_APP_ID_NUM;
         internal_id++) {
        const as7058_appmgr_app_definition_t *p_app = &g_app_table[internal_id];

        for (uint8_t signal_idx = 0; signal_idx < p_app->signals_num; signal_idx++) {
            if (p_app->p_signal_mapping) {
                p_app->p_signal_mapping[signal_idx] = 0;
            }
            if (p_app->p_excess_samples) {
                p_app->p_excess_samples[signal_idx].has_data = FALSE;
                p_app->p_excess_samples[signal_idx].sample = 0;
                p_app->p_excess_samples[signal_idx].metadata.flags.pd_offset_current_valid = FALSE;
                p_app->p_excess_samples[signal_idx].metadata.flags.led_current_valid = FALSE;
                p_app->p_excess_samples[signal_idx].metadata.pd_offset_current = 0;
                p_app->p_excess_samples[signal_idx].metadata.led_current = 0;
            }
            if (p_app->p_last_metadata) {
                p_app->p_last_metadata[signal_idx].flags.pd_offset_current_valid = FALSE;
                p_app->p_last_metadata[signal_idx].flags.led_current_valid = FALSE;
                p_app->p_last_metadata[signal_idx].pd_offset_current = 0;
                p_app->p_last_metadata[signal_idx].led_current = 0;
            }
        }
        if (p_app->p_enabled_preprocessing) {
            *p_app->p_enabled_preprocessing = 0;
        }
        if (p_app->p_last_metadata_valid) {
            *p_app->p_last_metadata_valid = 0;
        }

        M_CHECK_APP_DEFINITION(p_app->p_initialize);
        M_CHECK_SUCCESS(p_app->p_initialize());
    }

    g_state = AS7058_APPMGR_STATE_CONFIGURATION;

    return ERR_SUCCESS;
}

AS7058_APPMGR_FUNC_DEFN err_code_t as7058_appmgr_enable_apps(uint32_t enabled_apps)
{
    M_CHECK_STATE(AS7058_APPMGR_STATE_CONFIGURATION);

    if (enabled_apps >= (1 << AS7058_APPMGR_APP_ID_NUM)) {
        /* Invalid bits set. */
        return ERR_ARGUMENT;
    }

    uint32_t internal_flags = 0;
    uint32_t enabled_apps_unprocessed = enabled_apps;
    as7058_appmgr_app_id_t public_id = 0;
    while (enabled_apps_unprocessed) {
        if (enabled_apps_unprocessed & 1) {
            as7058_appmgr_internal_app_id_t internal_id;
            M_CHECK_SUCCESS(get_internal_app_id_for_public_app_id(public_id, &internal_id));

            const as7058_appmgr_app_definition_t *p_app = &g_app_table[internal_id];

            /* Check whether apps are enabled that cannot be enabled concurrently. */
            uint32_t excluded_apps = p_app->excluded_apps;
            if (enabled_apps & excluded_apps) {
                return ERR_ARGUMENT;
            }

            internal_flags |= M_ID_TO_FLAG(internal_id);
        }

        public_id++;
        enabled_apps_unprocessed >>= 1;
    }

    g_enabled_apps = internal_flags;

    return ERR_SUCCESS;
}

AS7058_APPMGR_FUNC_DEFN err_code_t as7058_appmgr_set_signal_routing(as7058_appmgr_app_id_t app,
                                                                    const as7058_sub_sample_ids_t *p_channels,
                                                                    uint8_t channels_num)
{
    M_CHECK_STATE(AS7058_APPMGR_STATE_CONFIGURATION);
    M_CHECK_PUBLIC_APP_ID(app);

    as7058_appmgr_internal_app_id_t internal_id;
    M_CHECK_SUCCESS(get_internal_app_id_for_public_app_id(app, &internal_id));

    const as7058_appmgr_app_definition_t *p_app = &g_app_table[internal_id];

    if (channels_num != p_app->signals_num) {
        /* Signal count mismatch. */
        return ERR_SIZE;
    }

    if (p_app->signals_num > 0) {
        M_CHECK_NULL_POINTER(p_channels);
        M_CHECK_APP_DEFINITION(p_app->p_signal_mapping);
    }

    for (uint8_t channel = 0; channel < channels_num; channel++) {
        if (AS7058_APPMGR_CHANNEL_ID_DISABLED == p_channels[channel] ||
            (p_channels[channel] >= AS7058_APPMGR_CHANNEL_ID_FIRST &&
             p_channels[channel] <= AS7058_APPMGR_CHANNEL_ID_LAST)) {
            /* Copy signal mapping to internal storage. */
            p_app->p_signal_mapping[channel] = p_channels[channel];
        } else {
            /* Channel not within valid range. */
            return ERR_ARGUMENT;
        }
    }

    return ERR_SUCCESS;
}

AS7058_APPMGR_FUNC_DEFN err_code_t as7058_appmgr_configure_app(as7058_appmgr_app_id_t app, const void *p_config,
                                                               uint8_t size)
{
    M_CHECK_STATE(AS7058_APPMGR_STATE_CONFIGURATION);
    M_CHECK_PUBLIC_APP_ID(app);
    M_CHECK_NULL_POINTER(p_config);

    as7058_appmgr_internal_app_id_t internal_id;
    M_CHECK_SUCCESS(get_internal_app_id_for_public_app_id(app, &internal_id));

    const as7058_appmgr_app_definition_t *p_app = &g_app_table[internal_id];
    M_CHECK_APP_DEFINITION(p_app->p_configure);

    return p_app->p_configure(p_config, size);
}

AS7058_APPMGR_FUNC_DEFN err_code_t as7058_appmgr_enable_preprocessing(as7058_appmgr_app_id_t app, uint32_t flags)
{
    M_CHECK_STATE(AS7058_APPMGR_STATE_CONFIGURATION);
    M_CHECK_PUBLIC_APP_ID(app);

    as7058_appmgr_internal_app_id_t internal_id;
    M_CHECK_SUCCESS(get_internal_app_id_for_public_app_id(app, &internal_id));

    const as7058_appmgr_app_definition_t *p_app = &g_app_table[internal_id];

    if (!p_app->p_enabled_preprocessing) {
        /* App does not support preprocessing features. */
        if (0 == flags) {
            return ERR_SUCCESS;
        } else {
            return ERR_ARGUMENT;
        }
    }

    if (flags > AS7058_APPMGR_PREPROCESSING_FLAG_PD_OFFSET_COMPENSATION) {
        /* Provided flags are invalid. */
        return ERR_ARGUMENT;
    }

    *p_app->p_enabled_preprocessing = flags;

    return ERR_SUCCESS;
}

err_code_t as7058_appmgr_configure_preprocessing(as7058_appmgr_preprocessing_id_t preprocessing, const void *p_config,
                                                 uint16_t size)
{
    M_CHECK_STATE(AS7058_APPMGR_STATE_CONFIGURATION);
    M_CHECK_NULL_POINTER(p_config);

    if (AS7058_APPMGR_PREPROCESSING_ID_PD_OFFSET_COMPENSATION == preprocessing) {
        if (size != sizeof(as7058_appmgr_preprocessing_configuration_pd_offset_compensation_t)) {
            return ERR_SIZE;
        }

        M_CHECK_SUCCESS(configure_pd_offset_compensation(
            (const as7058_appmgr_preprocessing_configuration_pd_offset_compensation_t *)p_config));
    } else {
        /* Invalid preprocessing feature ID. */
        return ERR_ARGUMENT;
    }

    /* Mark preprocessing feature as configured. */
    g_configured_preprocessing |= (1 << preprocessing);

    return ERR_SUCCESS;
}

AS7058_APPMGR_FUNC_DEFN err_code_t as7058_appmgr_start_processing(as7058_meas_config_t measurement_config,
                                                                  uint32_t acc_sample_period_us)
{
    M_CHECK_STATE(AS7058_APPMGR_STATE_CONFIGURATION);

    g_executable_apps = 0;
    g_pending_ext_event_count = 0;
#ifndef AS7058_APPMGR_DISABLE_STREAM
    g_agc_statuses_num = AS7058_APPMGR_AGC_STATUSES_NUM_UNKNOWN;
#endif

    M_CHECK_SUCCESS(process_measurement_config(measurement_config));

    /* Create AGC mapping. */
    for (uint8_t mapping_idx = 0; mapping_idx < AS7058_APPMGR_CHANNEL_AGC_NUM; mapping_idx++) {
        g_agc_mapping[mapping_idx] = AS7058_APPMGR_AGC_MAPPING_DISABLED;
    }
    for (uint8_t agc_idx = 0; agc_idx < AGC_MAX_CHANNEL_CNT; agc_idx++) {
        as7058_sub_sample_ids_t channel = measurement_config.agc_channels[agc_idx];
        uint8_t mapping_idx = channel - AS7058_APPMGR_CHANNEL_ID_AGC_FIRST;
        if (channel >= AS7058_APPMGR_CHANNEL_ID_AGC_FIRST && channel <= AS7058_APPMGR_CHANNEL_ID_AGC_LAST) {
            if (AS7058_APPMGR_AGC_MAPPING_DISABLED == g_agc_mapping[mapping_idx]) {
                g_agc_mapping[mapping_idx] = agc_idx;
            } else {
                /* Multiple AGC instances mapped to a single channel. */
                return ERR_CONFIG;
            }
        } else if (channel != AS7058_APPMGR_CHANNEL_ID_DISABLED) {
            /* AGC instance mapped to a channel that does not support AGC. */
            return ERR_CONFIG;
        }
    }

    /* Start enabled apps. */
    for (as7058_appmgr_internal_app_id_t internal_id = 0; internal_id < AS7058_APPMGR_INTERNAL_APP_ID_NUM;
         internal_id++) {
        if (!M_INTERNAL_APP_ID_IS_ENABLED(internal_id)) {
            /* Skip disabled apps. */
            continue;
        }

        const as7058_appmgr_app_definition_t *p_app = &g_app_table[internal_id];
        M_CHECK_APP_DEFINITION(p_app->p_start);
        M_CHECK_APP_DEFINITION(p_app->signals_num <= AS7058_APPMGR_MAX_APP_SIGNAL_NUM);

        if (p_app->p_enabled_preprocessing) {
            if ((*p_app->p_enabled_preprocessing & g_configured_preprocessing) != *p_app->p_enabled_preprocessing) {
                /* App uses preprocessing feature that has not been configured. */
                return ERR_CONFIG;
            }
        }

        /* Reset last metadata valid flags. */
        if (p_app->p_last_metadata_valid) {
            *p_app->p_last_metadata_valid = 0;
        }

        uint32_t signal_sample_periods_us[AS7058_APPMGR_MAX_APP_SIGNAL_NUM];

        for (uint8_t signal_idx = 0; signal_idx < p_app->signals_num; signal_idx++) {
            as7058_sub_sample_ids_t channel_id = p_app->p_signal_mapping[signal_idx];

            /* Get sample period and implicitly check whether signal routing is valid as get_sample_period_for_channel
             * is required to return an error when the channel selection is invalid given the current measurement
             * configuration. */
            M_CHECK_SUCCESS(get_sample_period_for_channel(channel_id, &signal_sample_periods_us[signal_idx]));

            /* Reset excess sample storage. */
            if (p_app->p_excess_samples) {
                p_app->p_excess_samples[signal_idx].has_data = FALSE;
                p_app->p_excess_samples[signal_idx].sample = 0;
                p_app->p_excess_samples[signal_idx].metadata.flags.pd_offset_current_valid = FALSE;
                p_app->p_excess_samples[signal_idx].metadata.flags.led_current_valid = FALSE;
                p_app->p_excess_samples[signal_idx].metadata.pd_offset_current = 0;
                p_app->p_excess_samples[signal_idx].metadata.led_current = 0;
            }

            /* Reset last metadata. */
            if (p_app->p_last_metadata) {
                p_app->p_last_metadata[signal_idx].flags.pd_offset_current_valid = FALSE;
                p_app->p_last_metadata[signal_idx].flags.led_current_valid = FALSE;
                p_app->p_last_metadata[signal_idx].pd_offset_current = 0;
                p_app->p_last_metadata[signal_idx].led_current = 0;
            }
        }

        M_CHECK_SUCCESS(p_app->p_start(signal_sample_periods_us, p_app->signals_num, acc_sample_period_us));
    }

    g_state = AS7058_APPMGR_STATE_PROCESSING;

    return ERR_SUCCESS;
}

AS7058_APPMGR_FUNC_DEFN err_code_t as7058_appmgr_set_input(const uint8_t *p_fifo_data, uint16_t fifo_data_size,
                                                           as7058_status_events_t status_events,
                                                           const agc_status_t *p_agc_statuses, uint8_t agc_statuses_num,
                                                           const vs_acc_data_t *p_acc_samples, uint16_t acc_samples_num,
                                                           uint8_t *p_ready_for_execution)
{
    M_CHECK_STATE(AS7058_APPMGR_STATE_PROCESSING);

    if (fifo_data_size > 0) {
        M_CHECK_NULL_POINTER(p_fifo_data);
    }
    if (agc_statuses_num > 0) {
        M_CHECK_NULL_POINTER(p_agc_statuses);
        M_CHECK_ARGUMENT_LOWER_EQUAL(agc_statuses_num, AGC_MAX_CHANNEL_CNT);
    }
    if (acc_samples_num > 0) {
        M_CHECK_NULL_POINTER(p_acc_samples);
    }
    M_CHECK_NULL_POINTER(p_ready_for_execution);

    uint8_t ext_event_count = g_pending_ext_event_count;
    g_pending_ext_event_count = 0;

#if defined(AS7058_APPMGR_DISABLE_RAW) && defined(AS7058_APPMGR_DISABLE_STREAM)
    M_UNUSED_PARAM(status_events);
    M_UNUSED_PARAM(ext_event_count);
#endif

    /* Extract all samples in FIFO data. */
    as7058_appmgr_extract_result_t p_extract_result;
    M_CHECK_SUCCESS(extract_samples_from_fifo_data(p_fifo_data, fifo_data_size, &p_extract_result));

    for (as7058_appmgr_internal_app_id_t internal_id = 0; internal_id < AS7058_APPMGR_INTERNAL_APP_ID_NUM;
         internal_id++) {
        if (!M_INTERNAL_APP_ID_IS_ENABLED(internal_id)) {
            /* Skip disabled app. */
            continue;
        }

        bio_execution_status_t execution_status = BIO_EXECUTION_STATUS_NOT_EXECUTABLE;

#ifndef AS7058_APPMGR_DISABLE_RAW
        if (AS7058_APPMGR_INTERNAL_APP_ID_RAW == internal_id) {
            /* Special handling of raw app as it receives data from Chip Library as-is. */
            M_CHECK_SUCCESS(handle_raw_app_set_input(p_fifo_data, fifo_data_size, status_events, p_agc_statuses,
                                                     agc_statuses_num, p_acc_samples, acc_samples_num, ext_event_count,
                                                     &execution_status));
        } else
#endif
#ifndef AS7058_APPMGR_DISABLE_BIOZ
            if (AS7058_APPMGR_INTERNAL_APP_ID_BIOZ == internal_id) {
            /* BioZ app receives input via as7058_appmgr_set_bioz_input. */
        } else
#endif
#ifndef AS7058_APPMGR_DISABLE_STREAM
            if (AS7058_APPMGR_INTERNAL_APP_ID_STREAM == internal_id) {
            M_CHECK_SUCCESS(handle_bio_stream_set_input(&p_extract_result, p_fifo_data, fifo_data_size, status_events,
                                                        p_agc_statuses, agc_statuses_num, p_acc_samples,
                                                        acc_samples_num, ext_event_count, &execution_status));
        } else
#endif
        {
            const as7058_appmgr_app_definition_t *p_app = &g_app_table[internal_id];
            M_CHECK_SUCCESS(process_samples(&p_extract_result, p_agc_statuses, agc_statuses_num, p_acc_samples,
                                            acc_samples_num, p_app, &execution_status));
        }

        /* Store "ready to execute" information. */
        if (BIO_EXECUTION_STATUS_EXECUTABLE == execution_status) {
            g_executable_apps |= M_ID_TO_FLAG(internal_id);
        }
    }

    /* Provide "ready to execute" information to caller. */
    *p_ready_for_execution = (g_executable_apps ? TRUE : FALSE);

    return ERR_SUCCESS;
}

AS7058_APPMGR_FUNC_DEFN err_code_t as7058_appmgr_set_special_measurement_input(
    as7058_meas_mode_t mode, const as7058_special_measurement_result_t *p_input, uint8_t *p_ready_for_execution)
{
    M_CHECK_STATE(AS7058_APPMGR_STATE_PROCESSING);

    if (AS7058_MEAS_MODE_NORMAL == mode || mode >= AS7058_MEAS_MODE_NUM) {
        return ERR_ARGUMENT;
    }

    M_CHECK_NULL_POINTER(p_input);
    M_CHECK_NULL_POINTER(p_ready_for_execution);

#ifndef AS7058_APPMGR_DISABLE_BIOZ
    if (M_INTERNAL_APP_ID_IS_ENABLED(AS7058_APPMGR_INTERNAL_APP_ID_BIOZ) && AS7058_MEAS_MODE_SPECIAL_BIOZ == mode) {
        /* Provide data to app. */
        bio_execution_status_t result = BIO_EXECUTION_STATUS_NOT_EXECUTABLE;
        M_CHECK_SUCCESS(as7058_bioz_app_set_input(&p_input->bioz, &result));

        /* Store "ready to execute" information. */
        if (BIO_EXECUTION_STATUS_EXECUTABLE == result) {
            g_executable_apps |= AS7058_APPMGR_APP_FLAG_BIOZ;
        }
    }
#endif

    /* Provide "ready to execute" information to caller. */
    *p_ready_for_execution = (g_executable_apps ? TRUE : FALSE);

    return ERR_SUCCESS;
}

AS7058_APPMGR_FUNC_DEFN err_code_t as7058_appmgr_set_ext_event_occurred(void)
{
    M_CHECK_STATE(AS7058_APPMGR_STATE_PROCESSING);

    if (g_pending_ext_event_count >= UINT8_MAX) {
        return ERR_OVERFLOW;
    }

    g_pending_ext_event_count++;
    return ERR_SUCCESS;
}

AS7058_APPMGR_FUNC_DEFN err_code_t as7058_appmgr_execute(uint32_t *p_data_available)
{
    M_CHECK_STATE(AS7058_APPMGR_STATE_PROCESSING);
    M_CHECK_NULL_POINTER(p_data_available);

    *p_data_available = 0;

    for (as7058_appmgr_internal_app_id_t internal_id = 0; internal_id < AS7058_APPMGR_INTERNAL_APP_ID_NUM;
         internal_id++) {
        if (!M_INTERNAL_APP_ID_IS_ENABLED(internal_id) || !M_ID_SET_IN_BITFIELD(internal_id, g_executable_apps)) {
            /* Skip apps that are disabled or not ready for execution. */
            continue;
        }

        /* Clear flag. */
        g_executable_apps &= ~M_ID_TO_FLAG(internal_id);

        /* Execute app. */
        const as7058_appmgr_app_definition_t *p_app = &g_app_table[internal_id];
        bio_output_status_t result = BIO_OUTPUT_STATUS_DATA_UNAVAILABLE;
        M_CHECK_APP_DEFINITION(p_app->p_execute);
        M_CHECK_SUCCESS(p_app->p_execute(&result));

        /* Store execution result. */
        if (BIO_OUTPUT_STATUS_DATA_AVAILABLE == result) {
            as7058_appmgr_app_id_t public_id = g_app_id_mapping_internal_to_public[internal_id];
            *p_data_available |= M_ID_TO_FLAG(public_id);
        }
    }

    return ERR_SUCCESS;
}

AS7058_APPMGR_FUNC_DEFN err_code_t as7058_appmgr_get_output(as7058_appmgr_app_id_t app, void *p_dest, uint16_t *p_size)
{
    M_CHECK_STATE(AS7058_APPMGR_STATE_PROCESSING);
    M_CHECK_PUBLIC_APP_ID(app);
    M_CHECK_NULL_POINTER(p_dest);
    M_CHECK_NULL_POINTER(p_size);

    as7058_appmgr_internal_app_id_t internal_id;
    M_CHECK_SUCCESS(get_internal_app_id_for_public_app_id(app, &internal_id));

    if (!M_INTERNAL_APP_ID_IS_ENABLED(internal_id)) {
        /* App was disabled at run-time. */
        return ERR_ARGUMENT;
    }

    const as7058_appmgr_app_definition_t *p_app = &g_app_table[internal_id];
    M_CHECK_APP_DEFINITION(p_app->p_get_output);

    return p_app->p_get_output(p_dest, p_size);
}

AS7058_APPMGR_FUNC_DEFN err_code_t as7058_appmgr_stop_processing(void)
{
    M_CHECK_STATE_NOT(AS7058_APPMGR_STATE_UNINITIALIZED);

    /* Stop enabled apps. */
    for (as7058_appmgr_internal_app_id_t internal_id = 0; internal_id < AS7058_APPMGR_INTERNAL_APP_ID_NUM;
         internal_id++) {
        if (!M_INTERNAL_APP_ID_IS_ENABLED(internal_id)) {
            /* Skip disabled app. */
            continue;
        }

        const as7058_appmgr_app_definition_t *p_app = &g_app_table[internal_id];
        M_CHECK_APP_DEFINITION(p_app->p_stop);

        M_CHECK_SUCCESS(p_app->p_stop());
    }

    M_CHECK_SUCCESS(clear_measurement_config());

    g_state = AS7058_APPMGR_STATE_CONFIGURATION;

    return ERR_SUCCESS;
}

AS7058_APPMGR_FUNC_DEFN err_code_t as7058_appmgr_shutdown(void)
{
    err_code_t return_value = ERR_SUCCESS;

    for (as7058_appmgr_internal_app_id_t internal_id = 0; internal_id < AS7058_APPMGR_INTERNAL_APP_ID_NUM;
         internal_id++) {
        const as7058_appmgr_app_definition_t *p_app = &g_app_table[internal_id];

        if (!p_app->p_shutdown) {
            return_value = ERR_CONFIG;
        } else {
            err_code_t result = p_app->p_shutdown();
            if (result != ERR_SUCCESS) {
                return_value = result;
            }
        }
    }

    g_state = AS7058_APPMGR_STATE_UNINITIALIZED;

    return return_value;
}

AS7058_APPMGR_FUNC_DEFN const char *as7058_appmgr_get_version(void)
{
    return AS7058_APP_MANAGER_VERSION;
}
