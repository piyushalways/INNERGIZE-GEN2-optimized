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

#include "bio_srd.h"

#include "bio_srd_version.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

/*!
 * Causes the function where this macro is used to return with ::ERR_PERMISSION if the Bio App is in an unexpected
 * state.
 */
#define M_CHECK_STATE(expected)                                                                                        \
    do {                                                                                                               \
        if (g_state != (expected)) {                                                                                   \
            return ERR_PERMISSION;                                                                                     \
        }                                                                                                              \
    } while (0)

/*!
 * Causes the function where this macro is used to return with ::ERR_PERMISSION if the Bio App is in an unexpected
 * state.
 */
#define M_CHECK_STATE_NOT(not_expected)                                                                                \
    do {                                                                                                               \
        if ((not_expected) == g_state) {                                                                               \
            return ERR_PERMISSION;                                                                                     \
        }                                                                                                              \
    } while (0)

/*!
 * Causes the function where this macro is used to return ::ERR_ARGUMENT if the provided argument does not match the
 * expected signal number of the Bio App.
 */
#define M_CHECK_SIGNAL_NUM(signal_num)                                                                                 \
    do {                                                                                                               \
        if ((signal_num) != BIO_SRD_SIGNAL_NUM) {                                                                      \
            return ERR_ARGUMENT;                                                                                       \
        }                                                                                                              \
    } while (0)

/*! States of the Bio App. */
enum bio_srd_state {
    BIO_SRD_STATE_UNINITIALIZED = 0, /*!< Bio app is uninitialized. */
    BIO_SRD_STATE_CONFIGURATION,     /*!< Bio app is in configuration state. */
    BIO_SRD_STATE_PROCESSING,        /*!< Bio app is in processing state. */
};

/*! State of the signal status change detection. */
struct bio_srd_change_detection {
    enum bio_srd_output_flags_signal_status output_signal_status;    /*!< Contains the signal status that is currently
                                                                          output. */
    enum bio_srd_output_flags_signal_status candidate_signal_status; /*!< Contains the signal status that might become
                                                                          the signal status that is used for output. */
    uint8_t candidate_region_samples_num;                            /*!< Contains the number of received consecutive
                                                                          samples that fall into the region of the
                                                                          candidate signal status. */
    uint8_t initial_output_generated;                                /*!< ::TRUE when the initial output of a processing
                                                                          session has been generated, ::FALSE
                                                                          otherwise. */
};

/*! State of the Bio App output. */
struct bio_srd_output {
    uint8_t pending;       /*!< ::TRUE when there is valid data for output, ::FALSE otherwise. */
    bio_srd_output_t data; /*!< Contains data for output. */
};

/*! Current state of the Bio App. */
static volatile enum bio_srd_state g_state = BIO_SRD_STATE_UNINITIALIZED;

/*! Current Bio App configuration. */
static volatile bio_srd_configuration_t g_config;

/*! Sample rate in Hertz of the monitored signal during the current processing session. */
static volatile uint32_t g_sample_rate_hz;

/*! State of the signal status change detection. */
static volatile struct bio_srd_change_detection g_change_detection;

/*! Sample counter used to generate periodic outputs. */
static volatile uint32_t g_sample_cnt_periodic;

/*! State of the Bio App output. */
static volatile struct bio_srd_output g_output;

/******************************************************************************
 *                              GLOBAL FUNCTIONS                              *
 ******************************************************************************/

/*! Gets the signal status region the provided sample falls into. */
static enum bio_srd_output_flags_signal_status signal_status_for_sample(int32_t sample)
{
    if (sample < g_config.lower_threshold) {
        return BIO_SRD_OUTPUT_FLAGS_SIGNAL_STATUS_LOWER;
    } else if (sample < g_config.upper_threshold) {
        return BIO_SRD_OUTPUT_FLAGS_SIGNAL_STATUS_CENTER;
    } else {
        return BIO_SRD_OUTPUT_FLAGS_SIGNAL_STATUS_UPPER;
    }
}

/*!
 * Gets the signal status that should currently be used for the output. The p_did_change parameter indicates whether the
 * signal status changed since the last call of the function.
 */
static enum bio_srd_output_flags_signal_status get_output_signal_status(int32_t sample, uint8_t *p_did_change)
{
    enum bio_srd_output_flags_signal_status status = signal_status_for_sample(sample);

    if (!g_change_detection.initial_output_generated) {
        /* After start of a processing session, generate an initial output. */
        g_change_detection.output_signal_status = status;
        *p_did_change = TRUE;

        g_change_detection.initial_output_generated = TRUE;
        g_change_detection.candidate_region_samples_num = 0;
    } else if (status != g_change_detection.output_signal_status) {
        if (status != g_change_detection.candidate_signal_status) {
            /* Reset change detection since the candidate region changed. */
            g_change_detection.candidate_signal_status = status;
            g_change_detection.candidate_region_samples_num = 0;
        }

        if (g_change_detection.candidate_region_samples_num >= g_config.change_detection_samples_num) {
            /* Enough samples that fall in the candidate region are received, update the signal status. */
            g_change_detection.output_signal_status = g_change_detection.candidate_signal_status;
            *p_did_change = TRUE;

            g_change_detection.candidate_region_samples_num = 0;
        } else {
            /* More samples that fall in the candidate region are required before the signal status is updated. */
            g_change_detection.candidate_region_samples_num++;
            *p_did_change = FALSE;
        }
    } else {
        /* No change in progress since the sample falls into current signal status region. Reset counter so that it
         * starts counting from zero when a sample that falls into a different signal status region arrives. */
        g_change_detection.candidate_region_samples_num = 0;
        *p_did_change = FALSE;
    }

    return g_change_detection.output_signal_status;
}

/*! Checks whether a periodic output is currently required. */
static uint8_t check_periodic_output_required(uint8_t reset)
{
    if (reset) {
        g_sample_cnt_periodic = 0;
    } else {
        g_sample_cnt_periodic++;
    }

    if (g_sample_cnt_periodic >= g_sample_rate_hz) {
        g_sample_cnt_periodic = 0;
        return TRUE;
    } else {
        return FALSE;
    }
}

err_code_t bio_srd_initialize(void)
{
    g_config.lower_threshold = INT32_MIN;
    g_config.upper_threshold = INT32_MAX;
    g_config.change_detection_samples_num = 0;
    g_sample_rate_hz = 0;
    g_change_detection.output_signal_status = BIO_SRD_OUTPUT_FLAGS_SIGNAL_STATUS_LOWER;
    g_change_detection.candidate_signal_status = BIO_SRD_OUTPUT_FLAGS_SIGNAL_STATUS_LOWER;
    g_change_detection.candidate_region_samples_num = 0;
    g_change_detection.initial_output_generated = FALSE;
    g_sample_cnt_periodic = 0;
    g_output.pending = FALSE;
    g_output.data.flags = 0;
    g_state = BIO_SRD_STATE_CONFIGURATION;

    return ERR_SUCCESS;
}

err_code_t bio_srd_configure(const void *p_config, uint8_t size)
{
    M_CHECK_STATE(BIO_SRD_STATE_CONFIGURATION);
    M_CHECK_NULL_POINTER(p_config);
    M_CHECK_SIZE(size, sizeof(bio_srd_configuration_t));

    const bio_srd_configuration_t *p_srd_config = (const bio_srd_configuration_t *)p_config;

    if (p_srd_config->upper_threshold < p_srd_config->lower_threshold) {
        return ERR_ARGUMENT;
    }

    g_config.lower_threshold = p_srd_config->lower_threshold;
    g_config.upper_threshold = p_srd_config->upper_threshold;
    g_config.change_detection_samples_num = p_srd_config->change_detection_samples_num;

    return ERR_SUCCESS;
}

err_code_t bio_srd_get_configuration(void *p_dest, uint8_t *p_size)
{
    M_CHECK_STATE(BIO_SRD_STATE_CONFIGURATION);

    M_CHECK_NULL_POINTER(p_dest);
    M_CHECK_NULL_POINTER(p_size);

    if (*p_size < sizeof(bio_srd_configuration_t)) {
        return ERR_SIZE;
    }

    bio_srd_configuration_t *p_srd_config = (bio_srd_configuration_t *)p_dest;
    p_srd_config->lower_threshold = g_config.lower_threshold;
    p_srd_config->upper_threshold = g_config.upper_threshold;
    p_srd_config->change_detection_samples_num = g_config.change_detection_samples_num;
    p_srd_config->reserved[0] = 0;
    p_srd_config->reserved[1] = 0;
    p_srd_config->reserved[2] = 0;

    *p_size = sizeof(bio_srd_configuration_t);

    return ERR_SUCCESS;
}

err_code_t bio_srd_start(const uint32_t *p_signal_sample_periods_us, uint8_t signal_num, uint32_t acc_sample_period_us)
{
    M_UNUSED_PARAM(acc_sample_period_us);

    M_CHECK_STATE(BIO_SRD_STATE_CONFIGURATION);
    M_CHECK_NULL_POINTER(p_signal_sample_periods_us);
    M_CHECK_SIGNAL_NUM(signal_num);

    if (0 == p_signal_sample_periods_us[BIO_SRD_SIGNAL_MAIN]) {
        return ERR_ARGUMENT;
    }

    /* Calculate number of samples per second (i.e. convert sample period to Hertz) for periodic updates. */
    g_sample_rate_hz = 1000 * 1000 / p_signal_sample_periods_us[BIO_SRD_SIGNAL_MAIN];

    /* Reset current signal status, change detection, counter for periodic output, and pending output data. */
    g_change_detection.output_signal_status = BIO_SRD_OUTPUT_FLAGS_SIGNAL_STATUS_LOWER;
    g_change_detection.candidate_signal_status = BIO_SRD_OUTPUT_FLAGS_SIGNAL_STATUS_LOWER;
    g_change_detection.candidate_region_samples_num = 0;
    g_change_detection.initial_output_generated = FALSE;
    g_sample_cnt_periodic = 0;
    g_output.pending = FALSE;
    g_output.data.flags = 0;

    g_state = BIO_SRD_STATE_PROCESSING;

    return ERR_SUCCESS;
}

err_code_t bio_srd_set_input(bio_signal_samples_type_t signal_samples_type,
                             const bio_signal_samples_t *p_signal_samples, const agc_status_t *const *pp_agc_statuses,
                             uint8_t signal_num, const vs_acc_data_t *p_acc_samples, uint8_t acc_sample_num,
                             bio_execution_status_t *p_result)
{
    M_UNUSED_PARAM(pp_agc_statuses);
    M_UNUSED_PARAM(p_acc_samples);
    M_UNUSED_PARAM(acc_sample_num);

    M_CHECK_STATE(BIO_SRD_STATE_PROCESSING);

    if (signal_samples_type != BIO_SIGNAL_SAMPLES_TYPE_I32) {
        return ERR_ARGUMENT;
    }

    M_CHECK_SIGNAL_NUM(signal_num);

    M_CHECK_NULL_POINTER(p_signal_samples);
    M_CHECK_NULL_POINTER(p_result);
    M_CHECK_NULL_POINTER(p_signal_samples[BIO_SRD_SIGNAL_MAIN].samples.p_i32);

    bio_signal_samples_t signal_samples = p_signal_samples[BIO_SRD_SIGNAL_MAIN];

    if (0 < signal_samples.count) {
        M_CHECK_NULL_POINTER(signal_samples.samples.p_i32);
    }

    for (unsigned int sample_idx = 0; sample_idx < signal_samples.count; sample_idx++) {
        int32_t sample = signal_samples.samples.p_i32[sample_idx];

        uint8_t signal_status_changed;
        enum bio_srd_output_flags_signal_status signal_status =
            get_output_signal_status(sample, &signal_status_changed);
        uint8_t periodic_output_required = check_periodic_output_required(signal_status_changed);

        if (signal_status_changed) {
            g_output.data.flags = BIO_SRD_OUTPUT_FLAGS_REASON_CHANGE | signal_status;
            g_output.pending = TRUE;
        } else if (periodic_output_required) {
            /* If there is a pending output, do not overwrite it if it has reason BIO_SRD_OUTPUT_FLAGS_REASON_CHANGE.
             * Change outputs have priority over periodic outputs. */
            if (!g_output.pending ||
                (g_output.data.flags & BIO_SRD_OUTPUT_FLAGS_REASON_MASK) != BIO_SRD_OUTPUT_FLAGS_REASON_CHANGE) {

                g_output.data.flags = BIO_SRD_OUTPUT_FLAGS_REASON_PERIODIC | signal_status;
                g_output.pending = TRUE;
            }
        }
    }

    if (g_output.pending) {
        *p_result = BIO_EXECUTION_STATUS_EXECUTABLE;
    } else {
        *p_result = BIO_EXECUTION_STATUS_NOT_EXECUTABLE;
    }

    return ERR_SUCCESS;
}

err_code_t bio_srd_execute(bio_output_status_t *p_result)
{
    M_CHECK_STATE(BIO_SRD_STATE_PROCESSING);
    M_CHECK_NULL_POINTER(p_result);

    if (g_output.pending) {
        *p_result = BIO_OUTPUT_STATUS_DATA_AVAILABLE;
    } else {
        *p_result = BIO_OUTPUT_STATUS_DATA_UNAVAILABLE;
    }

    return ERR_SUCCESS;
}

err_code_t bio_srd_get_output(void *p_dest, uint16_t *p_size)
{
    M_CHECK_STATE(BIO_SRD_STATE_PROCESSING);
    M_CHECK_NULL_POINTER(p_dest);
    M_CHECK_NULL_POINTER(p_size);

    if (*p_size < sizeof(bio_srd_output_t)) {
        return ERR_SIZE;
    }

    if (!g_output.pending) {
        return ERR_NO_DATA;
    }

    bio_srd_output_t *p_output = (bio_srd_output_t *)p_dest;
    p_output->flags = g_output.data.flags;
    *p_size = sizeof(bio_srd_output_t);

    g_output.pending = FALSE;

    return ERR_SUCCESS;
}

err_code_t bio_srd_stop(void)
{
    M_CHECK_STATE_NOT(BIO_SRD_STATE_UNINITIALIZED);

    g_state = BIO_SRD_STATE_CONFIGURATION;

    return ERR_SUCCESS;
}

err_code_t bio_srd_shutdown(void)
{
    g_state = BIO_SRD_STATE_UNINITIALIZED;

    return ERR_SUCCESS;
}

const char *bio_srd_get_version(void)
{
    return BIO_SRD_VERSION;
}
