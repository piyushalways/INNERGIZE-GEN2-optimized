/******************************************************************************
 * Copyright by ams AG                                                        *
 * All rights are reserved.                                                   *
 *                                                                            *
 * IMPORTANT - PLEASE READ CAREFULLY BEFORE COPYING, INSTALLING OR USING      *
 * THE SOFTWARE.                                                              *
 *                                                                            *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS        *
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT          *
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS          *
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT   *
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,      *
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT           *
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,      *
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY      *
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT        *
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE      *
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.       *
 ******************************************************************************/

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include "std_inc.h"

#include "agc.h"
#include "agc_hal.h"
#include "agc_typedefs.h"
#include "agc_version.h"
#include "error_codes.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

/*! Starting PD Offset stride for fast lock. */
#define FASTLOCK_START_STEPS 32
/*! Base correction when the signal exceeds the range limits: 20 % */
#define PD_OFFSET_BASE_CORRECTION_X100 20
/*! Lag of the moving window of the step detection filters. */
#define STEP_DETECTION_LAG 5
/*! Minimum relative signal step to be recognized as PD Offset change caused step,
    based on the moving standard deviation of the signal. */
#define RELATIVE_STEP_DETECT_THRESHOLD 6
/*! Minimum relative signal step to be recognized as PD Offset change caused step,
    based on the expected step size. It is in (%). The value is scaled to 100 for fixed point operation. */
#define RELATIVE_SIGNAL_THRESHOLD_X100 50
/*! Maximum relative standard deviation of the estimated signal step size to be
    considered stable. The value is scaled to 100 for fixed point operation.  */
#define RSD_THRESHOLD_X100 15
/*! Settling time in miliseconds after PD Offset or LED current was changed. */
#define SETTLING_TIME 200
/*! Signal amplitude detection window size in milliseconds. */
#define SIGNAL_AMPLITUDE_DETECTION_TIME 4000
/*! Divisor to the motion amplitude limit which determines the limit of the relative standard deviation of the signal
 * amplitude to recognize it as in steady state. */
#define SIGNAL_AMPLITUDE_STEADINESS_RELATION 6
/*! Moving mean filter window size in millisecond for smoothing the signal. */
#define SIGNAL_MOVE_MEAN_WINDOW_SIZE 200
#define MAX_LIMIT_BASELINE_TILT 1000
#define MIN_LIMIT_BASELINE_TILT -1000
#define HUNDRED_PERCENT 100
#define PD_OFFSET_INIT 128
#define EXTRACTED_MESSAGE_BUF_SIZE 100

/*! Normalization factors: Normalization is used to compensate the effect of changing float variables to fixed. It is
 * always used at the beginning of the calculation to maintain the accuracy.
 */
#define NORMALIZATION_FACTOR_10 10
#define NORMALIZATION_FACTOR_100 100
#define NORMALIZATION_FACTOR_1000 1000

/*! Magic value representing an invalid agc_internal_t::estimated_amplitude_x1000 value. Valid values are expected to
 *  be always greater than INT32_MIN. */
#define UNDEFINED_INT32 INT32_MIN

/*! Channel status. */
#define CHANNEL_DISABLED 0
/*! Maximum size for the moving filters. */
#define MAX_FILTER_SIZE 5
/*! Filter size to calculate moving mean of the PD offset signal change. */
#define SIGNAL_STRIDE_MOV_MEAN_SAMPLE_SIZE 3
/*! Filter size to find the moving median of the mean PD offset change. */
#define SIGNAL_STRIDE_MOV_MEDIAN_SAMPLE_SIZE 5
/*! Filter size to calculate moving standard deviation of the mean PD offset signal change. */
#define SIGNAL_STRIDE_MOV_SD_SAMPLE_SIZE 5
/*! Filter size to calculate the moving standard deviation of the estimated amplitude. */
#define AMPLITUDE_MOV_SD_SAMPLE_SIZE 3
/*! Minimum PD offset current. */
#define MIN_PD_OFFSET 0
/*! Maximum PD offset current. */
#define MAX_PD_OFFSET 255
/*! First input to the filter for calculating the standard deviation of the signal value change per PD offset step. */
#define SIGNAL_STRIDE_MOV_SD_INIT_VALUE_FIRST (0x01 << 19)
/*! Second input to the filter for calculating the standard deviation of the signal value change per PD offset step. */
#define SIGNAL_STRIDE_MOV_SD_INIT_VALUE_SECOND 0
/*! First input to the filter for calculating the standard deviation of the estimated amplitude. */
#define AMPLITUDE_MOV_SD_INIT_VALUE_FIRST NORMALIZATION_FACTOR_1000
/*! Other input to the filter for calculating the standard deviation of the estimated amplitude. */
#define AMPLITUDE_MOV_SD_INIT_VALUE_OTHER 0

/*! State of the AGC module. */
enum agc_state {
    STATE_UNINITIALIZED = 0, /*!< Uninitialized state. */
    STATE_CONFIGURATION,     /*!< Configuration state. */
    STATE_PROCESSING,        /*!< Processing state. */
};

/*! Type for ::agc_state. */
typedef uint8_t agc_state_t;

/*! State of the fast lock mode of PD offset control. */
enum agc_fast_lock_state {
    FASTLOCK_START = 0,   /*!< Fast lock mode started. */
    FASTLOCK_OVER_RANGE,  /*!< Signal exceeded the upper range limit. */
    FASTLOCK_UNDER_RANGE, /*!< Signal exceeded the lower range limit. */
    FASTLOCK_IN_RANGE,    /*!< Signal is within the target range. */
    FASTLOCK_FINISHED,    /*!< Fast lock mode finished. */
};

/*! Type for ::agc_fast_lock_state. */
typedef uint8_t agc_fast_lock_state_t;

/*! State of a filter with buffer. */
typedef struct {
    uint8_t size;       /*!< Number of sample size for the filter. */
    uint8_t cnt;        /*!< Number of samples available. This value should not be more than maximum size of the
                           filter. */
    uint8_t curr_index; /*!< Current index to point the last sample input. */
    int32_t buf[MAX_FILTER_SIZE]; /*!< Moving filters buffer to last received inputs */
} filter_body_t;

/*! State of a low-pass filter. */
typedef struct {
    uint8_t size;       /*!< Number of sample size for the filter. */
    uint8_t curr_index; /*!< Current index pointing to the last input sample. */
    int32_t data;       /*!< Buffer to store the last output. */
} filter_body_lp_t;

/*! State of a gradient calculation. */
typedef struct {
    uint8_t initiation_flag;  /*< Marks the beginning of gradient calculation. */
    uint32_t sampling_period; /*< Sampling period in millisecond. */
    int32_t last_sample;      /*< Last input value. */
} gradient_t;

/*! State of the normalized signal amplitude estimation algorithm. */
typedef struct {
    uint16_t reset_counter; /*!< Reset timer. */
    uint16_t reset_time;    /*!< Reset time interval to estimate normalized signal amplitude and standard deviation.*/
    int32_t signal_min;     /*!< Minimum signal amplitude. */
    int32_t signal_max;     /*!< Maximum signal amplitude. */
} amplitude_estimation_t;

/*! State of an AGC instance. */
typedef struct {
    /* Fields related to the PPG signal target range. */
    int32_t range_center;        /*!< Center point of the PPG signal target range in ADC counts. */
    uint32_t signal_range_limit; /*!< Size of the PPG signal target range in ADC counts. */

    /* Fields related to general processing of the PPG signal. */
    uint8_t settling_counter_start; /*!< Starting time for the settling counter. */
    uint8_t settling_counter;       /*!< Current time for the setting counter. */
    int32_t prev_sample;            /*!< Last input signal, used to estimate the change in the current input signal. */
    int32_t baseline_drift;         /*!< The low-pass filtered PPG signal. */
    int32_t baseline_tilt;          /*!< Baseline drift deviation from the center of the target PPG range. */
    int32_t baseline_grad;          /*!< Gradient of the baseline drift signal. */
    filter_body_lp_t baseline_filter; /*!< Low pass filter for input data stream. */
    gradient_t baseline_gradient;     /*!< For baseline gradient calculation. */

    /* Fields related to PPG signal step detection */
    uint8_t step_found; /*!< Flag to indicate the jump in the signal caused by an PD offset change. */
    filter_body_t
        step_detect_mov_mean_filter; /*!< Moving averaging filter to detect the jump position in the PPG signal. */
    filter_body_t step_detect_mov_sd_filter; /*!< Moving standard deviation filter to detect the jump position in the
                                                   PPG signal. */
    int32_t mov_mean;                        /*!< Moving mean of the signal, used in the PD Offset step detection. */
    int32_t mov_mean_prev;                   /*!< Last calculated moving mean of the signal. */
    uint32_t mov_sd;      /*!< Moving standard deviation of the signal, used in the PD Offset step detection. */
    uint32_t mov_sd_prev; /*!< Last calculated moving standard deviation of the signal. */

    /* Fields related to estimation of signal value change per PD offset step */
    uint32_t mean_pd_offset_signal_change;     /*!< Mean change in the signal value per PD offset step. */
    uint32_t rsd_pd_offset_signal_change_x100; /*!< Relative standard deviation of PD offset. */
    filter_body_t
        signal_stride_mov_mean_filter; /*!< Filter to calculate to calculate moving mean of the PD offset change. */
    filter_body_t
        signal_stride_mov_median_filter; /*!< Filter to calculate to moving of median of the mean PD offset change. */
    filter_body_t signal_stride_mov_sd_filter; /*!< Filter to calculate to calculate the moving standard deviation of
                                                     the mean PD offset change. */

    /* Fields related to PD offset control. */
    uint8_t pd_offset;         /*!< Local copy of the PD offset register value. */
    uint8_t pd_offset_changed; /*!< ::TRUE when the PD offset current was changed. */
    int16_t pd_offset_steps;   /*!< Current change of the PD offset register value. (1 step = increment of the register
                                   value by one) */
    int16_t last_pd_offset_steps;         /*!< Last non-zero value of pd_offset_steps. */
    agc_fast_lock_state_t fastlock_state; /*!< Stores state of the fast lock mode. */
    uint16_t fastlock_steps;              /*!< Steps size during fastlock mode. */

    /* Fields related to amplitude estimation. */
    int32_t estimated_amplitude_x1000;           /*!< Estimated of the normalized signal amplitude. */
    int16_t rsd_amplitude_x1000;                 /*!< Relative Standard deviation of the last found amplitudes. */
    amplitude_estimation_t amplitude_estimation; /*!< Used for estimation of the normalized signal amplitude and to
                                                      calculate the standard deviation of the last found amplitudes. */
    filter_body_t
        amplitude_mov_sd_filter; /*!< Filter to calculate moving standard deviation of estimation amplitude. */

    /* Fields related to LED current control. */
    uint8_t led_current;         /*!< Local copy of the LED current register value. */
    uint8_t led_current_changed; /*!< ::TRUE when the LED current was changed. */
    uint8_t led_current_stride;  /*!< The increment used to change the LED current register value. */
    int16_t led_current_steps;   /*!< Current change of the LED current register value. (1 step = increment of the
                                      register value by one). */
} agc_internal_t;

/******************************************************************************
 *                                  GLOBALS                                   *
 ******************************************************************************/

static agc_configuration_t g_agc_config[AGC_MAX_CHANNEL_CNT];
static agc_status_t g_agc_status[AGC_MAX_CHANNEL_CNT];
static agc_internal_t g_agc[AGC_MAX_CHANNEL_CNT];
static uint8_t g_agc_channel_cnt;
static volatile agc_state_t g_agc_state;

/******************************************************************************
 *                               LOCAL FUNCTIONS                              *
 ******************************************************************************/

/*!
 * \brief Inserts a sample in the circular buffer of a filter.
 *
 * \note p_filter must not be NULL. p_filter->size must be larger than zero and not be larger than ::MAX_FILTER_SIZE.
 */
static void update_circular_buff(int32_t sample, filter_body_t *p_filter)
{
    p_filter->buf[p_filter->curr_index] = sample;

    p_filter->curr_index++;
    if (p_filter->curr_index >= p_filter->size) {
        p_filter->curr_index = 0;
    }

    if (p_filter->cnt < p_filter->size) {
        p_filter->cnt++;
    }
}

/*!
 * \brief Provides a new sample to a moving mean filter and calculates the new filter output.
 *
 * \note p_filter must not be NULL. p_filter->size must not be zero and must not be greater than MAX_FILTER_SIZE. The
 *       sum of all samples within the internal sample buffer (buffer length: p_filter->size) must be representable
 *       using int32_t.
 */
static int32_t calc_moving_mean(int32_t sample, filter_body_t *p_filter)
{
    int32_t avg_val = 0;
    uint32_t i;

    update_circular_buff(sample, p_filter);
    for (i = 0; i < p_filter->cnt; i++) {
        avg_val += p_filter->buf[i];
    }
    avg_val = avg_val / p_filter->cnt;

    return avg_val;
}

/*!
 * \brief Provides a new sample to a low-pass filter and calculates the new filter output.
 *
 * This filter smoothens the data stream with minimum buffer size by using Exponentially Weighted Moving Mean method
 *
 * \note p_filter must not be NULL. p_filter->size must not be zero. Inputs and filter size must be chosen so that no
 *       overflow occurs during calculation.
 */
static int32_t calc_exp_mov_mean_filter(int32_t sample, filter_body_lp_t *p_filter)
{
    int32_t avg_val = 0;

    if (p_filter->curr_index < p_filter->size) {
        p_filter->curr_index++;
    }
    /* y(n)=αx(n)+(1−α)y(n−1), where α<1, α=(1/p_filter->curr_index). */
    avg_val = (sample + p_filter->data * (p_filter->curr_index - 1)) / p_filter->curr_index;
    p_filter->data = avg_val;
    return avg_val;
}

/*!
 * \brief Provides a new sample to a moving standard deviation filter and calculates the new filter output.
 *
 * \note p_filter must not be NULL. Inputs and filter size must be chosen so that no overflow occurs during calculation.
 *       This filter calls ::calc_moving_mean internally, i.e. see the notes of this function regarding limitations. All
 *       additional calculations are performed with uint64_t.
 */
static uint32_t calc_mov_std_deviation(int32_t sample, filter_body_t *p_filter)
{
    int32_t moving_avg = calc_moving_mean(sample, p_filter);
    uint64_t std_dev = 0;

    for (uint8_t index = 0; index < p_filter->cnt; index++) {
        uint64_t temp = abs(p_filter->buf[index] - moving_avg);
        std_dev += temp * temp;
    }

    std_dev = sqrt(DIV64_U64(std_dev, p_filter->cnt));
    return (uint32_t)std_dev;
}

/*!
 * \brief Calculates the gradient of a signal.
 *
 * \note p_input must not be NULL. p_input->sampling_period period must not be zero. Inputs must be chosen so that no
 *       no overflow occurs after normalization.
 */
static int32_t calc_gradient(int32_t curr_sample, gradient_t *p_input)
{
    int32_t gradient_val = 0;
    if (p_input->initiation_flag) {
        /* Normalization factor of 10 is applied in order to maintain the accuracy. */
        gradient_val =
            ((curr_sample - p_input->last_sample) * NORMALIZATION_FACTOR_10) / (int32_t)p_input->sampling_period;
    } else {
        p_input->initiation_flag = TRUE;
    }
    p_input->last_sample = curr_sample;
    return gradient_val;
}

/*!
 * \brief Provides a new sample to a moving median filter and calculates the new filter output.
 *
 * This filter is used to remove spikes from a signal.
 *
 * \note p_filter must not be NULL. p_filter->size must not be zero and must not be greater than MAX_FILTER_SIZE. This
 * implementation is only suitable for small filter sizes. In case of an even number of elements in the internal buffer,
 * two samples are summed. The inputs must be chosen so that this sum is representable using int32_t.
 */
static int32_t mov_median_filter(int32_t sample, filter_body_t *p_filter)
{
    int32_t tray, i, j;
    int32_t tray_buf[MAX_FILTER_SIZE];

    update_circular_buff(sample, p_filter);
    memcpy(tray_buf, p_filter->buf, sizeof(tray_buf));

    for (i = 0; i < (p_filter->cnt - 1); i++) {
        for (j = i; j < p_filter->cnt; j++) {
            if (tray_buf[i] > tray_buf[j]) {
                tray = tray_buf[i];
                tray_buf[i] = tray_buf[j];
                tray_buf[j] = tray;
            }
        }
    }
    if ((p_filter->cnt % 2) == 0) {
        /* Even number of elements */
        return (tray_buf[(p_filter->cnt - 2) / 2] + tray_buf[p_filter->cnt / 2]) / 2;
    } else {
        /* Odd number of elements */
        return tray_buf[(p_filter->cnt - 1) / 2];
    }
}

/*!
 * \brief Resets the calculation state of a filter structure. The filter size is not reset.
 *
 * \note p_filter must not be NULL.
 */
static void filter_reset(filter_body_t *p_filter)
{
    p_filter->cnt = 0;
    p_filter->curr_index = 0;
}

/*!
 * \brief Resets the calculation state of a low-pass filter structure. The filter size is not reset.
 *
 * \note p_filter must not be NULL.
 */
static void lp_filter_reset(filter_body_lp_t *p_filter)
{
    p_filter->data = 0;
    p_filter->curr_index = 0;
}

/*!
 * \brief Resets the calculation state of a amplitude estimation structure. The reset time is not reset.
 *
 * \note p_amplitude_estimation must not be NULL.
 */
static void reset_amplitude_estimation(amplitude_estimation_t *p_amplitude_estimation)
{
    p_amplitude_estimation->signal_max = INT32_MIN; /* Minimum value */
    p_amplitude_estimation->signal_min = INT32_MAX; /* Maximum value */
    p_amplitude_estimation->reset_counter = p_amplitude_estimation->reset_time;
}

/*!
 * \brief Sets start values for amplitude control filters.
 *
 * \note p_amplitude_mov_sd_filter must not be NULL.
 */
static void reset_amplitude_filter_values(filter_body_t *p_amplitude_mov_sd_filter)
{
    /* Call calc_mov_std_deviation several times to reset all entries in the buffer. */
    M_STATIC_ASSERT(AMPLITUDE_MOV_SD_SAMPLE_SIZE == 3, "Function needs to reset all buffer entries");
    calc_mov_std_deviation(AMPLITUDE_MOV_SD_INIT_VALUE_FIRST, p_amplitude_mov_sd_filter);
    calc_mov_std_deviation(AMPLITUDE_MOV_SD_INIT_VALUE_OTHER, p_amplitude_mov_sd_filter);
    calc_mov_std_deviation(AMPLITUDE_MOV_SD_INIT_VALUE_OTHER, p_amplitude_mov_sd_filter);
}

/*!
 * \brief Calculates drift, tilt and gradient of the signal's baseline.
 *
 * \note As the phase shift is too large for a real base line calculation, we use a simple moving mean filter with a
 *       higher cut-off frequency.
 *
 * \param[in]    sample Current PPG signal sample.
 * \param[inout] p_agc  Pointer to the internal structure of the AGC instance to use.
 */
static void calc_signal_params(int32_t sample, agc_internal_t *p_agc)
{
    /* Getting only the low frequency drift of the PPG signal would be ideal, but the accompanied high phase shift would
     * slow down the response time too much. So, we only smooth the signal a bit: Moving mean filter with a filter
     * window size of 0.2 s (= SIGNAL_MOVE_MEAN_WINDOW_SIZE, see configuration of baseline_filter in
     * agc_start_processing). */
    p_agc->baseline_drift = calc_exp_mov_mean_filter(sample, &p_agc->baseline_filter);

    /* The low pass filtered PPG signal (baseline drift) is normalized to the configured target range and its center
     * point, resulting in the baseline tilt. The signal is considered in-range when MIN_LIMIT_BASELINE_TILT <
     * baseline tilt < MAX_LIMIT_BASELINE_TILT. In the reference Python implementation the baseline tilt range is [-1.0,
     * 1.0]. This implementation scales the range with a constant factor for fixed point operation. */
    p_agc->baseline_tilt = (2 * MAX_LIMIT_BASELINE_TILT * (p_agc->baseline_drift - p_agc->range_center)) /
                           (int32_t)p_agc->signal_range_limit;

    /* Potential optimization: the gradient could also be calculated using the state of calc_exp_mov_mean_filter since
     * this filter already remembers its last output value. */
    p_agc->baseline_grad = calc_gradient(p_agc->baseline_drift, &p_agc->baseline_gradient);
}

/*!
 * \brief Calculates the moving mean and moving standard deviation of the PPG signal, which is used in the PD offset
 *        step detection.
 *
 * \param[in]    sample Current PPG signal sample.
 * \param[inout] p_agc  Pointer to the internal structure of the AGC instance to use.
 */
static void calc_step_detection_params(int32_t sample, agc_internal_t *p_agc)
{
    p_agc->mov_mean_prev = p_agc->mov_mean;
    p_agc->mov_sd_prev = p_agc->mov_sd;
    p_agc->mov_mean = calc_moving_mean(sample, &p_agc->step_detect_mov_mean_filter);
    p_agc->mov_sd = calc_mov_std_deviation(sample, &p_agc->step_detect_mov_sd_filter);
}

/*!
 * \brief Calculates the approximate signal value change per PD offset step and the relative standard deviation of the
 *        last signal value changes.
 *
 * \note p_agc->last_pd_offset_steps must not be zero.
 *
 * \param[in]    signal_change Difference of the current and the previous PPG signal sample.
 * \param[inout] p_agc         Pointer to the internal structure of the AGC instance to use.
 */
static void calc_pd_offset_signal_step_size(uint32_t signal_change, agc_internal_t *p_agc)
{
    uint32_t rel_signal_change = signal_change / (uint32_t)abs(p_agc->last_pd_offset_steps);

    uint32_t median_signal_change =
        (uint32_t)mov_median_filter(rel_signal_change, &p_agc->signal_stride_mov_median_filter);
    p_agc->mean_pd_offset_signal_change =
        (uint32_t)calc_moving_mean(median_signal_change, &p_agc->signal_stride_mov_mean_filter);

    if (p_agc->mean_pd_offset_signal_change > 0) {
        uint32_t sd_signal_change =
            calc_mov_std_deviation(p_agc->mean_pd_offset_signal_change, &p_agc->signal_stride_mov_sd_filter);
        p_agc->rsd_pd_offset_signal_change_x100 =
            sd_signal_change * NORMALIZATION_FACTOR_100 / p_agc->mean_pd_offset_signal_change;
    } else {
        p_agc->rsd_pd_offset_signal_change_x100 = NORMALIZATION_FACTOR_100;
    }
}

/*!
 * \brief Called when a jump in the signal has been found. Calculates the approximate signal value change per PD offset
 *        step and prepares the AGC instance for the next step detection.
 *
 * \param[in]    sample Current PPG signal sample.
 * \param[inout] p_agc  Pointer to the internal structure of the AGC instance to use.
 */
static void pd_offset_step_found(int32_t sample, agc_internal_t *p_agc)
{
    uint32_t signal_change = abs(sample - p_agc->prev_sample);
    if (p_agc->last_pd_offset_steps != 0) {
        calc_pd_offset_signal_step_size(signal_change, p_agc);
    }

    p_agc->settling_counter = M_MIN(STEP_DETECTION_LAG, p_agc->settling_counter);
    p_agc->step_found = TRUE;
    lp_filter_reset(&p_agc->baseline_filter);
    filter_reset(&p_agc->step_detect_mov_mean_filter);
    filter_reset(&p_agc->step_detect_mov_sd_filter);
}

/*!
 * \brief Finds a jump in the signal caused by a PD offset change. If a jump is found, the approximate signal value
 *        change per PD offset step is calculated.
 *
 * \param[in]    sample Current PPG signal sample.
 * \param[inout] p_agc  Pointer to the internal structure of the AGC instance to use.
 */
static void detect_pd_offset_steps(int32_t sample, agc_internal_t *p_agc)
{
    uint32_t signal_change, expected_signal_change;
    if (p_agc->step_found) {
        return;
    }

    signal_change = (uint32_t)abs(sample - p_agc->mov_mean_prev);
    if (p_agc->rsd_pd_offset_signal_change_x100 <= RSD_THRESHOLD_X100) {
        expected_signal_change = p_agc->mean_pd_offset_signal_change * (uint32_t)abs(p_agc->last_pd_offset_steps);
        if (signal_change * NORMALIZATION_FACTOR_100 > expected_signal_change * RELATIVE_SIGNAL_THRESHOLD_X100) {
            pd_offset_step_found(sample, p_agc);
        }
    } else {
        if (signal_change > RELATIVE_STEP_DETECT_THRESHOLD * p_agc->mov_sd_prev) {
            pd_offset_step_found(sample, p_agc);
        }
    }
}

/*!
 * \brief Sets PD offset steps.
 *
 * \param[in]    channel_id Index of the AGC instance to use.
 * \param[inout] p_agc      Pointer to the internal structure of the AGC instance to use.
 *
 * \retval ::ERR_SUCCESS Function returns without error.
 */
static err_code_t set_pd_offset_steps(uint8_t channel_id, agc_internal_t *p_agc)
{
    err_code_t result = ERR_SUCCESS;
    uint8_t step_limit_flag = FALSE;

    if (p_agc->pd_offset_steps > (MAX_PD_OFFSET - p_agc->pd_offset)) {
        p_agc->pd_offset_steps = MAX_PD_OFFSET - p_agc->pd_offset;
        step_limit_flag = TRUE;
    } else if (p_agc->pd_offset_steps < -p_agc->pd_offset) {
        p_agc->pd_offset_steps = -p_agc->pd_offset;
        step_limit_flag = TRUE;
    }

    if ((p_agc->pd_offset_steps != 0) || step_limit_flag) {

        if (p_agc->pd_offset_steps > 0) {
            g_agc_status[channel_id].pd_offset_change = AGC_STATE_INCREASED;
        } else if (p_agc->pd_offset_steps < 0) {
            g_agc_status[channel_id].pd_offset_change = AGC_STATE_DECREASED;
        } else if (MAX_PD_OFFSET == p_agc->pd_offset) {
            g_agc_status[channel_id].pd_offset_change = AGC_STATE_ATMAX;
        } else {
            g_agc_status[channel_id].pd_offset_change = AGC_STATE_ATMIN;
        }

        p_agc->pd_offset += p_agc->pd_offset_steps;
        p_agc->last_pd_offset_steps = p_agc->pd_offset_steps;

        if (p_agc->pd_offset_steps != 0) {
            /* PD offset changed, let the signal settle and start the PD offset step detection. */
            p_agc->settling_counter = p_agc->settling_counter_start;
            p_agc->step_found = FALSE;
            /* Note: This sets p_agc->pd_offset_changed to TRUE even if the PD offset didn't change because of
             * saturation, triggering a settling period with step detection. */
            p_agc->pd_offset_changed = TRUE;
            result = agc_hal_set_pd_offset(g_agc_config[channel_id].channel, p_agc->pd_offset);
        }
    }

    g_agc_status[channel_id].pd_offset_current = p_agc->pd_offset;

    return result;
}

/*!
 * \brief Controls PD offset.
 *
 * \param[in]    channel_id Index of the AGC instance to use.
 * \param[inout] p_agc      Pointer to the internal structure of the AGC instance to use.
 *
 * \retval ::ERR_SUCCESS Function returns without error.
 */
static err_code_t pd_offset_control(uint8_t channel_id, agc_internal_t *p_agc)
{
    uint16_t range_pd_offset_steps;
    int32_t base_correction;

    p_agc->pd_offset_steps = 0;
    if (p_agc->fastlock_state != FASTLOCK_FINISHED) {
        /* AGC just started or was reset, start with a fast PD offset approximation. */
        if (p_agc->fastlock_state == FASTLOCK_START) {
            /* Start with maximum step size. */
            p_agc->fastlock_steps = FASTLOCK_START_STEPS;
        }

        if (p_agc->baseline_tilt > MAX_LIMIT_BASELINE_TILT) {
            /* Beyond the upper range limit. */
            if (p_agc->fastlock_state == FASTLOCK_UNDER_RANGE) {
                /* Overshoot happened, halve the step size. */
                p_agc->fastlock_steps = M_MAX(1, p_agc->fastlock_steps >> 1);
            }
            p_agc->fastlock_state = FASTLOCK_OVER_RANGE;
            p_agc->pd_offset_steps = p_agc->fastlock_steps;
        } else if (p_agc->baseline_tilt < MIN_LIMIT_BASELINE_TILT) {
            /* Beyond the lower range limit. */
            if (p_agc->fastlock_state == FASTLOCK_OVER_RANGE) {
                /* Undershoot happened, halve the step size. */
                p_agc->fastlock_steps = M_MAX(1, p_agc->fastlock_steps >> 1);
            }
            p_agc->fastlock_state = FASTLOCK_UNDER_RANGE;
            p_agc->pd_offset_steps = -p_agc->fastlock_steps;
        } else if (p_agc->mean_pd_offset_signal_change != 0) {
            /* Within the range limits, normal control mode can be started. */
            p_agc->fastlock_state = FASTLOCK_FINISHED;
        } else {
            /* Start again */
            p_agc->fastlock_state = FASTLOCK_START;
        }
    } else {
        /* Normal control mode. */
        if (p_agc->mean_pd_offset_signal_change > 0) {
            /* Calculate the relative PD offset change needed to change the signal by about 20 % (see
             * PD_OFFSET_BASE_CORRECTION_X100) of the target signal range. */
            range_pd_offset_steps = p_agc->signal_range_limit / p_agc->mean_pd_offset_signal_change;
            base_correction =
                (M_MAX(1, range_pd_offset_steps * PD_OFFSET_BASE_CORRECTION_X100 / NORMALIZATION_FACTOR_100));
        } else {
            /* We don't have a valid signal step size, so let's assume only a PD offset stride of one. */
            range_pd_offset_steps = 0;
            base_correction = 1;
        }

        if (p_agc->baseline_tilt > MAX_LIMIT_BASELINE_TILT) {
            /* Upper range limit exceeded, correct for the excess plus an additional shift. */
            int32_t overshoot_compensation =
                ((p_agc->baseline_tilt - MAX_LIMIT_BASELINE_TILT) * range_pd_offset_steps) / MAX_LIMIT_BASELINE_TILT;
            int32_t new_pd_offset = overshoot_compensation + base_correction;

            if (p_agc->baseline_grad > 0) {
                /* Signal is still rising, increase the amount of correction. */
                new_pd_offset += base_correction / 2;
            }

            /* Limit PD offset jump to an 1/8 of the PD offset range. */
            p_agc->pd_offset_steps = M_MIN(((MAX_PD_OFFSET - MIN_PD_OFFSET) / 8), new_pd_offset);
        } else if (p_agc->baseline_tilt < MIN_LIMIT_BASELINE_TILT) {
            /* Lower range limit exceeded, correct for the excess plus an additional shift. */
            int32_t overshoot_compensation =
                ((p_agc->baseline_tilt - MIN_LIMIT_BASELINE_TILT) * range_pd_offset_steps) / MAX_LIMIT_BASELINE_TILT;
            int32_t new_pd_offset = overshoot_compensation - base_correction;

            if (p_agc->baseline_grad < 0) {
                /* Signal is still rising, increase the amount of correction. */
                new_pd_offset -= base_correction / 2;
            }

            /* Limit PD offset jump to an 1/8 of the PD offset range. */
            p_agc->pd_offset_steps = M_MAX(-((MAX_PD_OFFSET - MIN_PD_OFFSET) / 8), new_pd_offset);
        }
    }

    return set_pd_offset_steps(channel_id, p_agc);
}

/*!
 * \brief Estimates the normalized signal amplitude and calculates the standard deviation of the last found amplitudes.
 *
 * p_agc->amplitude_estimation.reset_counter must be non-zero when this function is called.
 *
 * \param[inout] p_agc Pointer to the internal structure of the AGC instance to use.
 */
static void estimate_amplitude(agc_internal_t *p_agc)
{
    /* Here the global minimum and maximum of the signal (baseline drift) is determined in a 4 second window (see
     * p_agc->amplitude_estimation.reset_time, SIGNAL_AMPLITUDE_DETECTION_TIME). */
    p_agc->amplitude_estimation.signal_max = M_MAX(p_agc->amplitude_estimation.signal_max, p_agc->baseline_drift);
    p_agc->amplitude_estimation.signal_min = M_MIN(p_agc->amplitude_estimation.signal_min, p_agc->baseline_drift);
    p_agc->amplitude_estimation.reset_counter--;

    if (0 == p_agc->amplitude_estimation.reset_counter) {
        /* At end of time window, amplitude is calculated and all other estimation parameter are reinitialized for
         * next window. */

        p_agc->estimated_amplitude_x1000 =
            ((p_agc->amplitude_estimation.signal_max - p_agc->amplitude_estimation.signal_min) *
             NORMALIZATION_FACTOR_1000 / (int32_t)p_agc->signal_range_limit);
        p_agc->rsd_amplitude_x1000 =
            calc_mov_std_deviation(p_agc->estimated_amplitude_x1000, &p_agc->amplitude_mov_sd_filter);

        reset_amplitude_estimation(&p_agc->amplitude_estimation);
    }
}

/*!
 * \brief Controls the LED current.
 *
 * \note The algorithm only tries to adjust the LED current if the PPG signal seems not to be superimposed by motion
 *       artifacts.
 *
 * \param[in]    channel_id Index of the AGC instance to use.
 * \param[inout] p_agc      Pointer to the internal structure of the AGC instance to use.
 *
 * \retval ::ERR_SUCCESS Function returns without error.
 */
static err_code_t led_current_control(uint8_t channel_id, agc_internal_t *p_agc)
{
    err_code_t result = ERR_SUCCESS;
    uint8_t step_limit_flag = FALSE;

    if (0 == p_agc->led_current_stride) {
        /* LED current is not changed, nothing to do. */
        return result;
    }

    /* Decrease the LED current in steps when the PD offset change is at maximum. */
    if (MAX_PD_OFFSET == p_agc->pd_offset && p_agc->led_current > g_agc_config[channel_id].led_current_min) {

        /* Check for the underflow. */
        if (p_agc->led_current >= p_agc->led_current_stride) {
            p_agc->led_current = p_agc->led_current - p_agc->led_current_stride;
            /* Due to fixed point operation the LED current may go below min LED current limit. */
            if (p_agc->led_current <= g_agc_config[channel_id].led_current_min) {
                p_agc->led_current = g_agc_config[channel_id].led_current_min;
            }
        } else {
            /* In case of under flow, fix the LED current to minimum. */
            p_agc->led_current = g_agc_config[channel_id].led_current_min;
        }

        g_agc_status[channel_id].led_change = AGC_STATE_DECREASED;
        p_agc->settling_counter = p_agc->settling_counter_start;
        p_agc->led_current_changed = TRUE;

        result = agc_hal_set_led_current(g_agc_config[channel_id].channel, p_agc->led_current);
        g_agc_status[channel_id].led_current = p_agc->led_current;

        return result;
    }

    /* Amplitude has a valid value means the amplitude estimation is complete, execute this step. */
    if (UNDEFINED_INT32 != p_agc->estimated_amplitude_x1000) {
        uint16_t rel_amplitude_motion_x1000 =
            g_agc_config[channel_id].rel_amplitude_motion_x100 * NORMALIZATION_FACTOR_10;
        uint16_t amplitude_steadiness_limit_x1000 = rel_amplitude_motion_x1000 / SIGNAL_AMPLITUDE_STEADINESS_RELATION;
        if ((p_agc->rsd_amplitude_x1000 < amplitude_steadiness_limit_x1000) &&
            (p_agc->estimated_amplitude_x1000 < rel_amplitude_motion_x1000)) {
            /* Signal is stable and motion artifacts seem to be low. */

            if (0 == g_agc_config[channel_id].num_led_steps) { /* Fast amplitude adjustment. */
                if ((p_agc->estimated_amplitude_x1000 >
                     g_agc_config[channel_id].rel_amplitude_max_x100 * NORMALIZATION_FACTOR_10) ||
                    (p_agc->estimated_amplitude_x1000 <
                     g_agc_config[channel_id].rel_amplitude_min_x100 * NORMALIZATION_FACTOR_10)) {
                    p_agc->estimated_amplitude_x1000 = M_MAX(1, p_agc->estimated_amplitude_x1000);
                    int32_t req_gain_x1000 =
                        ((g_agc_config[channel_id].rel_amplitude_max_x100 * NORMALIZATION_FACTOR_10) +
                         (g_agc_config[channel_id].rel_amplitude_min_x100 * NORMALIZATION_FACTOR_10)) *
                        NORMALIZATION_FACTOR_1000 / (2 * p_agc->estimated_amplitude_x1000);
                    int32_t led_current_steps =
                        ((req_gain_x1000 - NORMALIZATION_FACTOR_1000) * (p_agc->led_current + 1)) /
                        NORMALIZATION_FACTOR_1000;
                    p_agc->led_current_steps = M_MIN(INT16_MAX, M_MAX(INT16_MIN, led_current_steps));
                }

            } else { /* Normal amplitude adjustment. */
                if (p_agc->estimated_amplitude_x1000 >
                    g_agc_config[channel_id].rel_amplitude_max_x100 * NORMALIZATION_FACTOR_10) {
                    /* Signal amplitude too high, decrease LED current. */
                    p_agc->led_current_steps = -p_agc->led_current_stride;
                } else if (p_agc->estimated_amplitude_x1000 <
                           g_agc_config[channel_id].rel_amplitude_min_x100 * NORMALIZATION_FACTOR_10) {
                    /* Signal amplitude too low, increase LED current. */
                    p_agc->led_current_steps = p_agc->led_current_stride;
                }
            }

            /* Limit the LED current to the configured range. */
            if (p_agc->led_current_steps > (int16_t)(g_agc_config[channel_id].led_current_max - p_agc->led_current)) {
                p_agc->led_current_steps = g_agc_config[channel_id].led_current_max - p_agc->led_current;
                step_limit_flag = TRUE;
            } else if (p_agc->led_current_steps <
                       (int16_t)(g_agc_config[channel_id].led_current_min - p_agc->led_current)) {
                p_agc->led_current_steps = g_agc_config[channel_id].led_current_min - p_agc->led_current;
                step_limit_flag = TRUE;
            }

            if (p_agc->led_current_steps != 0 || step_limit_flag) {
                p_agc->settling_counter = p_agc->settling_counter_start;
                /* Note: This sets p_agc->led_current_changed to TRUE even if the LED current didn't change because of
                 * saturation, triggering a settling period, followed by amplitude estimation. */
                p_agc->led_current_changed = TRUE;

                if (p_agc->led_current_steps > 0) {
                    g_agc_status[channel_id].led_change = AGC_STATE_INCREASED;
                } else if (p_agc->led_current_steps < 0) {
                    g_agc_status[channel_id].led_change = AGC_STATE_DECREASED;
                } else if (g_agc_config[channel_id].led_current_max == p_agc->led_current) {
                    g_agc_status[channel_id].led_change = AGC_STATE_ATMAX;
                } else {
                    g_agc_status[channel_id].led_change = AGC_STATE_ATMIN;
                }

                if (0 == g_agc_config[channel_id].num_led_steps) { /* Fast amplitude adjustment. */
                    int32_t gain_x1000 = (p_agc->led_current + p_agc->led_current_steps) * NORMALIZATION_FACTOR_1000 /
                                         p_agc->led_current;
                    int32_t pd_offset_steps = ((gain_x1000 - NORMALIZATION_FACTOR_1000) * (int32_t)p_agc->pd_offset) /
                                              NORMALIZATION_FACTOR_1000;
                    p_agc->pd_offset_steps = M_MIN(INT16_MAX, M_MAX(INT16_MIN, pd_offset_steps));
                }

                p_agc->led_current = p_agc->led_current + p_agc->led_current_steps;

                if (p_agc->led_current_steps != 0) {
                    result = agc_hal_set_led_current(g_agc_config[channel_id].channel, p_agc->led_current);
                    if (ERR_SUCCESS == result && p_agc->pd_offset_steps) {
                        /* Compensate PD offset based on fast amplitude adjustments. (p_agc->pd_offset_steps is zero at
                         * this point when not performing fast amplitude adjustments.) */
                        result = set_pd_offset_steps(channel_id, p_agc);
                    }
                }
            }

            g_agc_status[channel_id].led_current = p_agc->led_current;
        }

        p_agc->estimated_amplitude_x1000 = UNDEFINED_INT32;
    } else {
        /* Amplitude estimation is ongoing, nothing to do. */
        return ERR_SUCCESS;
    }

    return result;
}

static err_code_t retrieve_led_status(uint8_t channel_id, agc_change_state_t *p_led_change, uint8_t *p_led_current)
{
    err_code_t result;

    uint8_t last_led_current = *p_led_current;
    agc_change_state_t last_change_state = *p_led_change;

    result = agc_hal_get_led_current(channel_id, p_led_current);
    if (ERR_SUCCESS == result) {
        if (AGC_STATE_UNDEFINED == last_change_state) {
            *p_led_change = AGC_STATE_NOT_CONTROLLED;
        } else {
            if (*p_led_current > last_led_current) {
                *p_led_change = AGC_STATE_INCREASED;
            } else if (*p_led_current < last_led_current) {
                *p_led_change = AGC_STATE_DECREASED;
            } else { /* *p_led_current == last_led_current */
                if (AGC_STATE_NOT_CONTROLLED == last_change_state) {
                    *p_led_change = AGC_STATE_NOT_CONTROLLED;
                } else {
                    *p_led_change = AGC_STATE_UNCHANGED;
                }
            }
        }
    } else if (ERR_LED_ACCESS == result) {
        /* No LED mapped to channel. */
        *p_led_current = 0;
        *p_led_change = AGC_STATE_UNDEFINED;
    } else {
        /* Unexpected return code. */
        M_CHECK_SUCCESS(result);
    }

    return ERR_SUCCESS;
}

/******************************************************************************
 *                             GLOBAL FUNCTIONS                               *
 ******************************************************************************/

err_code_t agc_initialize(void)
{
    memset(g_agc_config, 0x00, sizeof(g_agc_config));
    memset(g_agc, 0x00, sizeof(g_agc));
    memset(g_agc_status, 0x00, sizeof(g_agc_status));
    g_agc_channel_cnt = 0;
    g_agc_state = STATE_CONFIGURATION;

    return ERR_SUCCESS;
}

err_code_t agc_set_configuration(const agc_configuration_t *p_agc_configs, uint8_t agc_config_num)
{
    if (g_agc_state != STATE_CONFIGURATION) {
        return ERR_PERMISSION;
    }

    if (agc_config_num > 0) {
        M_CHECK_NULL_POINTER(p_agc_configs);
    }
    if (agc_config_num > AGC_MAX_CHANNEL_CNT) {
        return ERR_ARGUMENT;
    }

    /* Validating the input configuration. */
    for (int i = 0; i < agc_config_num; i++) {

        if (0 != p_agc_configs[i].reserved[0]) {
            return ERR_ARGUMENT;
        }
        if (0 != p_agc_configs[i].reserved[1]) {
            return ERR_ARGUMENT;
        }
        if (0 != p_agc_configs[i].reserved[2]) {
            return ERR_ARGUMENT;
        }

        if (CHANNEL_DISABLED == p_agc_configs[i].channel) {
            return ERR_ARGUMENT;
        }

        if (AGC_MODE_DEFAULT == p_agc_configs[i].mode) {
            if (p_agc_configs[i].led_control_mode > AGC_AMPL_CNTL_MODE_EXTERNAL) {
                return ERR_ARGUMENT;
            }
            if (p_agc_configs[i].led_current_max < p_agc_configs[i].led_current_min) {
                return ERR_ARGUMENT;
            }
            if (p_agc_configs[i].rel_amplitude_min_x100 > NORMALIZATION_FACTOR_100) {
                return ERR_ARGUMENT;
            }
            if (p_agc_configs[i].rel_amplitude_max_x100 > NORMALIZATION_FACTOR_100) {
                return ERR_ARGUMENT;
            }
            if (p_agc_configs[i].rel_amplitude_max_x100 < p_agc_configs[i].rel_amplitude_min_x100) {
                return ERR_ARGUMENT;
            }
            if (p_agc_configs[i].rel_amplitude_motion_x100 > NORMALIZATION_FACTOR_100) {
                return ERR_ARGUMENT;
            }
            if (p_agc_configs[i].rel_amplitude_max_x100 > p_agc_configs[i].rel_amplitude_motion_x100) {
                return ERR_ARGUMENT;
            }
            if (AGC_AMPL_CNTL_MODE_AUTO == p_agc_configs[i].led_control_mode) {
                if (p_agc_configs[i].num_led_steps >
                    (p_agc_configs[i].led_current_max - p_agc_configs[i].led_current_min)) {
                    return ERR_ARGUMENT;
                }
            }
            if (p_agc_configs[i].threshold_max <= p_agc_configs[i].threshold_min) {
                return ERR_ARGUMENT;
            }
        } else if (AGC_MODE_STATUS == p_agc_configs[i].mode) {
            /* Do nothing: All further parameters are not used in this case. */
        } else {
            return ERR_ARGUMENT;
        }
    }

    g_agc_channel_cnt = agc_config_num;
    memcpy(g_agc_config, p_agc_configs, sizeof(agc_configuration_t) * agc_config_num);

    return ERR_SUCCESS;
}

err_code_t agc_get_configuration(agc_configuration_t *p_agc_configs, uint8_t *p_agc_config_num)
{
    if (STATE_UNINITIALIZED == g_agc_state) {
        return ERR_PERMISSION;
    }

    M_CHECK_NULL_POINTER(p_agc_configs);
    M_CHECK_NULL_POINTER(p_agc_config_num);

    if (*p_agc_config_num < g_agc_channel_cnt) {
        return ERR_SIZE;
    }

    memcpy(p_agc_configs, g_agc_config, g_agc_channel_cnt * sizeof(agc_configuration_t));
    *p_agc_config_num = g_agc_channel_cnt;

    return ERR_SUCCESS;
}

err_code_t agc_start_processing(void *p_config, uint16_t size)
{
    uint32_t sampling_period;

    if (g_agc_state != STATE_CONFIGURATION) {
        return ERR_PERMISSION;
    }

    M_CHECK_SUCCESS(agc_hal_initialize(p_config, size));

    memset(g_agc, 0x00, sizeof(g_agc));

    for (int i = 0; i < g_agc_channel_cnt; i++) {

        switch (g_agc_config[i].mode) {
        case AGC_MODE_DEFAULT:
            /* Get sample period from HAL (microsecond) and convert to milliseconds. */
            M_CHECK_SUCCESS(agc_hal_get_sampling_period_us(g_agc_config[i].channel, &sampling_period));
            sampling_period /= 1000;
            if (0 == sampling_period) {
                return ERR_SYSTEM_CONFIG;
            }

            g_agc[i].range_center = (g_agc_config[i].threshold_max + g_agc_config[i].threshold_min) / 2;
            g_agc[i].signal_range_limit = g_agc_config[i].threshold_max - g_agc_config[i].threshold_min;

            /* Initial value of the settling counter = settling time / sampling period. This counter determines the
             * maximum settling time after the PD offset was changed. The settling time can be shortened, if a PPG jump
             * is found: jump found + step detection filter lag. */
            g_agc[i].settling_counter_start = (SETTLING_TIME / sampling_period);
            g_agc[i].settling_counter = g_agc[i].settling_counter_start;
            g_agc[i].baseline_filter.size = SIGNAL_MOVE_MEAN_WINDOW_SIZE / sampling_period;
            g_agc[i].baseline_gradient.sampling_period = sampling_period;

            g_agc[i].step_detect_mov_mean_filter.size = STEP_DETECTION_LAG;
            g_agc[i].step_detect_mov_sd_filter.size = STEP_DETECTION_LAG;

            g_agc[i].rsd_pd_offset_signal_change_x100 = NORMALIZATION_FACTOR_100;
            g_agc[i].signal_stride_mov_mean_filter.size = SIGNAL_STRIDE_MOV_MEAN_SAMPLE_SIZE;
            g_agc[i].signal_stride_mov_median_filter.size = SIGNAL_STRIDE_MOV_MEDIAN_SAMPLE_SIZE;
            g_agc[i].signal_stride_mov_sd_filter.size = SIGNAL_STRIDE_MOV_SD_SAMPLE_SIZE;
            calc_mov_std_deviation(SIGNAL_STRIDE_MOV_SD_INIT_VALUE_FIRST, &g_agc[i].signal_stride_mov_sd_filter);
            calc_mov_std_deviation(SIGNAL_STRIDE_MOV_SD_INIT_VALUE_SECOND, &g_agc[i].signal_stride_mov_sd_filter);

            g_agc[i].pd_offset = PD_OFFSET_INIT;
            g_agc[i].fastlock_steps = FASTLOCK_START_STEPS;

            g_agc[i].estimated_amplitude_x1000 = UNDEFINED_INT32;
            g_agc[i].rsd_amplitude_x1000 = NORMALIZATION_FACTOR_1000;
            reset_amplitude_estimation(&g_agc[i].amplitude_estimation);
            g_agc[i].amplitude_estimation.reset_time = M_MAX(1, (SIGNAL_AMPLITUDE_DETECTION_TIME / sampling_period));
            g_agc[i].amplitude_mov_sd_filter.size = AMPLITUDE_MOV_SD_SAMPLE_SIZE;
            reset_amplitude_filter_values(&g_agc[i].amplitude_mov_sd_filter);

            /* When the amplitude control is enabled in the AGC algorithm, the initial value of the
             * LED current shall be the mean of the configured maximum and minimum LED current. */
            g_agc[i].led_current = (g_agc_config[i].led_current_min + g_agc_config[i].led_current_max) / 2;
            if (g_agc_config[i].num_led_steps > 0) {
                g_agc[i].led_current_stride = ((g_agc_config[i].led_current_max - g_agc_config[i].led_current_min) /
                                               g_agc_config[i].num_led_steps);
                g_agc[i].led_current_stride = M_MAX(1, g_agc[i].led_current_stride);
            } else { /* Fast amplitude control mode. */
                g_agc[i].led_current_stride = g_agc_config[i].led_current_max - g_agc_config[i].led_current_min;
            }

            if (AGC_AMPL_CNTL_MODE_DISABLED == g_agc_config[i].led_control_mode ||
                AGC_AMPL_CNTL_MODE_EXTERNAL == g_agc_config[i].led_control_mode) {
                g_agc_status[i].led_current = 0;
                g_agc_status[i].led_change = AGC_STATE_UNDEFINED;
                M_CHECK_SUCCESS(retrieve_led_status(g_agc_config[i].channel, &(g_agc_status[i].led_change),
                                                    &(g_agc_status[i].led_current)));
            } else {
                g_agc_status[i].led_change = AGC_STATE_UNCHANGED;
                g_agc_status[i].led_current = g_agc[i].led_current;
                M_CHECK_SUCCESS(agc_hal_set_led_current(g_agc_config[i].channel, g_agc[i].led_current));
            }

            g_agc_status[i].pd_offset_change = AGC_STATE_UNCHANGED;
            g_agc_status[i].pd_offset_current = g_agc[i].pd_offset;
            M_CHECK_SUCCESS(agc_hal_set_pd_offset(g_agc_config[i].channel, g_agc[i].pd_offset));

            break;

        case AGC_MODE_STATUS:

            g_agc_status[i].led_current = 0;
            g_agc_status[i].led_change = AGC_STATE_UNDEFINED;
            M_CHECK_SUCCESS(retrieve_led_status(g_agc_config[i].channel, &(g_agc_status[i].led_change),
                                                &(g_agc_status[i].led_current)));

            g_agc_status[i].pd_offset_change = AGC_STATE_NOT_CONTROLLED;
            M_CHECK_SUCCESS(agc_hal_get_pd_offset(g_agc_config[i].channel, &(g_agc_status[i].pd_offset_current)));
            break;

        default:

            return ERR_CONFIG;
        }
    }

    g_agc_state = STATE_PROCESSING;

    return ERR_SUCCESS;
}

err_code_t agc_execute(const uint8_t *p_fifo_data, uint16_t fifo_data_size)
{
    int32_t raw_vals[EXTRACTED_MESSAGE_BUF_SIZE];
    uint16_t num_raw_vals, sample_idx;
    uint8_t new_fifo_data = TRUE;

    if (g_agc_state != STATE_PROCESSING) {
        return ERR_PERMISSION;
    }

    M_CHECK_NULL_POINTER(p_fifo_data);
    if (0 == fifo_data_size) {
        return ERR_SIZE;
    }

    for (uint8_t channel_id = 0; channel_id < g_agc_channel_cnt; channel_id++) {

        switch (g_agc_config[channel_id].mode) {

        case AGC_MODE_DEFAULT:

            if (AGC_AMPL_CNTL_MODE_AUTO == g_agc_config[channel_id].led_control_mode) {
                g_agc_status[channel_id].led_change = AGC_STATE_UNCHANGED;
                g_agc_status[channel_id].led_current = g_agc[channel_id].led_current;
            } else if (AGC_AMPL_CNTL_MODE_EXTERNAL == g_agc_config[channel_id].led_control_mode) {
                // TODO: Implement synchronization of externally set LED current
            }
            g_agc_status[channel_id].pd_offset_change = AGC_STATE_UNCHANGED;
            g_agc_status[channel_id].pd_offset_current = g_agc[channel_id].pd_offset;

            num_raw_vals = sizeof(raw_vals) / sizeof(raw_vals[0]);
            M_CHECK_SUCCESS(agc_hal_extract_samples(g_agc_config[channel_id].channel, p_fifo_data, fifo_data_size,
                                                    new_fifo_data, raw_vals, &num_raw_vals));
            new_fifo_data = FALSE;

            for (sample_idx = 0; sample_idx < num_raw_vals; sample_idx++) {
                /* Calculation of the auxiliary parameters from the current PPG signal for PD offset control. */
                calc_signal_params(raw_vals[sample_idx], &g_agc[channel_id]);
                calc_step_detection_params(raw_vals[sample_idx], &g_agc[channel_id]);

                if (AGC_AMPL_CNTL_MODE_AUTO == g_agc_config[channel_id].led_control_mode) {
                    /* Estimate signal amplitude for LED current control. */
                    estimate_amplitude(&g_agc[channel_id]);
                }
                g_agc[channel_id].pd_offset_steps = 0;
                g_agc[channel_id].led_current_steps = 0;

                if (g_agc[channel_id].settling_counter > 0) {
                    /* PD offset or LED current change settling time is active. */
                    if (g_agc[channel_id].pd_offset_changed) {
                        /* PD offset step detection. */
                        detect_pd_offset_steps(raw_vals[sample_idx], &g_agc[channel_id]);
                    }

                    g_agc[channel_id].settling_counter -= 1;

                    if (0 == g_agc[channel_id].settling_counter) {
                        if (AGC_AMPL_CNTL_MODE_AUTO == g_agc_config[channel_id].led_control_mode) {
                            /* Reset amplitude estimation of LED current control. */
                            reset_amplitude_estimation(&g_agc[channel_id].amplitude_estimation);
                            reset_amplitude_filter_values(&g_agc[channel_id].amplitude_mov_sd_filter);
                            g_agc[channel_id].estimated_amplitude_x1000 = UNDEFINED_INT32;

                            if (g_agc[channel_id].led_current_changed) {
                                /* Reset filters when settling counter expired after LED current change. There is no
                                 * need to reset the filters after PD offset reset here, as they are already reset as
                                 * soon as a step is detected (see detect_pd_offset_steps). */
                                lp_filter_reset(&g_agc[channel_id].baseline_filter);
                                filter_reset(&g_agc[channel_id].step_detect_mov_mean_filter);
                                filter_reset(&g_agc[channel_id].step_detect_mov_sd_filter);
                            }
                        }
                        /* Ready for the next PD offset or LED current control action */
                        g_agc[channel_id].pd_offset_changed = FALSE;
                        g_agc[channel_id].led_current_changed = FALSE;
                    }
                } else {
                    /* PD offset control */
                    M_CHECK_SUCCESS(pd_offset_control(channel_id, &g_agc[channel_id]));

                    if (0 == g_agc[channel_id].pd_offset_steps) {
                        /* LED current control is only performed when PD offset is not changed. */
                        if (AGC_AMPL_CNTL_MODE_AUTO == g_agc_config[channel_id].led_control_mode) {
                            /* LED control enabled */
                            M_CHECK_SUCCESS(led_current_control(channel_id, &g_agc[channel_id]));
                        } else if (AGC_AMPL_CNTL_MODE_EXTERNAL == g_agc_config[channel_id].led_control_mode) {
                            /* LED current can be controlled by an Vital Sign algorithm by setting a control request via
                             * the Chip Library: increase/decrease LED current by one current stride as configured or by
                             * an amount given as function argument. */
                        } else {
                            /* LED current control is disabled - nothing to do. */
                        }
                    }
                }
                /* Current ADC value will be needed for the next sample. */
                g_agc[channel_id].prev_sample = raw_vals[sample_idx];
            }
            break;

        case AGC_MODE_STATUS:

            /* nothing do do */
            break;

        default:

            return ERR_CONFIG;
        }
    }

    /* Update the LED current in a separate loop. The current could be updated by another channel.
     * (e.g. Two channels control the same LED) */
    for (uint8_t channel_id = 0; channel_id < g_agc_channel_cnt; channel_id++) {
        if ((AGC_MODE_STATUS == g_agc_config[channel_id].mode) ||
            (AGC_MODE_DEFAULT == g_agc_config[channel_id].mode &&
             AGC_AMPL_CNTL_MODE_DISABLED == g_agc_config[channel_id].led_control_mode))
            M_CHECK_SUCCESS(retrieve_led_status(g_agc_config[channel_id].channel,
                                                &(g_agc_status[channel_id].led_change),
                                                &(g_agc_status[channel_id].led_current)));
    }

    return ERR_SUCCESS;
}

err_code_t agc_get_status(agc_status_t *p_agc_status, uint8_t *p_agc_status_num)
{
    if (g_agc_state != STATE_PROCESSING) {
        return ERR_PERMISSION;
    }

    M_CHECK_NULL_POINTER(p_agc_status);
    M_CHECK_NULL_POINTER(p_agc_status_num);

    if (*p_agc_status_num < g_agc_channel_cnt) {
        return ERR_SIZE;
    }

    memcpy(p_agc_status, g_agc_status, g_agc_channel_cnt * sizeof(agc_status_t));
    *p_agc_status_num = g_agc_channel_cnt;

    return ERR_SUCCESS;
}

err_code_t agc_stop_processing(void)
{
    err_code_t result;

    if (STATE_UNINITIALIZED == g_agc_state) {
        return ERR_PERMISSION;
    }

    result = agc_hal_shutdown();
    if (ERR_SUCCESS == result) {
        g_agc_state = STATE_CONFIGURATION;
    }

    return result;
}

err_code_t agc_shutdown(void)
{
    g_agc_state = STATE_UNINITIALIZED;

    return agc_hal_shutdown();
}

err_code_t agc_get_version(agc_version_t *p_agc_version)
{
    M_CHECK_NULL_POINTER(p_agc_version);

    p_agc_version->major = AGC_VER_MAJOR;
    p_agc_version->minor = AGC_VER_MINOR;
    p_agc_version->patch = AGC_VER_PATCH;

    return ERR_SUCCESS;
}
