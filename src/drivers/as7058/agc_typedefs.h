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

#ifndef __AGC_TYPEDEFS_H__
#define __AGC_TYPEDEFS_H__

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

/*!
 * \file      agc_typedefs.h
 * \authors   RSIN
 * \copyright ams
 * \addtogroup VITAL_SIGNS_AGC Vital Signs AGC
 *
 * @{
 */

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include "error_codes.h"
#include "std_inc.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

#ifndef AGC_MAX_CHANNEL_CNT
/*! The maximum number of enabled AGC instances. */
#define AGC_MAX_CHANNEL_CNT 4
#endif

/*! AGC current change information. */
enum agc_change_state {
    AGC_STATE_UNCHANGED = 0,      /*!< Current not changed. */
    AGC_STATE_INCREASED = 1,      /*!< Current increased. */
    AGC_STATE_DECREASED = 2,      /*!< Current decreased. */
    AGC_STATE_ATMIN = 3,          /*!< Current needs to be decreased, but is at the lower limit. */
    AGC_STATE_ATMAX = 4,          /*!< Current needs to be increased, but is at the upper limit. */
    AGC_STATE_NOT_CONTROLLED = 5, /*!< Current is not controlled as amplitude control is disabled. */
    AGC_STATE_UNDEFINED = 6,      /*!< Current is undefined. For example the channel has no connected LED. */
};

/*! Type for ::agc_change_state */
typedef uint8_t agc_change_state_t;

/*! Status information of an instance of the AGC algorithm. */
typedef struct {
    agc_change_state_t pd_offset_change; /*!< Change information for the photodiode offset current. */
    uint8_t pd_offset_current;           /*!< Current value of the photodiode offset current as a register value. */
    agc_change_state_t led_change;       /*!< Change information for the LED current. */
    uint8_t led_current;                 /*!< Current value of the LED current as a register value. */
} agc_status_t;

/*! Operating modes of the AGC algorithm. */
enum agc_mode {
    AGC_MODE_DEFAULT = 0, /*!< Default mode. */
    AGC_MODE_STATUS = 1,  /*!< AGC algorithm is disabled but returns at least one status package for the selected
                               channel. */
};

/*! Type for ::agc_mode. */
typedef uint8_t agc_mode_t;

/*! Amplitude control modes of the AGC algorithm. */
enum agc_ampl_cntl_mode {
    AGC_AMPL_CNTL_MODE_DISABLED = 0, /*!< No amplitude control enabled. */
    AGC_AMPL_CNTL_MODE_AUTO = 1,     /*!< Internal amplitude control enabled. */
    AGC_AMPL_CNTL_MODE_EXTERNAL = 2, /*!< Amplitude is controlled by an external algorithm. */
};

/*! Type for ::agc_ampl_cntl_mode. */
typedef uint8_t agc_ampl_cntl_mode_t;

/*! Represents a PPG channel. A value of 0 represents a disabled channels, all other values are chip-specific. */
typedef uint8_t agc_channel_id_t;

/*!
 * Configuration of an instance of the AGC algorithm.
 *
 * \note For mode ::AGC_MODE_STATUS all the parameters but channel are unused and should be set to zero.
 */
typedef struct {
    agc_mode_t mode;                       /*!< Selects the AGC algorithm mode. */
    agc_ampl_cntl_mode_t led_control_mode; /*!< Selects the LED amplitude control mode. */
    agc_channel_id_t channel;              /*!< Selects the PPG channel that is controlled. */
    uint8_t led_current_min;               /*!< Lower bound of the LED current range as a register value. */
    uint8_t led_current_max;               /*!< Upper bound of the LED current range as a register value. */
    uint8_t rel_amplitude_min_x100; /*!< Lower bound of the targeted PPG signal amplitude, relative to the size of the
                                         target PGG signal range. The unit of this field is percent. The minimum valid
                                         value is 0, the maximum valid value is 100. */
    uint8_t rel_amplitude_max_x100; /*!< Upper bound of the targeted PPG signal amplitude, relative to the size of the
                                         target PGG signal range. The unit of this field is percent. This value must not
                                         be less than rel_amplitude_min_x100. The maximum valid value is 100. */
    uint8_t rel_amplitude_motion_x100; /*!< Minimum PPG signal amplitude at which the PPG signal is considered a motion
                                            artifact. The threshold is relative to the size of the target PGG signal
                                            range. The unit of this field is percent. This value must not
                                            be less than rel_amplitude_max_x100. The maximum valid value is 100. */
    uint8_t num_led_steps; /*!< Number of steps the LED current range is partitioned in. When the AGC algorithm
                                determines that the LED current needs to be increased or decreased and the bounds of the
                                LED current range are not yet reached, the LED current is adjusted by one step. If
                                led_control_mode is set to ::AGC_AMPL_CNTL_MODE_AUTO, this value must not be zero and
                                must not be greater than the size of the LED current range. */
    uint8_t reserved[3];   /*!< Padding bytes. Needs to be set to zero. */
    int32_t threshold_min; /*!< Lower bound of the target PPG signal range. The unit of this field is ADC counts. */
    int32_t threshold_max; /*!< Upper bound of the target PPG signal range. The unit of this field is ADC counts. This
                                value must be greater than threshold_min. */
} agc_configuration_t;

/*! Version information of the AGC module. */
typedef struct {
    uint8_t major; /*!< Major version. */
    uint8_t minor; /*!< Minor version. */
    uint8_t patch; /*!< Patch version. */
} agc_version_t;

M_STATIC_ASSERT_TYPE_SIZE(agc_status_t, 4);
M_STATIC_ASSERT_TYPE_SIZE(agc_configuration_t, 20);
M_STATIC_ASSERT_TYPE_SIZE(agc_version_t, 3);

#ifdef __cplusplus
}
#endif // __cplusplus

/*! @} */

#endif /* __AGC_TYPEDEFS_H__ */
