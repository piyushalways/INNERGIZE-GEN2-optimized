#ifndef EMS_PWM_H
#define EMS_PWM_H

#include <stdint.h>
#include <stdbool.h>
/**
 * @brief Initialise EMS timers and PWM params to default
 * 
 * @return 0 on success
 */
int ems_pwm_init();

/**
 * @brief toggle EMS on/off
 * 
 * @param state 0 for off, 1 for off
 */
void ems_pwm_toggle(int state);

/**
 * @brief update pwm parameters for the ems
 * 
 * @param chan_number channel number (0 and 1 supported)
 * @param on_time_ns on time in nanoseconds
 * @param duration_ns total duration of the PWM signal
 * @param interval_ns time between consecutive PWM signals
 * @return 0 in success
 */
int ems_pwm_update_params(uint8_t chan_number, uint64_t on_time_ns, uint64_t duration_ns, uint64_t interval_ns);

/**
 * @brief update duty cycle of the power signal(CHAN2)
 * 
 * @param duty_cycle duty cycle in percentage(0-100)
 */

void chan0_para_update();

void chan23update();

void chan23reset();

void RelaxMode();

void SleepMode();

void BreathMode();

// Structure to store the EMS intensity data
typedef struct {
    long PWM_PERIOD;
    long PWM_ON_TIME;
    long PWM_INTERVAL;
    long PWM_DURATION;
    long CHAN0_PLAYBACK;
    long CHAN0_INDUCTOR;
    long PWM23_DURATION;
    long PWM23_ON_DURATION;
    long CHAN0_DURATION;
    long CHAN0_ON_DURATION;
    
} ems_values;

extern ems_values ems_intensity_data; // Declare a global instance
extern uint64_t CHAN23_PWM_DEFAULT_PERIOD_NS ;
extern uint64_t CHAN23_PWM_DEFAULT_ON_TIME_NS ;
extern bool is_pwm_modes_enabled;
extern bool battery_update_ready;

#endif
