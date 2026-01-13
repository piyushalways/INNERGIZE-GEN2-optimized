#include "ems_engine.h"
#include "startup.h"
#include "io_adapter.h"

#include <zephyr/kernel.h>
#include <zephyr/drivers/pwm.h>
#include <nrfx_timer.h>
#include <nrfx_pwm.h>
#include <hal/nrf_gpio.h>
#include <string.h>
#include <zephyr/logging/log.h>
#include <hal/nrf_timer.h>


LOG_MODULE_REGISTER(EMS_PWM, LOG_LEVEL_INF);

ems_values ems_intensity_data = {
    .PWM_PERIOD = 64,
    .PWM_ON_TIME = 45,
    .PWM_INTERVAL = 10,
    .PWM_DURATION = 5,
    .CHAN0_PLAYBACK = 3,
    .CHAN0_INDUCTOR = 3,
    .PWM23_DURATION = 1000,
    .PWM23_ON_DURATION = 900,
};

// {64, 40, 5, 12, 11, 11}; // Default values for the EMS

/* 502 = 64
 503 = 20
 504 = 5
 505 = 12
 506 =11
 507 =11
 for 3 seconds 
 508 =  seconds total (6)
 509 = on duration (120)
 for 5
 508 = 10
 509= 200

sint32 little
*/

#define CHAN0_GPIO_PIN                          DT_GPIO_PIN(DT_ALIAS(ems_chan0_gpio), gpios)
#define CHAN0_DEFAULT_ON_TIME                   (PWM_MSEC(500))
#define CHAN0_DEFAULT_PERIOD                    (PWM_SEC(2))

#if (CONFIG_BOARD_EMS_NRF52840)
#define CHAN1_PWM_GPIO_PIN                      4
#else 
#define CHAN1_PWM_GPIO_PIN                      44
#endif

#define CHAN1_PWM_INST                          NRFX_PWM_INSTANCE(20)
#define CHAN1_PWM_PERIOD_NS                     PWM_USEC(64)
#define CHAN1_PWM_DEFAULT_ON_TIME_NS            PWM_USEC(20)
#define POWER_SIGNAL_DEFAULT_INTERVAL_NS        PWM_MSEC(20)
#define POWER_SIGNAL_DEFAULT_DURATION_NS        PWM_MSEC(40)

#if (CONFIG_BOARD_EMS_NRF52840)
#define CHAN2_PWM_GPIO_PIN                      27
#else
#define CHAN2_PWM_GPIO_PIN                      43
#endif

#if (CONFIG_BOARD_EMS_NRF52840)
#define CHAN3_PWM_GPIO_PIN                      26
#else
#define CHAN3_PWM_GPIO_PIN                      39
#endif

#define CHAN23_PWM_INST                         NRFX_PWM_INSTANCE(21)

#define CHAN23_DEFAULT_DURATION_NS              PWM_MSEC(100)

#define TIMER_INSTANCE_NUMBER 21

K_MUTEX_DEFINE(update_mut);

// Parameters for a generic EMS pwm channel
struct pwm_mode_chan_spec {
    uint64_t active_duration_ns; // Time the signal is on
    uint64_t interval_ns; // Time between consecutive signals
    uint64_t pwm_on_time_ns;
    int8_t status; // 1/0 (on/off)
};

// Timer for channel 0
const nrfx_timer_t pwm_modes_timer = NRFX_TIMER_INSTANCE(TIMER_INSTANCE_NUMBER);

// Channel 1 PWM instance
const nrfx_pwm_t chan1_pwm_inst = CHAN1_PWM_INST;
nrf_pwm_values_common_t chan1_seq_common_values = 0;
nrf_pwm_values_t chan1_seq_values = {.p_common = &chan1_seq_common_values};
nrf_pwm_sequence_t chan1_sequence = {
    .length = 1,
    .repeats = 0,
    .end_delay = 0
};

// Channels 2 and 3 PWM instance (channel 2 and 3 are independent channels on the PWM instance)
const nrfx_pwm_t chan23_pwm_inst = CHAN23_PWM_INST;
nrf_pwm_values_individual_t chan23_pwm_seq_ind_values ;

nrf_pwm_values_t chan23_values = {.p_individual = &chan23_pwm_seq_ind_values};
nrf_pwm_sequence_t chan23_sequence = {
    .length = 4,
    .repeats = 0,
    .end_delay = 0
};

struct pwm_mode_chan_spec chan0_spec = {
    .active_duration_ns = (CHAN0_DEFAULT_PERIOD - CHAN0_DEFAULT_ON_TIME),
    .interval_ns = (CHAN0_DEFAULT_ON_TIME),
    .status = 0
};

struct pwm_mode_chan_spec chan1_spec = {
    .active_duration_ns = POWER_SIGNAL_DEFAULT_DURATION_NS,
    .interval_ns = POWER_SIGNAL_DEFAULT_INTERVAL_NS,
    .pwm_on_time_ns = CHAN1_PWM_DEFAULT_ON_TIME_NS,
    .status = 0
};

struct pwm_mode_chan_spec chan2_spec = {
    .active_duration_ns = CHAN23_DEFAULT_DURATION_NS,
    .status = 0
};

struct pwm_mode_chan_spec chan3_spec = {
    .active_duration_ns = CHAN23_DEFAULT_DURATION_NS,
    .status = 0
};

struct pwm_mode_chan_spec update_buf[] = {
    {0}, // Channel 0
    {0}, // Channel 1
    {0}, // Channel 2
    {0}  // Channel 3
};

uint32_t chan0_counter = 0; // Timer counter for channel 0
uint32_t chan1_counter_on = 0, chan1_counter_off = 0; // counter_on -> timer counter when chan1 is active, counter_off -> counter when chan1 is inactive
uint16_t power_signal_count = 3, power_signal_counter = 0; // power_signal_count -> number of chan1 signals to trigger, signal_counter -> counts number of signals triggered, Default is 3
uint8_t active_stimulating_chan = 2; // Channel to toggle the stimulating signal on (2 or 3)
uint8_t chan_param_update_available = 0; // Flag set when channel parameters have been updated but not triggered
bool is_pwm_modes_enabled = false; // Flag set when EMS is enabled, default false
bool battery_update_ready = false;

// Initialise channel 0
static void chan0_gpio_init() {
    LOG_INF("Config channel 0 pin");

    nrf_gpio_cfg_output(CHAN0_GPIO_PIN);
    nrf_gpio_pin_clear(CHAN0_GPIO_PIN);
}

void chan0_para_update()
{
    chan0_spec.active_duration_ns = PWM_SEC(ems_intensity_data.CHAN0_DURATION) - (25*PWM_MSEC(ems_intensity_data.CHAN0_ON_DURATION));
    chan0_spec.interval_ns = 25*PWM_MSEC(ems_intensity_data.CHAN0_ON_DURATION);
}


// Update the power signal count
static void update_power_signal_count() {
    power_signal_count = chan0_spec.active_duration_ns / (PWM_MSEC(ems_intensity_data.PWM_DURATION) + PWM_MSEC(ems_intensity_data.PWM_INTERVAL));
}

// Event handler for channel 1 PWM 
static void chan1_pwm_event_handler(nrfx_pwm_evt_type_t event_type, void *p_context) {
    if (event_type == NRFX_PWM_EVT_STOPPED) {
        chan1_spec.status = 0;
    }
}

// Initialise channel 1
static int chan1_pwm_init() {
    nrfx_err_t ret = 0;
    nrfx_pwm_config_t chan1_pwm_conf = NRFX_PWM_DEFAULT_CONFIG(CHAN1_PWM_GPIO_PIN, 
                                        NRF_PWM_PIN_NOT_CONNECTED, 
                                        NRF_PWM_PIN_NOT_CONNECTED, 
                                        NRF_PWM_PIN_NOT_CONNECTED);

    chan1_pwm_conf.top_value = (PWM_USEC(ems_intensity_data.PWM_PERIOD) / NSEC_PER_USEC); // At 1 MHz top val will be the usec value

    nrfx_pwm_uninit(&chan1_pwm_inst); // Uninit to initialise with new custom values

    ret = nrfx_pwm_init(&chan1_pwm_inst, &chan1_pwm_conf, chan1_pwm_event_handler, NULL);

    if (ret == NRFX_SUCCESS) {
        IRQ_DIRECT_CONNECT(PWM20_IRQn, 0, nrfx_pwm_20_irq_handler, 0);
        irq_enable(PWM20_IRQn);
        return 0;
    }

    LOG_ERR("Chan1 pwm init fail (err 0x%08x)", ret);
    return -ENODEV;
}

// Update the on time of the PWM signal
static int chan1_pwm_update_on_time(uint32_t on_time_ns) { 
    if (on_time_ns > 0) {
        chan1_seq_common_values = ((PWM_USEC(ems_intensity_data.PWM_PERIOD) - PWM_USEC(ems_intensity_data.PWM_ON_TIME)) / NSEC_PER_USEC);
        chan1_seq_values.p_common = &chan1_seq_common_values;
        chan1_sequence.values = chan1_seq_values;
    } else {   
        nrfx_pwm_stop(&chan1_pwm_inst, false);
        return 0;     
    }

    uint16_t playback_count = (PWM_MSEC(ems_intensity_data.PWM_DURATION) / PWM_USEC(ems_intensity_data.PWM_PERIOD));

    //LOG_DBG("Chan1 playback count %d", playback_count);
    
    // If the playback is successful, set the status to 1
    if (nrfx_pwm_simple_playback(&chan1_pwm_inst, &chan1_sequence, playback_count, NRFX_PWM_FLAG_STOP) == 0) {
        chan1_spec.status = 1;
        return 0;
    }

    LOG_ERR("Start PWM playback fail");
    return -EIO;
}

// Toggle the power signal
static void chan1_toggle_power_signal() {
    update_power_signal_count();

    if (power_signal_counter >= power_signal_count) {
        return;
    } else if (chan1_spec.status == 0) {
        chan1_pwm_update_on_time(PWM_USEC(ems_intensity_data.PWM_ON_TIME));
        power_signal_counter++;
    }
}

// Event handler for channel 2 and 3 PWM
static void chan23_pwm_event_handler(nrfx_pwm_evt_type_t event_type, void *p_context) {   
    if (event_type == NRFX_PWM_EVT_STOPPED) {
        active_stimulating_chan = (active_stimulating_chan == 2) ? 3 : 2;
    }
}

// Toggle the channel 2 and 3 PWM signals 
static int chan23_toggle() {
    if (active_stimulating_chan == 2) {
        chan23_pwm_seq_ind_values.channel_0 = chan2_spec.pwm_on_time_ns / NSEC_PER_USEC;
        chan23_pwm_seq_ind_values.channel_1 = PWM_USEC(ems_intensity_data.PWM23_DURATION) / NSEC_PER_USEC;
        chan23_values.p_individual = &chan23_pwm_seq_ind_values;
        chan23_sequence.values = chan23_values;
        
    } else {
        chan23_pwm_seq_ind_values.channel_0 = PWM_USEC(ems_intensity_data.PWM23_DURATION) / NSEC_PER_USEC;
        chan23_pwm_seq_ind_values.channel_1 = chan3_spec.pwm_on_time_ns / NSEC_PER_USEC;
        chan23_values.p_individual = &chan23_pwm_seq_ind_values;
        chan23_sequence.values = chan23_values;
        
    }

    uint16_t playback_count = ems_intensity_data.CHAN0_PLAYBACK;

    if (nrfx_pwm_simple_playback(&chan23_pwm_inst, &chan23_sequence, playback_count, NRFX_PWM_FLAG_STOP) == 0) {
        if (active_stimulating_chan == 2) {
            chan2_spec.status = 1;
        } else {
            chan3_spec.status = 1;
        }
        return 0;
    }
    return -EIO;
}

// Initialise channel 2 and 3 PWM
static int chan23_pwm_init() {

    chan2_spec.pwm_on_time_ns = PWM_USEC(ems_intensity_data.PWM23_ON_DURATION);
    chan3_spec.pwm_on_time_ns = PWM_USEC(ems_intensity_data.PWM23_ON_DURATION);

    nrfx_err_t err = NRFX_SUCCESS;
    
    nrfx_pwm_config_t chan23_conf = NRFX_PWM_DEFAULT_CONFIG(CHAN2_PWM_GPIO_PIN, CHAN3_PWM_GPIO_PIN, 
                                                            NRF_PWM_PIN_NOT_CONNECTED, NRF_PWM_PIN_NOT_CONNECTED);
                                                            
    chan23_conf.top_value = PWM_USEC(ems_intensity_data.PWM23_DURATION) / NSEC_PER_USEC;

    chan23_conf.load_mode = NRF_PWM_LOAD_INDIVIDUAL;

    chan23_sequence.values = chan23_values;

    nrfx_pwm_uninit(&chan23_pwm_inst);

    err = nrfx_pwm_init(&chan23_pwm_inst, &chan23_conf, chan23_pwm_event_handler, &active_stimulating_chan);


    if (err == NRFX_SUCCESS) {
        IRQ_DIRECT_CONNECT(PWM21_IRQn, 0, nrfx_pwm_21_irq_handler, 0);
        irq_enable(PWM21_IRQn);
       //LOG_INF("WORK DOEN BAHIJAAN");
        return 0;
    }

    LOG_ERR("PWM channels 2, 3 init fail (err %08x)", err);
    return -EIO;
}

// Update the channel parameters like on time, duration, interval 
static void update_chan_params() {
    if (k_mutex_lock(&update_mut, K_NO_WAIT)) {
        return;
    }

    if (chan_param_update_available & (1 << 0)) {
        chan0_spec.active_duration_ns = update_buf[0].active_duration_ns;
        chan0_spec.interval_ns = update_buf[0].interval_ns;
        chan_param_update_available &= ~(1 << 0);
        LOG_DBG("Chan 0 params updated");
    }

    if (chan_param_update_available & (1 << 1)) {
        chan1_spec.active_duration_ns = update_buf[1].active_duration_ns;
        chan1_spec.interval_ns = update_buf[1].interval_ns;
        chan1_spec.pwm_on_time_ns = update_buf[1].pwm_on_time_ns;
        chan_param_update_available &= ~(1 << 1);
        LOG_DBG("Chan 1 params updated");
    }

    // Update the channel 2 and 3 parameters
    if (chan_param_update_available & (1 << 2)) {
        chan2_spec.pwm_on_time_ns = update_buf[2].pwm_on_time_ns;
    }

    if (chan_param_update_available & (1 << 3)) {
        chan3_spec.pwm_on_time_ns = update_buf[3].pwm_on_time_ns;
    }

    k_mutex_unlock(&update_mut);
}

// Event handler for the PWM modes timer 
static void pwm_modes_timer_event_handler(nrf_timer_event_t event_type, void *p_context) {
    
    if (event_type == NRF_TIMER_EVENT_COMPARE0) {


        chan0_counter++;
        if (chan0_spec.status == 1) { // Inactive period
            // Time has expired
            if (chan0_counter >= (chan0_spec.interval_ns / NSEC_PER_MSEC)) {
                nrf_gpio_pin_clear(CHAN0_GPIO_PIN);
                chan0_spec.status = 0;
                chan0_counter = 0;

                chan1_counter_on = 0; // Reset chan 1 timer
                chan1_counter_off = 0;
                power_signal_counter = 0;
                
                // Update params
                update_chan_params();
                chan1_toggle_power_signal();
            }

        } else if (chan0_spec.status == 0) {
            if (chan1_spec.status == 1) {
                chan1_counter_on++;
                if (((PWM_MSEC(ems_intensity_data.PWM_DURATION) / NSEC_PER_MSEC) - chan1_counter_on) == ems_intensity_data.CHAN0_INDUCTOR) {
                    chan23_toggle();
                } else if (chan1_counter_on >= (PWM_MSEC(ems_intensity_data.PWM_DURATION) / NSEC_PER_MSEC)) {
                    chan1_toggle_power_signal();
                    chan1_counter_off = 0;
                    chan1_counter_on = 0;
                

                    //if (!pwm_stopped_check(&chan23_pwm_inst)) {
                        nrfx_pwm_stop(&chan23_pwm_inst, false);
                    
                }
            } else if (chan1_spec.status == 0) {
                chan1_counter_off++;
                if (chan1_counter_off >= (PWM_MSEC(ems_intensity_data.PWM_INTERVAL) / NSEC_PER_MSEC)) {
                    chan1_toggle_power_signal();
                    chan1_counter_off = 0;
                    chan1_counter_on = 0;
                    
                }
            }

            if (chan0_counter >= (chan0_spec.active_duration_ns / NSEC_PER_MSEC)) {
                nrf_gpio_pin_set(CHAN0_GPIO_PIN);
                chan0_counter = 0;
                chan0_spec.status = 1;

                if (!is_pwm_modes_enabled) {
                    // Disable timer after iteration is complete
                    nrfx_timer_disable(&pwm_modes_timer);
                }
            }
        }
    }
}


// Function to generate 5 simultaneous PWM spikes of 20% duty cycle on CHAN2 and CHAN3
int ems_pwm_generate_simultaneous_spikes_chan23(void) {
    // Define PWM values for 20% duty cycle
    const uint32_t period_ns = PWM_USEC(ems_intensity_data.PWM23_DURATION);
    const uint32_t on_time_ns = period_ns * 80 / 100; // 20% duty cycle

    // Configure both channels for simultaneous operation
    chan23_pwm_seq_ind_values.channel_0 = on_time_ns / NSEC_PER_USEC; // CHAN2 (mapped to channel_0)
    chan23_pwm_seq_ind_values.channel_1 = on_time_ns / NSEC_PER_USEC; // CHAN3 (mapped to channel_1)

    // Set up sequence values for both channels
    chan23_values.p_individual = &chan23_pwm_seq_ind_values;
    chan23_sequence.values = chan23_values;
    chan23_sequence.length = 4;  // Length matches the individual channel configuration
    chan23_sequence.repeats = 0; // No repeats for each value in the sequence

    // Set playback count to 5 for 5 spikes
    uint16_t playback_count = 5;

    // Trigger playback on CHAN23 for both channels
    if (nrfx_pwm_simple_playback(&chan23_pwm_inst, &chan23_sequence, playback_count, NRFX_PWM_FLAG_STOP) == 0) {
        chan2_spec.status = 1; // Update CHAN2 status
        chan3_spec.status = 1; // Update CHAN3 status
      //  LOG_INF("5 simultaneous PWM spikes of 20% duty cycle generated on CHAN23 (CHAN2 and CHAN3)");
        return 0;
    }
    LOG_ERR("Simultaneous PWM spikes generation on CHAN23 failed");
    return -EIO;
}

// Initialise timer

static int pwm_modes_timer_init() {
    LOG_INF("Init PWM modes timer");

 nrfx_err_t err;

    /* STEP 3.3 - Declaring timer config and intialize nrfx_timer instance. */
    nrfx_timer_config_t timer_config = NRFX_TIMER_DEFAULT_CONFIG(500000);
    err = nrfx_timer_init(&pwm_modes_timer, &timer_config, pwm_modes_timer_event_handler);
    if (err != NRFX_SUCCESS) {
        LOG_ERR("nrfx_timer_init error: %08x", err);
        return 0;
    }
        IRQ_DIRECT_CONNECT(TIMER21_IRQn, 0, nrfx_timer_21_irq_handler, 0);
        irq_enable(TIMER21_IRQn);

        return 0;
}
// Initialise the EMS PWM channels
int ems_pwm_init() {
    int ret = 0;

    chan0_gpio_init();

    ret = chan1_pwm_init();
    if (ret) {
        return ret;
    }

    update_power_signal_count();

    ret = chan23_pwm_init();
    if (ret) {
        return ret;
    }

    ret = pwm_modes_timer_init();
    if (ret) {
        return ret;
    } 

    return 0;
}

void chan23reset(){

   chan23_pwm_init();
}

void SleepMode(){

    LOG_INF("EMS enabled with relax part 1");

    ems_intensity_data.PWM_PERIOD = 64;
    ems_intensity_data.PWM_ON_TIME = 5;
    ems_intensity_data.PWM_INTERVAL = 10;
    ems_intensity_data.PWM_DURATION = 5;
    ems_intensity_data.CHAN0_PLAYBACK = 60;
    ems_intensity_data.CHAN0_INDUCTOR = 3;
    ems_intensity_data.PWM23_DURATION = 1000;
    ems_intensity_data.PWM23_ON_DURATION = 900;
    ems_intensity_data.CHAN0_DURATION = 2;
    ems_intensity_data.CHAN0_ON_DURATION = 20;
    chan0_para_update();
    chan23reset();
}

void RelaxMode(){

    LOG_INF("EMS enabled with sleep part 1");

    ems_intensity_data.PWM_PERIOD = 64;
    ems_intensity_data.PWM_ON_TIME = 5;
    ems_intensity_data.PWM_INTERVAL = 5;
    ems_intensity_data.PWM_DURATION = 5;
    ems_intensity_data.CHAN0_PLAYBACK = 10;
    ems_intensity_data.CHAN0_INDUCTOR = 3;
    ems_intensity_data.PWM23_DURATION = 1000;
    ems_intensity_data.PWM23_ON_DURATION = 900;
    ems_intensity_data.CHAN0_DURATION = 2;
    ems_intensity_data.CHAN0_ON_DURATION = 20;
    chan0_para_update();
    chan23reset();

}

void BreathMode(){

    LOG_INF("EMS enabled with sleep part 1");

    ems_intensity_data.PWM_PERIOD = 64;
    ems_intensity_data.PWM_ON_TIME = 5;
    ems_intensity_data.PWM_INTERVAL = 5;
    ems_intensity_data.PWM_DURATION = 5;
    ems_intensity_data.CHAN0_PLAYBACK = 10;
    ems_intensity_data.CHAN0_INDUCTOR = 3;
    ems_intensity_data.PWM23_DURATION = 1000;
    ems_intensity_data.PWM23_ON_DURATION = 900;
    ems_intensity_data.CHAN0_DURATION = 6;
    ems_intensity_data.CHAN0_ON_DURATION = 120;
    chan0_para_update();
    chan23reset();

}

// Function called to start and stop the EMS session
void ems_pwm_toggle(int state) {
    if (state != 0 && !is_pwm_modes_enabled) {
        is_pwm_modes_enabled = true;
      //int ret = ems_pwm_generate_simultaneous_spikes_chan23();
    //    for(int i =0; i<100000;i++){
    //     active_stimulating_chan =2;
    //    int err44 =  chan23_toggle();
    //     k_msleep(1);
    //     active_stimulating_chan =3;
    //    err44 =  chan23_toggle();
    //    k_msleep(1);
    //    }
      
        //ems_pwm_generate_spikes_chan23(3);
if (!nrfx_timer_is_enabled(&pwm_modes_timer)) {
    nrfx_timer_extended_compare(&pwm_modes_timer, NRF_TIMER_CC_CHANNEL0, 500, NRF_TIMER_SHORT_COMPARE0_CLEAR_MASK, true); // Enable interrupt!
    nrfx_timer_enable(&pwm_modes_timer);
    LOG_INF("PWM modes enabled");
}

       
    } else if (is_pwm_modes_enabled && state == 0) {
        is_pwm_modes_enabled = false;
        battery_update_ready = true;
        // Timer will be turned off in the timer callback. This is to allow the current power signal to complete
        LOG_INF("PWM modes disabled");
        nrf_gpio_pin_set(CHAN0_GPIO_PIN);
        // Trigger single playback on CHAN2
        //ems_pwm_single_playback_chan23(2);

         // Trigger single playback on CHAN3
        //ems_pwm_single_playback_chan23(3);
    }
}

// Update the PWM parameters for the EMS
int ems_pwm_update_params(uint8_t chan_number, uint64_t on_time_ns, uint64_t duration_ns, uint64_t interval_ns) {
    if (k_mutex_lock(&update_mut, K_MSEC(100))) {
        return -ETIMEDOUT;
    }

    switch (chan_number) {
        case 0: {
            memcpy(&update_buf[0], &chan0_spec, sizeof(chan0_spec));
            struct pwm_mode_chan_spec *temp = &update_buf[0];
            temp->active_duration_ns = (duration_ns > 0) ? duration_ns : temp->active_duration_ns;

            if (on_time_ns > 0) {
                temp->interval_ns = on_time_ns;
            } else if (interval_ns > 0) {
                temp->interval_ns = interval_ns;
            }

            chan_param_update_available |= (1 << 0);
            LOG_DBG("Chan 0 update, on_time %llu, interval %llu", temp->active_duration_ns, temp->interval_ns);
            break;
        }
        case 1: {
            memcpy(&update_buf[1], &chan1_spec, sizeof(chan1_spec));
            struct pwm_mode_chan_spec *temp = &update_buf[1];

            if (on_time_ns >= PWM_USEC(ems_intensity_data.PWM_PERIOD) || (interval_ns + duration_ns) > chan0_spec.active_duration_ns) {
                LOG_ERR("Parameters out of range");
                break;
            }

            temp->pwm_on_time_ns = (on_time_ns > 0) ? on_time_ns : temp->active_duration_ns;
            temp->interval_ns = (interval_ns > 0) ? interval_ns : temp->interval_ns;
            temp->active_duration_ns = (duration_ns > 0) ? duration_ns : temp->active_duration_ns;

            chan_param_update_available |= (1 << 1);
            LOG_DBG("Chan 1 update, on_time %llu, interval %llu", temp->active_duration_ns, temp->interval_ns);
            break;
        }
        case 2: {
            memcpy(&update_buf[2], &chan2_spec, sizeof(chan2_spec));
            struct pwm_mode_chan_spec *temp = &update_buf[2];

            if (on_time_ns > PWM_USEC(ems_intensity_data.PWM23_DURATION)) {
                LOG_ERR("Parameter out of range");
                break;
            }

            temp->pwm_on_time_ns = (uint64_t)(((float)on_time_ns * PWM_USEC(ems_intensity_data.PWM23_DURATION)) / 100.0f);
            chan_param_update_available |= (1 << 2);
            break;
        }
        case 3: {
            memcpy(&update_buf[3], &chan3_spec, sizeof(chan3_spec));
            struct pwm_mode_chan_spec *temp = &update_buf[3];

            if (on_time_ns > PWM_USEC(ems_intensity_data.PWM23_DURATION)) {
                LOG_ERR("Parameter out of range");
                break;
            }

            temp->pwm_on_time_ns = (uint64_t)(((float)on_time_ns * PWM_USEC(ems_intensity_data.PWM23_DURATION)) / 100.0f);
            chan_param_update_available |= (1 << 3);
            break;
        }
        default: {
            break;
        }
    }
    k_mutex_unlock(&update_mut);
    return 0;
}