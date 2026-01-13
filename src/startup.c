#include <zephyr/kernel.h>
#include <zephyr/logging/log.h>
#include <zephyr/drivers/gpio.h>
#include <zephyr/drivers/pwm.h>
#include <hal/nrf_gpio.h>
#include <zephyr/drivers/adc.h>
#include <zephyr/pm/pm.h>

#include "startup.h"
#include "ems_engine.h"
#include "core_types.h"
#include "io_adapter.h"
#include "watchdog_heartbeat.h"

LOG_MODULE_REGISTER(MAIN, LOG_LEVEL_DBG);

#define BLE_CONNECTION_STATE_NO_CONNECTION   -1
#define BLE_CONNECTION_STATE_DISCONNECTED     0
#define BLE_CONNECTION_STATE_CONNECTED        1
#define NUM_STEPS                             50U
#define SLEEP_MSEC                            25U
#define SLEEP_TIME_MS                         1000
#define ADC_CHANNEL_1                         1

#define GPIO_PIN                              NRF_GPIO_PIN_MAP(0, 5)
#define GPIO_PIN1                             NRF_GPIO_PIN_MAP(0, 25)
#define DEFAULT_SESSION_TIME_SECONDS          1200

#if !DT_NODE_EXISTS(DT_PATH(zephyr_user)) || \
    !DT_NODE_HAS_PROP(DT_PATH(zephyr_user), io_channels)
#error "No suitable devicetree overlay specified"
#endif

#define DT_SPEC_AND_COMMA(node_id, prop, idx) \
    ADC_DT_SPEC_GET_BY_IDX(node_id, idx),

// Get the ADC channels from the devicetree
const struct adc_dt_spec adc_channels[] = {
    DT_FOREACH_PROP_ELEM(DT_PATH(zephyr_user), io_channels,
    DT_SPEC_AND_COMMA)
};

static void session_timer_exp_cb(struct k_timer *timer);

static void adjust_pwm_timer_exp_cb(struct k_timer *timer);

uint32_t standby_counter;
volatile bool ems_session_running = false;
bool in_standby = false;
static int increment;

int8_t ble_connection_state = BLE_CONNECTION_STATE_NO_CONNECTION;

extern struct k_msgq ble_msgq;

struct main_msg_data data;

struct ble_msg *temp_msg = &data.data.ble;

K_MSGQ_DEFINE(main_msgq, sizeof(struct main_msg_data), 5, 4);

K_TIMER_DEFINE(session_timer, session_timer_exp_cb, NULL); // Timer for the session timer callback
K_TIMER_DEFINE(adjust_pwm_timer, adjust_pwm_timer_exp_cb, NULL);


// Struct for storing the EMS parameters like on-time, off-time, duty cycle, etc.
struct ems_def current_ems = {
    .status = {
        .control = 0,
        .session = {0},
    },
    .channels = {
        .chan0 = {.on_time = 450, .off_time = 1910},
        .chan1 = {.on_time = (6.25 * NSEC_PER_USEC), .interval = (50 * USEC_PER_MSEC)},
        .chan2 = {.duty_cycle = 50},
        .chan3 = {.duty_cycle = 50}
    }
};

// Function to update the BLE message queue
static void update_ble(struct ble_msg *msg) {
    k_msgq_put(&ble_msgq, msg, K_NO_WAIT);
}

// Timer function to turn off the EMS after the user-specified time
static void session_timer_exp_cb(struct k_timer *timer) {
    struct ble_msg control_session_msg = {0};
    if (disconnect_reason == 19) { // If user disconnected the device manually, then stop the EMS
        current_ems.status.session.current_session_len = 0;
        current_ems.status.control = 0;
        LOG_INF("EMS disabled");
        ems_pwm_toggle(0);
        ems_session_running = false;
        LOG_DBG("Function called to stop EMS");
        disconnect_reason = 0;
    }

    if (current_ems.status.control == 1) {
        current_ems.status.session.current_session_len++;
        LOG_DBG("EMS session %u, target %u", current_ems.status.session.current_session_len, current_ems.status.session.target_session_len);

        // If the session length is greater than the target session length, then turn off the EMS
        if ((current_ems.status.session.target_session_len > 0) &&
            (current_ems.status.session.current_session_len > current_ems.status.session.target_session_len)) {
            current_ems.status.control = 0;
            LOG_DBG("End EMS Session");
           // stop_green_led_thread();
            //start_green_led_thread(1000000);
            ems_session_running = false;
            ems_pwm_toggle(0);
        }
    }

    control_session_msg.id = BLE_MSG_ID_EMS_CONTROL;
    memcpy(&control_session_msg.data.ems, &current_ems, sizeof(current_ems)); // Copy the EMS parameters to the BLE message
    update_ble(&control_session_msg); // Update the BLE message queue

    //IF THE DEVICE IS NOT CONNECTED THEN INCREMENT THE STANDBY COUNTER
    if(ble_connection_state != BLE_CONNECTION_STATE_CONNECTED){
        standby_counter++;
            //LOG_INF("STANDBY %u", standby_counter);
    }
    //PUTS DEVICE TO SLEEP IF NO DEVICE CONNECTED FOR 5 MINUTES
     if(ble_connection_state != BLE_CONNECTION_STATE_CONNECTED && standby_counter > 300 && ems_session_running == false ){
    
            LOG_INF("Enter standby mode");
            nrf_gpio_pin_clear(GPIO_PIN);
            nrf_gpio_pin_clear(GPIO_PIN1);
    
    }
}

// Calculates the step size for INCREASING the on-time
static int on_time_increment_func() {
    uint32_t difference = temp_msg->data.ems.status.ontime - ems_intensity_data.PWM_ON_TIME;
    if (difference <= 10) {
        return 1;
    } else if (difference > 10 && difference <= 25) {
        return 3;
    } else if (difference > 25) {
        return 5;
    }
    return 0; // Should not be reached if called correctly
}

// Calculates the step size for DECREASING the on-time
static int on_time_decrement_func() {
    uint32_t difference = ems_intensity_data.PWM_ON_TIME - temp_msg->data.ems.status.ontime;
    if (difference <= 10) {
        return 1;
    } else if (difference > 10 && difference <= 25) {
        return 3;
    } else if (difference > 25) {
        return 5;
    }
    return 0; // Should not be reached if called correctly
}

// Function to gradually change the PWM_ON_TIME (handles both increase and decrease)
static void adjust_pwm_on_time() {
    // This static variable will hold the step value (positive or negative)
    // and retain it between timer callbacks for a single adjustment operation.
    static int step_value = 0;

    // If step_value is 0, a new adjustment has started. Calculate the direction and step size.
    if (step_value == 0) {
        // Case 1: Target is HIGHER than current -> We need to INCREASE
        if (ems_intensity_data.PWM_ON_TIME < temp_msg->data.ems.status.ontime) {
            step_value = on_time_increment_func();
        }
        // Case 2: Target is LOWER than current -> We need to DECREASE
        else if (ems_intensity_data.PWM_ON_TIME > temp_msg->data.ems.status.ontime) {
            // Get the step size and make it negative for subtraction
            step_value = -on_time_decrement_func();
        }
        // Case 3: Target is already met (or no change needed)
        else {
            k_timer_stop(&adjust_pwm_timer);
            return;
        }
    }

    // Apply the step (either adds or subtracts based on the sign of step_value)
    ems_intensity_data.PWM_ON_TIME += step_value;

    // Check if the target has been reached or passed
    bool target_reached = false;
    if (step_value > 0 && ems_intensity_data.PWM_ON_TIME >= temp_msg->data.ems.status.ontime) {
        // If increasing, stop when current is >= target
        target_reached = true;
    } else if (step_value < 0 && ems_intensity_data.PWM_ON_TIME <= temp_msg->data.ems.status.ontime) {
        // If decreasing, stop when current is <= target
        target_reached = true;
    }

    // If the target is reached, finalize the value and stop the timer
    if (target_reached) {
        step_value = 0; // Reset for the next command
        k_timer_stop(&adjust_pwm_timer);
        // Set the value exactly to the target to prevent overshooting
        ems_intensity_data.PWM_ON_TIME = temp_msg->data.ems.status.ontime;
    }

    // Enforce boundaries for the PWM value
    if (ems_intensity_data.PWM_ON_TIME > 100) {
        ems_intensity_data.PWM_ON_TIME = 100; // Cap at 100
    }
    // Since PWM_ON_TIME is likely unsigned, a check for < 0 is not needed,
    // but if it were a signed type, you would add:
    if (ems_intensity_data.PWM_ON_TIME < 0) {
        ems_intensity_data.PWM_ON_TIME = 0;
    }

    // Update the actual PWM hardware with the new value
    ems_pwm_update_params(1, PWM_USEC(ems_intensity_data.PWM_ON_TIME), 0, current_ems.channels.chan1.interval * NSEC_PER_USEC);
}

// Timer function to adjust PWM_ON_TIME every 20 seconds
static void adjust_pwm_timer_exp_cb(struct k_timer *timer) {
    adjust_pwm_on_time();
}

// Function to turn EMS on and off
static void ems_control_cmd_handle(uint8_t control) {
    if (control) {
        // Enable EMS
        initial_value = batt_val_mv;
        current_ems.status.session.current_session_len = 0;
        current_ems.status.control = 1;
        ems_pwm_toggle(1);
        //stop_green_led_thread();
        //start_green_led_thread(10000);
        LOG_INF("EMS enabled");
        current_ems.status.session.target_session_len = DEFAULT_SESSION_TIME_SECONDS; // Turn off EMS automatically after 20 minutes
        ems_session_running = true;
    } 
    else {
        current_ems.status.session.current_session_len = 0;
        current_ems.status.control = 0;
        LOG_INF("EMS disabled");
        ems_pwm_toggle(0);
        //stop_green_led_thread();
        //start_green_led_thread(1000000);
        ems_session_running = false;
    }
}

// Function to update the EMS parameters included in the EMS service 
static void ems_chan_cmd_handle(uint8_t channel, struct pwm_channel_data *chan_data) {
    switch (channel) {
        case BLE_MSG_ID_EMS_CHAN1_CONTROL: {
            ems_pwm_update_params(0, chan_data->chan0.on_time * NSEC_PER_MSEC, chan_data->chan0.off_time * NSEC_PER_MSEC, 0);
            memcpy(&current_ems.channels.chan0, &chan_data->chan0, sizeof(current_ems.channels.chan0));
            LOG_DBG("Chan0 update on_time: %u, off_time: %u", current_ems.channels.chan0.on_time, current_ems.channels.chan0.off_time);
            break;
        }
        case BLE_MSG_ID_EMS_CHAN2_CONTROL: {
            ems_pwm_update_params(1, chan_data->chan1.on_time, 0, chan_data->chan1.interval * NSEC_PER_USEC);
            memcpy(&current_ems.channels.chan1, &chan_data->chan1, sizeof(current_ems.channels.chan1));
            LOG_DBG("Chan1 update on_time: %u, interval: %u", current_ems.channels.chan1.on_time, current_ems.channels.chan1.interval);
            break;
        }
        case BLE_MSG_ID_EMS_CHAN3_CONTROL: {
            ems_pwm_update_params(2, chan_data->chan2.duty_cycle, 0, 0);
            memcpy(&current_ems.channels.chan2, &chan_data->chan2, sizeof(current_ems.channels.chan2));
            LOG_DBG("Chan2 update duty_cycle: %d", current_ems.channels.chan2.duty_cycle);
            break;
        }
        case BLE_MSG_ID_EMS_CHAN4_CONTROL: {
            ems_pwm_update_params(3, chan_data->chan3.duty_cycle, 0, 0);
            memcpy(&current_ems.channels.chan3, &chan_data->chan3, sizeof(current_ems.channels.chan3));
            LOG_DBG("Chan3 update duty_cycle: %d", current_ems.channels.chan3.duty_cycle);
            break;
        }
        default: {
            break;
        }
    }
}

int main(void) {

  register_thread(k_current_get());

    nrf_gpio_cfg_output(GPIO_PIN);
    nrf_gpio_cfg_output(GPIO_PIN1);

    nrf_gpio_pin_set(GPIO_PIN);
    nrf_gpio_pin_set(GPIO_PIN1);

    //LOG_INF("VALUE OF TEMP SENSOR %f",read_cpu_temp_sensor());
    ems_pwm_init(); // Initializes the PWM

    k_timer_start(&session_timer, K_SECONDS(1), K_SECONDS(1)); // Starts the timer


    while (1) {
        
       int ret = k_msgq_get(&main_msgq, &data, K_MSEC(100));

        heartbeat(); // Report healthy every loop
        
        if (ret == 0) {
        // If the data source is BLE, then handle the BLE messages
        if (data.src == MAIN_MSG_DATA_SRC_BLE) {
            // Switch case to handle the BLE messages
            switch (temp_msg->id) {
                case BLE_MSG_ID_EMS_CONTROL: {
                    if(temp_msg->data.ems.status.control == 1){
                        RelaxMode();
                    }
                    else if(temp_msg->data.ems.status.control == 2){
                        SleepMode();
                    }
                    else if(temp_msg->data.ems.status.control == 3){
                        BreathMode();
                    }
                    ems_control_cmd_handle(temp_msg->data.ems.status.control);
                    LOG_INF("EMS control CALLED");
                    break;
                }
                case BLE_MSG_ID_EMS_SESSION: {
                    current_ems.status.session.current_session_len = 0;
                    current_ems.status.session.target_session_len = temp_msg->data.ems.status.session.target_session_len; // uint32 big endian
                    break;
                }
                case BLE_MSG_ID_PWM_PERIOD: {
                    ems_intensity_data.PWM_PERIOD = temp_msg->data.ems.status.period;
                    break;
                }
                case BLE_MSG_ID_PWM_ONTIME: {
                    // Start the timer to adjust PWM_ON_TIME every 20 seconds
                    k_timer_start(&adjust_pwm_timer, K_SECONDS(2), K_SECONDS(2));
                    break;
                }
                case BLE_MSG_ID_PWM_INTERVAL: {
                    ems_intensity_data.PWM_INTERVAL = temp_msg->data.ems.status.interval;
                    break;
                }
                case BLE_MSG_ID_PWM_DURATION: {
                    ems_intensity_data.PWM_DURATION = temp_msg->data.ems.status.duration;
                    break;
                }
                case BLE_MSG_ID_CHAN0_PLAYBACK_COUNT: {
                    ems_intensity_data.CHAN0_PLAYBACK = temp_msg->data.ems.status.chan0playback;


                    break;
                }
                case BLE_MSG_ID_CHAN0_INUCT_DURATION: {
                    ems_intensity_data.CHAN0_INDUCTOR = temp_msg->data.ems.status.chan0inductor;

                    break;
                }
                 case BLE_MSG_ID_CHAN0_ON_DURATION: {
                    ems_intensity_data.CHAN0_DURATION = temp_msg->data.ems.status.chan0ontime;
                  chan0_para_update();

                    break;
                }
                case BLE_MSG_ID_CHAN0_DURATION: {
                    ems_intensity_data.CHAN0_ON_DURATION = temp_msg->data.ems.status.chan0time;
                    chan0_para_update();
                    break;
                }
                case BLE_MSG_ID_CHAN23_PWM_PERIOD_NS: {
                    ems_intensity_data.PWM23_DURATION = 25*(temp_msg->data.ems.status.pwm23time);
                    //CHAN23_PWM_DEFAULT_PERIOD_NS = temp_msg->data.ems.status.pwm23time;
                    //LOG_INF("VALUE OF CHAN 23 IN BLE STACK  %u", temp_msg->data.ems.status.pwm23time );
                    //LOG_INF("VALUE OF CHAN 23 %u", ems_intensity_data.PWM23_DURATION );
                    chan23reset();

                    break;
                }
                case BLE_MSG_ID_CHAN23_PWM_ON_TIME_NS: {
                    ems_intensity_data.PWM23_ON_DURATION = 25*(temp_msg->data.ems.status.pwm23ontime);
                    //CHAN23_PWM_DEFAULT_ON_TIME_NS= temp_msg->data.ems.status.pwm23ontime;
                    //LOG_INF("VALUE OF CHAN 23ONM in ble stack %u", temp_msg->data.ems.status.pwm23ontime);
                    //LOG_INF("VALUE OF CHAN 23ON %u", ems_intensity_data.PWM23_ON_DURATION );
                    chan23reset();
                    break;
                }
                case BLE_MSG_ID_CHARGER_ON_OFF: {
                    if(temp_msg->data.ems.status.chargeronoff == 5)
                    {
                         nrf_gpio_pin_clear(GPIO_PIN);
                         nrf_gpio_pin_clear(GPIO_PIN1);
                    }
                    break;
                }
                case BLE_MSG_ID_CONNECTED: {
                    ble_connection_state = BLE_CONNECTION_STATE_CONNECTED;
                    standby_counter = 0;
                    break;
                }
                case BLE_MSG_ID_DISCONNECTED: {
                    ble_connection_state = BLE_CONNECTION_STATE_DISCONNECTED;
                    standby_counter = 0;
                    LOG_DBG("BLE disconnected");
                    k_timer_stop(&adjust_pwm_timer);
                    break;
                }
                default: {
                    break;
                }
            }
        }
    }
    }
    return 0;
}



