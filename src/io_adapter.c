#include "io_adapter.h"
#include "bluetooth_manager.h"
#include "startup.h"
#include "ems_engine.h"
#include "watchdog_heartbeat.h"

#include <zephyr/drivers/pwm.h>
#include <zephyr/kernel.h>
#include <zephyr/drivers/gpio.h>
#include <zephyr/drivers/adc.h>
#include <zephyr/logging/log.h>
#include <zephyr/sys/reboot.h>
#include <hal/nrf_gpio.h>
#include <zephyr/bluetooth/bluetooth.h>
#include <zephyr/bluetooth/gatt.h>
#include <zephyr/bluetooth/uuid.h>
#include <zephyr/bluetooth/conn.h>
#include <zephyr/bluetooth/gap.h>
#include <zephyr/bluetooth/hci.h>

// Add NVS includes
#include <zephyr/device.h>
#include <zephyr/drivers/flash.h>
#include <zephyr/storage/flash_map.h>
#include <zephyr/fs/nvs.h>

#include <nrfx_grtc.h>

#include <inttypes.h>
#include <stdio.h>

#include <zephyr/device.h>
#include <zephyr/drivers/gpio.h>
#include <zephyr/drivers/hwinfo.h>
#include <zephyr/drivers/comparator.h>
#include <zephyr/kernel.h>
#include <zephyr/pm/device.h>
#include <zephyr/sys/poweroff.h>
#include <zephyr/sys/util.h>
#include <zephyr/drivers/timer/nrf_grtc_timer.h>

#include <zephyr/drivers/flash.h>
#include <zephyr/storage/flash_map.h>
#include <zephyr/fs/nvs.h>

#include <hal/nrf_grtc.h>
#include <haly/nrfy_grtc.h>

LOG_MODULE_REGISTER(APP_IO, LOG_LEVEL_DBG);

// NVS configuration
static struct nvs_fs fs;
#define NVS_PARTITION		storage_partition
#define NVS_PARTITION_DEVICE	FIXED_PARTITION_DEVICE(NVS_PARTITION)
#define NVS_PARTITION_OFFSET	FIXED_PARTITION_OFFSET(NVS_PARTITION)

// NVS IDs for storing data
#define TRANSITION_COUNTER_ID	1
#define HIGH_DURATION_ID		2
#define LOW_DURATION_ID			3
#define TOTAL_CYCLES_ID			4

#define BLUE_LED_OUT_NODE                   DT_ALIAS(blue_led)       // blue LED node
#define GREEN_LED_OUT_NODE                  DT_ALIAS(green_led) 
#define RED_LED_OUT_NODE                    DT_ALIAS(red_led)        // red LED node

#define SW0_NODE	                    DT_ALIAS(on_button)           // Button node

#define GPIO_PIN                        NRF_GPIO_PIN_MAP(0, 5)
#define GPIO_PIN1                       NRF_GPIO_PIN_MAP(0, 25)

#define STACK_SIZE                            512
#define MY_STACK_SIZE                         500
#define THREAD_PRIORITY                       4

#define PWM_PERIOD   PWM_MSEC(60)

#define PWM_MIN_DUTY_CYCLE 20000000
#define PWM_MAX_DUTY_CYCLE 50000000

#define ADC_THRESHOLD                   70  // Threshold for waking up based on ADC value difference

#define SLEEP_DURATION_MS               5000 // Duration of sleep in milliseconds
#define TIME_WINDOW_MS     10000  // 10-second time window
#define DEEP_SLEEP_TIME_S 2

// Sleep/wakeup timing constants
#define MONITORING_PERIOD_MS    10000   // 10 seconds monitoring period
#define SLEEP_CHECK_PERIOD_MS   20000   // 20 seconds sleep check period
#define POLL_INTERVAL_MS        50      // Polling interval for pin state

static const struct gpio_dt_spec sleep_wakeup_button  = GPIO_DT_SPEC_GET(DT_ALIAS(sleep_wakeup_button), gpios);

#if !DT_NODE_HAS_STATUS(SW0_NODE, okay)
#error "Unsupported board: sw0 devicetree alias is not defined"
#endif

// ADC spec macro
#define DT_SPEC_AND_COMMA(node_id, prop, idx) \
	ADC_DT_SPEC_GET_BY_IDX(node_id, idx),

struct gpio_dt_spec red_led_spec = GPIO_DT_SPEC_GET(RED_LED_OUT_NODE, gpios); // Red LED spec
struct gpio_dt_spec green_led_spec = GPIO_DT_SPEC_GET(GREEN_LED_OUT_NODE, gpios); // Green LED spec
struct gpio_dt_spec blue_led_spec = GPIO_DT_SPEC_GET(BLUE_LED_OUT_NODE, gpios); // Blue LED spec
const struct device *const cons = DEVICE_DT_GET(DT_CHOSEN(zephyr_console));

extern struct k_msgq ble_msgq;  // BLE message queue

// Define the thread stack
K_THREAD_STACK_DEFINE(dyn_thread_stack_1, MY_STACK_SIZE);
K_THREAD_STACK_DEFINE(dyn_thread_stack_2, MY_STACK_SIZE);
K_THREAD_STACK_DEFINE(dyn_thread_stack_3, MY_STACK_SIZE);
K_THREAD_STACK_DEFINE(sleep_wakeup_thread_stack, 1024);

// Define the thread control block
struct k_thread my_thread_data_1;
struct k_thread my_thread_data_2;
struct k_thread my_thread_data_3;
struct k_thread sleep_wakeup_thread_data;

/* Define the timer object */
static struct k_timer my_timer;

static struct gpio_callback button_cb_data;
static const struct gpio_dt_spec button = GPIO_DT_SPEC_GET_OR(SW0_NODE, gpios, {0}); // Button spec

// ADC channels
static const struct adc_dt_spec adc_channels[] = {
	DT_FOREACH_PROP_ELEM(DT_PATH(zephyr_user), io_channels, DT_SPEC_AND_COMMA)
};

// Thread definitions
#define LED_BLINK_THREAD_STACK_SIZE 1024
#define LED_BLINK_THREAD_PRIORITY 5

#define MIN_DUTY_CYCLE 0
#define MAX_DUTY_CYCLE 10000 // Maximum duty cycle in nanoseconds, adjust as needed
#define STEP_SIZE 100 // Step size for duty cycle increment/decrement, adjust for smoothness
#define STEP_DELAY_MS 10 // Delay between steps in milliseconds, adjust for speed of breathing effect
#define SOLID_BRIGHT_PERIOD 10000 // Set period for solid bright     // Maximum duty cycle for full brightness
#define ZERO_DUTY_CYCLE 0           // Duty cycle for turning off the LED
#define GRTC_FREQ_HZ 1000000

uint32_t btn_hold_counter = 0;
uint32_t ems_on = 0;
uint16_t raw_batt_val = 0;
int32_t batt_val_mv = 0;
int32_t initial_value = 0;
int32_t current_value = 0;
int32_t final_value = 0;
int charging_threshold;  // Charging threshold will be dynamically set
uint8_t charger_state = 0;   // Initialize the charger state
uint8_t battery_low = 0; 
uint16_t buf;
k_tid_t my_tid1;
k_tid_t my_tid2;
k_tid_t my_tid3;
k_tid_t sleep_wakeup_tid;
uint8_t sleep_flag = 0;
static uint64_t t_before_sleep = 0;


static int charge_count = 0;
static int charge_count1 = 0;
static int discharge = 0;

volatile bool in_critical_section = false;
extern bool in_standby;

// Sleep/wakeup state variables
static volatile bool system_in_sleep = false;
static volatile bool wakeup_requested = false;
static volatile uint32_t transition_counter = 0;
static volatile uint32_t high_duration_counter = 0;
static volatile uint32_t low_duration_counter = 0;
static uint32_t total_cycles = 0;  // Total monitoring cycles
double seconds;
K_SEM_DEFINE(button_sem, 0, 1);
K_SEM_DEFINE(wakeup_sem, 0, 1);

// Device availability flags
static bool red_led_available = false;
static bool green_led_available = false;
static bool blue_led_available = false;
static bool button_available = false;
static bool console_available = false;

void create_red_thread_from_function(void);
void create_green_thread_from_function(void);
void create_blue_thread_from_function(void);

// Battery ADC sequence
struct adc_sequence batt_read_sequence = {
    .buffer = &raw_batt_val,
    .buffer_size = sizeof(raw_batt_val)
};

// NVS initialization function
static int nvs_init(void)
{
    int rc = 0;
    struct flash_pages_info info;

    /* Define the nvs file system with settings_storage partition */
    fs.flash_device = NVS_PARTITION_DEVICE;
    if (!device_is_ready(fs.flash_device)) {
        LOG_ERR("Flash device %s is not ready", fs.flash_device->name);
        return -ENODEV;
    }
    
    fs.offset = NVS_PARTITION_OFFSET;
    rc = flash_get_page_info_by_offs(fs.flash_device, fs.offset, &info);
    if (rc) {
        LOG_ERR("Unable to get page info, rc=%d", rc);
        return rc;
    }
    
    fs.sector_size = info.size;
    fs.sector_count = 2U;  // Using 2 sectors for wear leveling

    rc = nvs_mount(&fs);
    if (rc) {
        LOG_ERR("Flash mount failed, rc=%d", rc);
        return rc;
    }

    LOG_INF("NVS initialized successfully");
    return 0;
}

// Function to save transition data to NVS
static int save_transition_data(void)
{
    int rc;
    
    // Save transition counter
    rc = nvs_write(&fs, TRANSITION_COUNTER_ID, &transition_counter, sizeof(transition_counter));
    if (rc < 0) {
        LOG_ERR("Failed to write transition counter, rc=%d", rc);
        return rc;
    }
    
    LOG_INF("Transition data saved to NVS");
    return 0;
}

// Function to load transition data from NVS
static int load_transition_data(void)
{
    int rc;
    uint32_t temp_val;
    
    // Load transition counter
    rc = nvs_read(&fs, TRANSITION_COUNTER_ID, &temp_val, sizeof(temp_val));
    if (rc > 0) {
        transition_counter = temp_val;
        LOG_INF("Loaded transition counter: %d", transition_counter);
    } else {
        LOG_INF("No transition counter found in NVS");
    }
    
    
    return 0;
}

/* Callback function for the timer */
void timer_expiry_function(struct k_timer *timer_id)
{
    /* Optional: If you want to restart the process for another 30 seconds, restart the timer */
    k_timer_start(&my_timer, K_SECONDS(30), K_NO_WAIT);
}

// Button pressed callback function
void button_pressed(const struct device *dev, struct gpio_callback *cb, uint32_t pins) {
    k_sem_give(&button_sem);
	LOG_DBG("Button pressed at %" PRIu32 "\n", k_cycle_get_32());
}



 

static void red_led_main() {
    while (1) {
        if (red_led_available) {
            gpio_pin_toggle_dt(&red_led_spec);
        }
        k_sleep(K_MSEC(1000));
    }
}

static void green_led_main() {
    while (1) {
        if (green_led_available) {
            gpio_pin_toggle_dt(&green_led_spec);
        }
        k_sleep(K_MSEC(1000));
    }
}

static void blue_led_main() {
    while (1) {
        if (blue_led_available) {
            gpio_pin_toggle_dt(&blue_led_spec);
        }
        k_sleep(K_MSEC(1000));
    }
}

int input_main() {

    register_thread(k_current_get());

    gpio_pin_interrupt_configure_dt(&sleep_wakeup_button, GPIO_INT_DISABLE);

   
    
    int err = 0;
    int ret;
    int val;
    int btn_hold_counter = 0;
    bool pattern_changed = false; // Flag to track if LED pattern is already changed
    const int hold_duration_threshold = 2000; // 2 seconds in milliseconds

    int rc;
	const struct device *const cons = DEVICE_DT_GET(DT_CHOSEN(zephyr_console));

    create_red_thread_from_function();
    create_green_thread_from_function();
    create_blue_thread_from_function();

    // Initialize NVS
    ret = nvs_init();
    if (ret) {
        LOG_ERR("NVS initialization failed, rc=%d", ret);
        // Continue without NVS - data won't be persistent
    }

    // Initialize the timer
    k_timer_init(&my_timer, timer_expiry_function, NULL);
    k_timer_start(&my_timer, K_SECONDS(30), K_NO_WAIT);

    console_available = device_is_ready(cons);
    if (!console_available) {
		LOG_ERR("%s: device not ready - continuing without console", cons->name);
	} else {
		LOG_INF("Console device ready");
	}

    // Button initialization
    button_available = false;
    if (!gpio_is_ready_dt(&button)) {
        LOG_WRN("Error: button device %s is not ready - button functionality disabled", button.port->name);
    } else {
		ret = gpio_pin_configure_dt(&button, GPIO_INPUT);

		if (ret) {
			LOG_WRN("Error %d: failed to configure %s pin %d - button functionality disabled", ret, button.port->name, button.pin);
		} else {
			button_available = true;
			LOG_INF("Button configured successfully");
		}
	}

    // Configure the sleep/wakeup GPIO pin as input
    ret = gpio_pin_configure_dt(&sleep_wakeup_button, GPIO_INPUT);
    if (ret < 0) {
        LOG_ERR("Sleep/wakeup GPIO pin config failed: %d - continuing anyway", ret);
    } else {
		LOG_INF("Sleep/wakeup button configured successfully");
	}

    // Button callback - only if button is available
    if (button_available) {
		gpio_init_callback(&button_cb_data, button_pressed, BIT(button.pin));
		gpio_add_callback(button.port, &button_cb_data);
		LOG_INF("Button callback registered");
	}

    k_sleep(K_MSEC(100));

    initial_value = batt_val_mv;
    printk("Initial value: %d\n", initial_value);

	red_led_available = false;
   	if (!gpio_is_ready_dt(&red_led_spec)) {
		LOG_WRN("Red LED device not ready - red LED disabled");
	} else {
		ret = gpio_pin_configure_dt(&red_led_spec, GPIO_OUTPUT_INACTIVE);
		if (ret < 0) {
			LOG_WRN("Red LED configure failed: %d - red LED disabled", ret);
		} else {
			red_led_available = true;
			LOG_INF("Red LED configured successfully");
		}
	}

	green_led_available = false;
    if (!gpio_is_ready_dt(&green_led_spec)) {
		LOG_WRN("Green LED device not ready - green LED disabled");
	} else {
		ret = gpio_pin_configure_dt(&green_led_spec, GPIO_OUTPUT_INACTIVE);
		if (ret < 0) {
			LOG_WRN("Green LED configure failed: %d - green LED disabled", ret);
		} else {
			green_led_available = true;
			LOG_INF("Green LED configured successfully");
		}
	}

	blue_led_available = false;
    if (!gpio_is_ready_dt(&blue_led_spec)) {
		LOG_WRN("Blue LED device not ready - blue LED disabled");
	} else {
		ret = gpio_pin_configure_dt(&blue_led_spec, GPIO_OUTPUT_INACTIVE);
		if (ret < 0) {
			LOG_WRN("Blue LED configure failed: %d - blue LED disabled", ret);
		} else {
			blue_led_available = true;
			LOG_INF("Blue LED configured successfully");
		}
	}

    // Simulate some other operations
    k_sleep(K_SECONDS(1));

	// Log initialization summary
	LOG_INF("=== IO Adapter Initialization Summary ===");
	LOG_INF("Console: %s", console_available ? "OK" : "DISABLED");
	LOG_INF("Button: %s", button_available ? "OK" : "DISABLED");
	LOG_INF("Red LED: %s", red_led_available ? "OK" : "DISABLED");
	LOG_INF("Green LED: %s", green_led_available ? "OK" : "DISABLED");
	LOG_INF("Blue LED: %s", blue_led_available ? "OK" : "DISABLED");
	LOG_INF("========================================");

     int uy = nrfx_grtc_init(8);
    LOG_INF("GRTC INIT %d",uy);


    uint64_t ticks = 0;
    nrfx_grtc_syscounter_get(&ticks);
    seconds = (double)ticks / GRTC_FREQ_HZ;
    //LOG_INF("GRTC TICKS %f",seconds);
    // Main loop
    while (1) {

        heartbeat();

        // Check battery value
        if (batt_val_mv < 1600 ) {
            if(battery_low == 0){
                if (red_led_available) k_thread_suspend(my_tid2);
                if (green_led_available) k_thread_suspend(my_tid3);
                if (blue_led_available) k_thread_start(my_tid1);
                battery_low=1;
            }
        }

        // Get button state - only if button is available
        if (button_available) {
			val = gpio_pin_get_dt(&button);
		} else {
			val = 0;  // Default to not pressed
		}

        k_msleep(1);  // Sleep to avoid busy waiting

        // Button press handling
        if (val == 1 && button_available) {

            // rc = pm_device_action_run(cons, PM_DEVICE_ACTION_SUSPEND);
            // if (rc < 0) {
            //     LOG_ERR("Could not suspend console (%d)\n", rc);
            //     return 0;
            // }

            // hwinfo_clear_reset_cause();
            // sys_poweroff();
            btn_hold_counter++;  // Increment counter every ms while the button is held

            // If button has been held for more than 3 seconds, change the LED pattern
            if (btn_hold_counter >= hold_duration_threshold && !pattern_changed && pairing_on) {

                if(battery_low == 0){
                    k_thread_start(my_tid3);
                }
                
                LOG_INF("Button held for 3 seconds, changed to blinking");
                pattern_changed = true; // Set flag to indicate the pattern has changed

                bt_adv_restart_init();
                
                // if ((err = bt_le_adv_stop()) == 0) {
                //     LOG_INF("Advertising stopped successfully");
                // }
                // else {
                //     LOG_INF("Cannot stop advertising, err = %d", err);
                // }

                // if ((err = bt_le_filter_accept_list_clear()) == 0) {
                //     LOG_INF("Accept list cleared successfully");

                //     ble_new_adv();

                //     if ((err = bt_le_adv_start(BT_LE_ADV_CONN_NAME, NULL, 0, NULL, 0)) == 0) {
                //         LOG_INF("Advertising in pairing mode started");
                //     } else {
                //         LOG_INF("Cannot start advertising, err = %d", err);
                //     }
                // }
                // else {
                //     LOG_INF("Cannot clear accept list, err = %d", err);
                // }
            }
        }
        else {
            // Reset the counter and pattern_changed flag when the button is released
            btn_hold_counter = 0;
            pattern_changed = false;
        }

        // Handle longer button hold (e.g., reboot) if needed
        if (btn_hold_counter > 5000) {
            LOG_INF("Button held for more than 9 seconds, rebooting");
            nrf_gpio_pin_clear(GPIO_PIN);
            nrf_gpio_pin_clear(GPIO_PIN1);
        }
    }

    return 0;  // Return success
}

K_THREAD_DEFINE(input_thread, 2048, input_main, NULL, NULL, NULL, 2, K_ESSENTIAL, 0);
//K_THREAD_DEFINE(batt_thread, 512, batt_read_update, NULL, NULL, NULL, 3, 0, 0);

void create_red_thread_from_function(void) {
    my_tid1 = k_thread_create(&my_thread_data_1, dyn_thread_stack_1,
                             K_THREAD_STACK_SIZEOF(dyn_thread_stack_1),
                             red_led_main,
                             NULL, NULL, NULL,
                             4, 0, K_FOREVER);
}

void create_green_thread_from_function(void) {
    my_tid2 = k_thread_create(&my_thread_data_2, dyn_thread_stack_2,
                             K_THREAD_STACK_SIZEOF(dyn_thread_stack_2),
                             green_led_main,
                             NULL, NULL, NULL,
                             5, 0, K_FOREVER);
}

void create_blue_thread_from_function(void) {
    my_tid3 = k_thread_create(&my_thread_data_3, dyn_thread_stack_3,
                             K_THREAD_STACK_SIZEOF(dyn_thread_stack_3),
                             blue_led_main,
                             NULL, NULL, NULL,
                             6, 0, K_FOREVER);
}