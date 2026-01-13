/*
 * Copyright (c) 2023 Nordic Semiconductor ASA
 * SPDX-License-Identifier: LicenseRef-Nordic-5-Clause
 */

#include <stdlib.h>

#include <zephyr/kernel.h>
#include <zephyr/device.h>
#include <zephyr/drivers/gpio.h>
#include <zephyr/drivers/mfd/npm1300.h>
#include <zephyr/drivers/sensor.h>
#include <zephyr/sys/printk.h>
#include <zephyr/pm/device.h>
#include <zephyr/sys/poweroff.h>
#include <zephyr/drivers/hwinfo.h>
#include <zephyr/logging/log.h>

#include "fuel_gauge.h"

// Forward declaration for prepare_for_sleep from bluetooth_manager
extern void prepare_for_sleep(void);

LOG_MODULE_REGISTER(NPM1300, LOG_LEVEL_DBG);

#define SLEEP_TIME_MS 30000
#define VBUS_SLEEP_CHECK_MS 5000  // 5 seconds to check if VBUS stays connected
#define POLL_INTERVAL_MS 100      // Polling interval

static const struct device *pmic = DEVICE_DT_GET(DT_NODELABEL(npm1300_ek_pmic));
static const struct device *charger = DEVICE_DT_GET(DT_NODELABEL(npm1300_ek_charger));
static const struct device *cons = DEVICE_DT_GET(DT_CHOSEN(zephyr_console));

// Sleep/wakeup state variables
static volatile bool vbus_connected;
static volatile bool system_in_sleep = false;
static volatile bool wakeup_requested = false;

// Semaphore for wakeup
K_SEM_DEFINE(vbus_wakeup_sem, 0, 1);

// GPIO spec for PMIC host interrupt pin (from devicetree)
// This is the pin that the PMIC uses to signal events (GPIO1 pin 6)
static const struct gpio_dt_spec pmic_int_gpio = GPIO_DT_SPEC_GET(DT_NODELABEL(npm1300_ek_pmic), host_int_gpios);

// Timer for sleep monitoring
static struct k_timer sleep_monitor_timer;

// Forward declaration of timer expiry function
static void sleep_monitor_timer_expiry(struct k_timer *timer_id);

// Timer expiry callback - called after 5 seconds of VBUS being HIGH
static void sleep_monitor_timer_expiry(struct k_timer *timer_id)
{
	// Check if VBUS is still connected when timer expires
	if (vbus_connected && !system_in_sleep) {
		LOG_INF("Timer expired: VBUS still HIGH for 5 seconds, entering sleep mode");

		// Prepare for sleep
		prepare_for_sleep();

		// Configure PMIC host interrupt GPIO for wakeup on HIGH level
		if (gpio_is_ready_dt(&pmic_int_gpio)) {
			gpio_pin_interrupt_configure_dt(&pmic_int_gpio, GPIO_INT_LEVEL_HIGH);
			LOG_INF("PMIC interrupt GPIO configured for wakeup (level HIGH on P1.06)");
		} else {
			LOG_ERR("PMIC interrupt GPIO not ready for wakeup config!");
		}

		// Set sleep flag
		system_in_sleep = true;
		wakeup_requested = false;

		LOG_INF("System entering sleep mode, will wake on PMIC interrupt (VBUS detect)");

		// Suspend console before sleep
		int rc = pm_device_action_run(cons, PM_DEVICE_ACTION_SUSPEND);
		if (rc < 0) {
			LOG_ERR("Could not suspend console (%d)", rc);
		}

		// Clear reset cause and enter power-off (deep sleep)
		hwinfo_clear_reset_cause();
		sys_poweroff();
	} else if (!vbus_connected) {
		LOG_INF("Timer expired: VBUS went LOW, sleep cancelled");
	}
}

// PMIC interrupt GPIO callback - used for wakeup from sleep
static void pmic_int_wakeup_handler(const struct device *dev, struct gpio_callback *cb, uint32_t pins)
{
	if (system_in_sleep) {
		LOG_INF("System wakeup triggered by PMIC interrupt");
		wakeup_requested = true;
		k_sem_give(&vbus_wakeup_sem);
	}
}

static void event_callback(const struct device *dev, struct gpio_callback *cb, uint32_t pins)
{
	if (pins & BIT(NPM1300_EVENT_VBUS_DETECTED)) {
		printk("Vbus connected\n");
		vbus_connected = true;

		// If system is in sleep, trigger wakeup
		if (system_in_sleep) {
			LOG_INF("Wakeup requested - VBUS detected");
			wakeup_requested = true;
			k_sem_give(&vbus_wakeup_sem);
			return;
		}

		// Start 5-second timer to monitor VBUS
		LOG_INF("VBUS detected, starting %d second timer", VBUS_SLEEP_CHECK_MS / 1000);
		k_timer_start(&sleep_monitor_timer, K_MSEC(VBUS_SLEEP_CHECK_MS), K_NO_WAIT);
	}

	if (pins & BIT(NPM1300_EVENT_VBUS_REMOVED)) {
		printk("Vbus removed\n");
		vbus_connected = false;

		// Stop the timer if VBUS goes LOW
		k_timer_stop(&sleep_monitor_timer);
		LOG_INF("VBUS removed, timer stopped - sleep cancelled");
	}
}

static void npm1300_thread_main1(void)
{
	int err;
	bool pmic_available = false;
	bool charger_available = false;
	bool fuel_gauge_available = false;

	if (!device_is_ready(pmic)) {
		LOG_ERR("PMIC device not ready - continuing without PMIC functionality");
		pmic_available = false;
	} else {
		LOG_INF("PMIC device ready");
		pmic_available = true;
	}

	if (!device_is_ready(charger)) {
		LOG_ERR("Charger device not ready - continuing without charger functionality");
		charger_available = false;
	} else {
		LOG_INF("Charger device ready");
		charger_available = true;
	}

	if (!charger_available || fuel_gauge_init(charger) < 0) {
		LOG_ERR("Could not initialise fuel gauge - continuing without fuel gauge");
		fuel_gauge_available = false;
	} else {
		LOG_INF("Fuel gauge initialized successfully");
		fuel_gauge_available = true;
	}

	// Initialize the sleep monitor timer
	k_timer_init(&sleep_monitor_timer, sleep_monitor_timer_expiry, NULL);
	LOG_INF("Sleep monitor timer initialized");

	// Initialize PMIC host interrupt GPIO for wakeup (GPIO1 pin 6)
	if (pmic_available && gpio_is_ready_dt(&pmic_int_gpio)) {
		err = gpio_pin_configure_dt(&pmic_int_gpio, GPIO_INPUT);
		if (err < 0) {
			LOG_ERR("PMIC interrupt GPIO config failed: %d - continuing anyway", err);
		} else {
			LOG_INF("PMIC interrupt GPIO configured (P1.06)");

			// Initialize the wakeup callback for PMIC interrupt pin
			static struct gpio_callback pmic_int_wakeup_cb;
			gpio_init_callback(&pmic_int_wakeup_cb, pmic_int_wakeup_handler,
					   BIT(pmic_int_gpio.pin));
			gpio_add_callback(pmic_int_gpio.port, &pmic_int_wakeup_cb);

			// Disable interrupt initially (will be enabled before sleep)
			gpio_pin_interrupt_configure_dt(&pmic_int_gpio, GPIO_INT_DISABLE);
			LOG_INF("PMIC interrupt wakeup callback registered");
		}
	} else {
		LOG_ERR("PMIC interrupt GPIO not ready - sleep/wake functionality disabled");
	}

	if (pmic_available) {
		static struct gpio_callback event_cb;

		gpio_init_callback(&event_cb, event_callback,
				   BIT(NPM1300_EVENT_VBUS_DETECTED) |
				   BIT(NPM1300_EVENT_VBUS_REMOVED));

		err = mfd_npm1300_add_callback(pmic, &event_cb);
		if (err) {
			LOG_ERR("Failed to add pmic callback - VBUS detection disabled");
		} else {
			LOG_INF("PMIC event callback registered successfully");
		}
	}

	/* Initialise vbus detection status. */
	if (charger_available) {
		struct sensor_value val;
		int ret = sensor_attr_get(charger, SENSOR_CHAN_CURRENT, SENSOR_ATTR_UPPER_THRESH, &val);

		if (ret < 0) {
			LOG_ERR("Could not get VBUS status - assuming disconnected");
			vbus_connected = false;
		} else {
			vbus_connected = (val.val1 != 0) || (val.val2 != 0);
			LOG_INF("Initial VBUS status: %s", vbus_connected ? "connected" : "disconnected");
		}
	} else {
		LOG_INF("Charger not available - VBUS detection disabled");
		vbus_connected = false;
	}

	LOG_INF("NPM1300 initialization complete (PMIC: %s, Charger: %s, Fuel Gauge: %s)",
		pmic_available ? "OK" : "FAILED",
		charger_available ? "OK" : "FAILED",
		fuel_gauge_available ? "OK" : "FAILED");

	// Main loop - just update fuel gauge periodically
	// Sleep logic is now handled in event_callback when VBUS is detected
	while (1) {
		if (fuel_gauge_available) {
			fuel_gauge_update(charger, vbus_connected);
		}
		k_msleep(SLEEP_TIME_MS);
	}
}

K_THREAD_DEFINE(npm_thread1, 2048, npm1300_thread_main1, NULL, NULL, NULL, 4, 0, 0);
