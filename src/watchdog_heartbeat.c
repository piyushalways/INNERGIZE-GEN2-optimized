/*
 * Copyright (c) 2015 Intel Corporation
 * Copyright (c) 2018 Nordic Semiconductor
 * Copyright (c) 2019 Centaur Analytics, Inc
 * Copyright 2023 NXP
 *
 * SPDX-License-Identifier: Apache-2.0
 */

#include <zephyr/kernel.h>
#include <zephyr/device.h>
#include <zephyr/drivers/watchdog.h>
#include <stdbool.h>
#include <zephyr/logging/log.h>

#include "watchdog_heartbeat.h"

#define WDT_FEED_TRIES 500

/*
 * To use this sample the devicetree's /aliases must have a 'watchdog0' property.

 LOG_MODULE_REGISTER(APP_IO, LOG_LEVEL_DBG);
 */

LOG_MODULE_REGISTER(WDT_IO, LOG_LEVEL_DBG);
#if DT_HAS_COMPAT_STATUS_OKAY(st_stm32_window_watchdog)
#define WDT_MAX_WINDOW  100U
#elif DT_HAS_COMPAT_STATUS_OKAY(nordic_nrf_wdt)
/* Nordic supports a callback, but it has 61.2 us to complete before
 * the reset occurs, which is too short for this sample to do anything
 * useful.  Explicitly disallow use of the callback.
 */
#define WDT_ALLOW_CALLBACK 0
#elif DT_HAS_COMPAT_STATUS_OKAY(raspberrypi_pico_watchdog)
#define WDT_ALLOW_CALLBACK 0
#elif DT_HAS_COMPAT_STATUS_OKAY(gd_gd32_wwdgt)
#define WDT_MAX_WINDOW 24U
#define WDT_MIN_WINDOW 18U
#define WDG_FEED_INTERVAL 12U
#elif DT_HAS_COMPAT_STATUS_OKAY(intel_tco_wdt)
#define WDT_ALLOW_CALLBACK 0
#define WDT_MAX_WINDOW 3000U
#elif DT_HAS_COMPAT_STATUS_OKAY(nxp_fs26_wdog)
#define WDT_MAX_WINDOW  1024U
#define WDT_MIN_WINDOW	320U
#define WDT_OPT 0
#define WDG_FEED_INTERVAL (WDT_MIN_WINDOW + ((WDT_MAX_WINDOW - WDT_MIN_WINDOW) / 4))
#endif

#ifndef WDT_ALLOW_CALLBACK
#define WDT_ALLOW_CALLBACK 1
#endif

#ifndef WDT_MAX_WINDOW
#define WDT_MAX_WINDOW  5000U
#endif

#ifndef WDT_MIN_WINDOW
#define WDT_MIN_WINDOW  0U
#endif

#ifndef WDG_FEED_INTERVAL
#define WDG_FEED_INTERVAL 1000U
#endif

#ifndef WDT_OPT
#define WDT_OPT (WDT_OPT_PAUSE_HALTED_BY_DBG | WDT_OPT_PAUSE_IN_SLEEP)
#endif


#define MAX_THREADS 10
#define THREAD_CHECK_INTERVAL 10  // Number of WDT cycles to wait before considering a thread unhealthy

struct thread_health {
    k_tid_t thread_id;
    bool is_healthy;
    int counter;
};

static struct thread_health thread_health_array[MAX_THREADS];
static int num_threads = 0;
static K_MUTEX_DEFINE(health_mutex);

void register_thread(k_tid_t thread_id) {
    k_mutex_lock(&health_mutex, K_FOREVER);
    if (num_threads < MAX_THREADS) {
        thread_health_array[num_threads].thread_id = thread_id;
        thread_health_array[num_threads].is_healthy = true;
        thread_health_array[num_threads].counter  = 0;
        num_threads++;
    }
    k_mutex_unlock(&health_mutex);
}

void update_thread_health(k_tid_t thread_id) {
    k_mutex_lock(&health_mutex, K_FOREVER);
    for (int i = 0; i < num_threads; i++) {
        if (thread_health_array[i].thread_id == thread_id) {
            thread_health_array[i].is_healthy = true;
            thread_health_array[i].counter = 0;
            break;
        }
    }
    k_mutex_unlock(&health_mutex);
}

bool all_threads_healthy(void) {
    bool healthy = true;
    k_mutex_lock(&health_mutex, K_FOREVER);
    for (int i = 0; i < num_threads; i++) {
        thread_health_array[i].counter++;
        if (!thread_health_array[i].is_healthy || thread_health_array[i].counter > THREAD_CHECK_INTERVAL) {
			 LOG_INF("Thread %p is unhealthy. is_healthy: %d, counter: %d", 
                    thread_health_array[i].thread_id, 
                    thread_health_array[i].is_healthy, 
                    thread_health_array[i].counter);
            healthy = false;
            break;
        }
    }
    k_mutex_unlock(&health_mutex);
    return healthy;
}

#if WDT_ALLOW_CALLBACK
static void wdt_callback(const struct device *wdt_dev, int channel_id)
{
	static bool handled_event;

	if (handled_event) {
		return;
	}

	wdt_feed(wdt_dev, channel_id);

	LOG_INF("Handled things..ready to reset\n");
	handled_event = true;
}
#endif /* WDT_ALLOW_CALLBACK */

static void wdt_main(void)
{
	int err;
	int wdt_channel_id;
	const struct device *const wdt = DEVICE_DT_GET(DT_ALIAS(watchdog0));

	LOG_INF("Watchdog sample application\n");

	if (!device_is_ready(wdt)) {
		LOG_INF("%s: device not ready.\n", wdt->name);
		return ;
	}

	struct wdt_timeout_cfg wdt_config = {
		/* Reset SoC when watchdog timer expires. */
		.flags = WDT_FLAG_RESET_SOC,

		/* Expire watchdog after max window */
		.window.min = WDT_MIN_WINDOW,
		.window.max = WDT_MAX_WINDOW,
	};

#if WDT_ALLOW_CALLBACK
	/* Set up watchdog callback. */
	wdt_config.callback = wdt_callback;

	LOG_INF("Attempting to test pre-reset callback\n");
#else /* WDT_ALLOW_CALLBACK */
	LOG_INF("Callback in RESET_SOC disabled for this platform\n");
#endif /* WDT_ALLOW_CALLBACK */

	wdt_channel_id = wdt_install_timeout(wdt, &wdt_config);
	if (wdt_channel_id == -ENOTSUP) {
		/* IWDG driver for STM32 doesn't support callback */
		LOG_INF("Callback support rejected, continuing anyway\n");
		wdt_config.callback = NULL;
		wdt_channel_id = wdt_install_timeout(wdt, &wdt_config);
	}
	if (wdt_channel_id < 0) {
		LOG_INF("Watchdog install error\n");
		return ;
	}

	err = wdt_setup(wdt, WDT_OPT);
	if (err < 0) {
		LOG_INF("Watchdog setup error\n");
		return ;
	}

#if WDT_MIN_WINDOW != 0
	/* Wait opening window. */
	k_msleep(WDT_MIN_WINDOW);
#endif
	/* Feeding watchdog. */
	LOG_INF("Feeding watchdog %d times\n", WDT_FEED_TRIES);
	/* Waiting for the SoC reset. */
	LOG_INF("Waiting for reset...\n");

    // Register the main thread
    register_thread(k_current_get());

    while (1) {
        // Update health status of the WDT thread
        update_thread_health(k_current_get());

        if (all_threads_healthy()) {
            //LOG_INF("All threads healthy, feeding watchdog...\n");
            wdt_feed(wdt, wdt_channel_id);
        } else {
            LOG_INF("Not all threads are healthy, allowing WDT reset...\n");
        }

        k_sleep(K_MSEC(WDG_FEED_INTERVAL));
    }
}

// Function to be called by other threads periodically
void heartbeat(void) {
	//LOG_INF("Heartbeat from thread %p\n", k_current_get());
    update_thread_health(k_current_get());
}

K_THREAD_DEFINE(wdt_thread, 1024, wdt_main, NULL, NULL, NULL, 7, K_ESSENTIAL, 0);