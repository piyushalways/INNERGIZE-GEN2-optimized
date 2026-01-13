#include "bluetooth_manager.h"
#include "startup.h"
#include "io_adapter.h"
#include "ems_engine.h"
#include "watchdog_heartbeat.h"
#include "ppg.h"

#include <zephyr/kernel.h>
#include <zephyr/bluetooth/bluetooth.h>
#include <zephyr/bluetooth/gatt.h>
#include <zephyr/bluetooth/uuid.h>
#include <zephyr/logging/log.h>
#include <hal/nrf_gpio.h>
#include <zephyr/bluetooth/conn.h>
#include <zephyr/bluetooth/gap.h>
#include <zephyr/bluetooth/hci.h>
#include <zephyr/settings/settings.h>
#include <zephyr/drivers/hwinfo.h> // For reset reason
#include <zephyr/drivers/gpio.h>
#include <bluetooth/services/bms.h>
#include <zephyr/drivers/pwm.h>
#include <zephyr/drivers/flash.h>
#include <zephyr/devicetree.h>

#include <bluetooth/services/fast_pair/fast_pair.h>
#include <bluetooth/adv_prov/fast_pair.h>

#include <zephyr/sys/__assert.h>
#include <dk_buttons_and_leds.h>

#include <zephyr/drivers/counter.h>

// --- ADD THESE ---
#include <nrfx_grtc.h>
#include <zephyr/drivers/timer/nrf_grtc_timer.h>

#include "bt_adv_helper.h"
#include "hids_helper.h"
#include "battery_module.h"
#include "ppg.h"

// --- ADDED --- Include for HCI Vendor-Specific commands
#include <zephyr/bluetooth/hci_vs.h>
#include <zephyr/sys/byteorder.h>
// --- END ADDED ---

// --- ADDED --- Includes for time.h, system time, and time utilities
#include <time.h>

// --- END ADDED ---

LOG_MODULE_REGISTER(BLE, LOG_LEVEL_DBG);


/* *** NEW: Define a semaphore for signaling connection events *** */
K_SEM_DEFINE(connection_sem, 0, 1);

#define DEVICE_NAME             CONFIG_BT_DEVICE_NAME
#define DEVICE_NAME_LEN         (sizeof(DEVICE_NAME) - 1)

#define BATT_MAX_VOLTAGE_MV             2100 // Max battery voltage (100%)
#define BATT_MIN_VOLTAGE_MV             1500 // Minimum allowed battery voltage (0%)

// --- ADDED ---
// Variable to store the last known time for persistence
static struct timespec last_known_time;

/* Current Time Service UUID */
#define BT_UUID_CTS_VAL 0x1805
#define BT_UUID_CTS BT_UUID_DECLARE_16(BT_UUID_CTS_VAL)

/* Current Time Characteristic UUID */
#define BT_UUID_CTS_CURRENT_TIME_VAL 0x2A2B
#define BT_UUID_CTS_CURRENT_TIME BT_UUID_DECLARE_16(BT_UUID_CTS_CURRENT_TIME_VAL)

// Define the GRTC frequency (32.768 kHz)
#define GRTC_FREQ_HZ 1000000

// EMS service UUIDs
#define EMS_SERVICE_UUID_VAL            BT_UUID_128_ENCODE(0x5cf7d300, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b)
#define EMS_CONTROL_UUID_VAL            BT_UUID_128_ENCODE(0x5cf7d301, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b)
#define EMS_SESSION_UUID_VAL            BT_UUID_128_ENCODE(0x5cf7d302, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b)

#define CHAN1_PWM_PERIOD                BT_UUID_128_ENCODE(0x5cf7d303, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b)
#define CHAN1_PWM_DEFAULT_ON_TIME       BT_UUID_128_ENCODE(0x5cf7d304, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b)
#define POWER_SIGNAL_DEFAULT_INTERVAL   BT_UUID_128_ENCODE(0x5cf7d305, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b)
#define POWER_SIGNAL_DEFAULT_DURATION   BT_UUID_128_ENCODE(0x5cf7d306, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b)

#define CHAN0_PLAYBACK_COUNT            BT_UUID_128_ENCODE(0x5cf7d307, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b)
#define CHAN0_BEFORE_INDUC              BT_UUID_128_ENCODE(0x5cf7d308, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b)
#define CHAN0_DEFAULT_ON_DURATION       BT_UUID_128_ENCODE(0x5cf7d309, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b)
#define CHAN0_DEFAULT_DURATION          BT_UUID_128_ENCODE(0x5cf7d30a, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b)

#define CHAN23_PWM_DEFAULT_PERIOD_NS    BT_UUID_128_ENCODE(0x5cf7d30b, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b)
#define CHAN23_PWM_DEFAULT_ON_TIME_NS   BT_UUID_128_ENCODE(0x5cf7d30c, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b)

#define CHARGER_UUID                    BT_UUID_128_ENCODE(0x5cf7d518, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b)
#define CHARGER_ON_OFF                  BT_UUID_128_ENCODE(0x5cf7d519, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b)

// Charger Battery Service UUIDs
#define CHARGER_BATT_SERVICE_UUID_VAL   BT_UUID_128_ENCODE(0x5cf7d600, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b)
#define CHARGER_BATT_PERCENT_UUID_VAL   BT_UUID_128_ENCODE(0x5cf7d601, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b)

// Power Mode Service UUIDs
#define POWER_MODE_SERVICE_UUID_VAL     BT_UUID_128_ENCODE(0x5cf7d700, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b)
#define POWER_MODE_CHAR_UUID_VAL        BT_UUID_128_ENCODE(0x5cf7d701, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b)

// Fuel Gauge Service UUIDs
#define FUEL_GAUGE_SERVICE_UUID_VAL     BT_UUID_128_ENCODE(0x5cf7d800, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b)
#define FUEL_GAUGE_TTE_UUID_VAL         BT_UUID_128_ENCODE(0x5cf7d801, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b)
#define FUEL_GAUGE_TTF_UUID_VAL         BT_UUID_128_ENCODE(0x5cf7d802, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b)
#define FUEL_GAUGE_CHG_STATUS_UUID_VAL  BT_UUID_128_ENCODE(0x5cf7d803, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b)

/*
 * PPG Service:         F3641400-00B0-4240-BA50-05CA45BFeF1F
 * PPG Control Characteristic: F3641401-00B0-4240-BA50-05CA45BFeF1F (Write-only)
 */
static struct bt_uuid_128 ppg_service_uuid = BT_UUID_INIT_128(
	BT_UUID_128_ENCODE(0x5cf7d514, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b));

static struct bt_uuid_128 ppg_control_char_uuid = BT_UUID_INIT_128(
	BT_UUID_128_ENCODE(0x5cf7d515, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b));

    // --- ADD A NEW UUID for the data ---
static struct bt_uuid_128 ppg_data_char_uuid = BT_UUID_INIT_128(
	BT_UUID_128_ENCODE(0x5cf7d516, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b));

    // --- UUID for HRV Features characteristic ---
static struct bt_uuid_128 ppg_hrv_features_char_uuid = BT_UUID_INIT_128(
	BT_UUID_128_ENCODE(0x5cf7d517, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b));

    // --- Add a variable to track if notifications are enabled ---
static bool ppg_notify_enabled = false;
static bool hrv_features_notify_enabled = false;

/******************************************************************************
 *                       FLASH DATA SERVICE UUIDs                             *
 ******************************************************************************/
/*
 * Flash Data Service:  0x5cf7d520-0ac9-4df4-b0e5-e28a976fe53b
 * Flash Control:       0x5cf7d521-0ac9-4df4-b0e5-e28a976fe53b (Write)
 * Flash Data:          0x5cf7d522-0ac9-4df4-b0e5-e28a976fe53b (Notify)
 * Flash Status:        0x5cf7d523-0ac9-4df4-b0e5-e28a976fe53b (Read)
 */
static struct bt_uuid_128 flash_service_uuid = BT_UUID_INIT_128(
	BT_UUID_128_ENCODE(0x5cf7d520, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b));

static struct bt_uuid_128 flash_control_char_uuid = BT_UUID_INIT_128(
	BT_UUID_128_ENCODE(0x5cf7d521, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b));

static struct bt_uuid_128 flash_data_char_uuid = BT_UUID_INIT_128(
	BT_UUID_128_ENCODE(0x5cf7d522, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b));

static struct bt_uuid_128 flash_status_char_uuid = BT_UUID_INIT_128(
	BT_UUID_128_ENCODE(0x5cf7d523, 0x0ac9, 0x4df4, 0xb0e5, 0xe28a976fe53b));

/******************************************************************************
 *                       FLASH DATA SERVICE GLOBALS                           *
 ******************************************************************************/

/* Flash device and parameters - set by PPG module */
static const struct device *ble_flash_dev = NULL;
static off_t ble_flash_offset = 0;
static size_t ble_flash_sample_count = 0;

/* Flash data notification enabled flag */
static bool flash_data_notify_enabled = false;

/* Buffer for reading flash data */
#define FLASH_READ_CHUNK_SIZE  240  /* Read 60 samples (240 bytes) at a time */
static uint8_t flash_read_buffer[FLASH_READ_CHUNK_SIZE];

/* Pointer to flash data characteristic attribute (initialized after service definition) */
static const struct bt_gatt_attr *flash_data_attr = NULL;

/* Flash streaming state */
static struct {
    struct k_work_delayable work;
    struct bt_conn *conn;
    uint32_t offset;
    uint32_t bytes_remaining;
    bool active;
} flash_stream;


/**
 * @brief Callback for settings_load_subtree_direct.
 * This is called for each key found in "ble/time".
 */



struct persistent_time {
    struct timespec wall_time; // The human-readable time
    uint64_t grtc_ticks;       // The raw GRTC ticks at that time
};
static struct persistent_time last_saved_time = {0};

static int time_load_cb(const char *key, size_t len, settings_read_cb read_cb, void *cb_arg)
{
    // We only care about the "time_snapshot" key
    if (strcmp(key, "time_snapshot") == 0) {
        if (len != sizeof(last_saved_time)) {
            LOG_ERR("Invalid time snapshot size from flash");
            return -EINVAL;
        }

        // Read the value directly into our global variable
        int rc = read_cb(cb_arg, &last_saved_time, sizeof(last_saved_time));
        if (rc < 0) {
            LOG_ERR("Failed to read time_snapshot (err %d)", rc);
            return rc;
        }
        
        LOG_INF("Loaded 'time_snapshot' from flash.");
    }
    return 0;
}

/* Current Time structure based on Bluetooth spec */
struct cts_current_time {
    uint16_t year;
    uint8_t month;
    uint8_t day;
    uint8_t hours;
    uint8_t minutes;
    uint8_t seconds;
    uint8_t day_of_week;
    uint8_t fractions256;
    uint8_t adjust_reason;
} __packed;

static struct cts_current_time current_time = {
    .year = 2024,
    .month = 11,
    .day = 15,
    .hours = 12,
    .minutes = 30,
    .seconds = 0,
    .day_of_week = 6, /* Saturday */
    .fractions256 = 0,
    .adjust_reason = 0
};

/* Notification enabled flag */
static bool notify_enabled = false;

// --- Add the callback for when the client enables/disables notifications ---
static void on_ppg_ccc_changed(const struct bt_gatt_attr *attr, uint16_t value)
{
    ppg_notify_enabled = (value == BT_GATT_CCC_NOTIFY);
    LOG_INF("PPG data notifications %s", ppg_notify_enabled ? "enabled" : "disabled");
}

// --- Callback for HRV Features notifications ---
static void on_hrv_features_ccc_changed(const struct bt_gatt_attr *attr, uint16_t value)
{
    hrv_features_notify_enabled = (value == BT_GATT_CCC_NOTIFY);
    LOG_INF("HRV features notifications %s", hrv_features_notify_enabled ? "enabled" : "disabled");
}

/******************************************************************************
 *                   FLASH DATA SERVICE CALLBACKS                             *
 ******************************************************************************/

/**
 * @brief Callback when flash data notifications are enabled/disabled
 */
static void on_flash_data_ccc_changed(const struct bt_gatt_attr *attr, uint16_t value)
{
    flash_data_notify_enabled = (value == BT_GATT_CCC_NOTIFY);
    LOG_INF("Flash data notifications %s", flash_data_notify_enabled ? "enabled" : "disabled");

    /* Cancel any ongoing flash streaming if notifications are disabled */
    if (!flash_data_notify_enabled && flash_stream.active) {
        k_work_cancel_delayable(&flash_stream.work);
        flash_stream.active = false;
        if (flash_stream.conn) {
            bt_conn_unref(flash_stream.conn);
            flash_stream.conn = NULL;
        }
        ppg_resume_after_flash_read();
        LOG_INF("Flash streaming cancelled");
    }
}

/**
 * @brief Work handler for asynchronous flash data streaming
 *
 * This runs in a work queue context and sends flash data in small chunks
 * with delays to keep the BLE connection alive and avoid overwhelming the stack.
 */
static void flash_stream_work_handler(struct k_work *work)
{
    if (!flash_stream.active || !flash_stream.conn) {
        return;
    }

    /* Check if connection is still valid */
    if (!flash_data_notify_enabled) {
        LOG_WRN("Flash notifications disabled during streaming");
        goto cleanup;
    }

    /* Determine chunk size for this iteration */
    uint32_t chunk_size = flash_stream.bytes_remaining;
    if (chunk_size > FLASH_READ_CHUNK_SIZE) {
        chunk_size = FLASH_READ_CHUNK_SIZE;
    }

    /* Read from flash */
    int rc = flash_read(ble_flash_dev, flash_stream.offset,
                       flash_read_buffer, chunk_size);
    if (rc) {
        LOG_ERR("Flash read failed at offset 0x%06x (err %d)",
               (unsigned)flash_stream.offset, rc);
        goto cleanup;
    }

    /* Send notification */
    rc = bt_gatt_notify(flash_stream.conn, flash_data_attr,
                       flash_read_buffer, chunk_size);
    if (rc) {
        if (rc == -ENOTCONN) {
            LOG_ERR("Connection lost during flash streaming");
        } else if (rc != -ENOMEM) {
            LOG_ERR("Flash notify failed (err %d)", rc);
        } else {
            /* -ENOMEM: TX buffer full, retry after delay */
            LOG_DBG("TX buffer full, retrying...");
            k_work_schedule(&flash_stream.work, K_MSEC(50));
            return;
        }
        goto cleanup;
    }

    /* Update state */
    flash_stream.offset += chunk_size;
    flash_stream.bytes_remaining -= chunk_size;

    /* Check if done */
    if (flash_stream.bytes_remaining == 0) {
        LOG_INF("Flash streaming complete: %u bytes sent",
               (unsigned)(flash_stream.offset - ble_flash_offset));
        goto cleanup;
    }

    /* Schedule next chunk with delay to keep connection alive */
    /* Use 20ms delay - enough time for BLE events but fast streaming */
    k_work_schedule(&flash_stream.work, K_MSEC(20));
    return;

cleanup:
    flash_stream.active = false;
    if (flash_stream.conn) {
        bt_conn_unref(flash_stream.conn);
        flash_stream.conn = NULL;
    }
    ppg_resume_after_flash_read();
    LOG_INF("PPG processing RESUMED after flash read");
}

/**
 * @brief Flash Control Write Callback
 *
 * Format: [COMMAND(1)]
 * - COMMAND: 1 byte (0x01 = read all available flash data)
 *
 * When 0x01 is received, starts asynchronous flash data streaming
 * using the stored ble_flash_offset and ble_flash_sample_count parameters.
 */
static ssize_t on_flash_control_write(struct bt_conn *conn,
                                      const struct bt_gatt_attr *attr,
                                      const void *buf, uint16_t len,
                                      uint16_t offset, uint8_t flags)
{
    if (len != 1) {
        LOG_ERR("Flash control write: invalid length %d (expected 1)", len);
        return BT_GATT_ERR(BT_ATT_ERR_INVALID_ATTRIBUTE_LEN);
    }

    if (!ble_flash_dev) {
        LOG_ERR("Flash device not initialized");
        return BT_GATT_ERR(BT_ATT_ERR_UNLIKELY);
    }

    if (!flash_data_notify_enabled) {
        LOG_WRN("Flash data notifications not enabled");
        return BT_GATT_ERR(BT_ATT_ERR_CCC_IMPROPER_CONF);
    }

    if (!flash_data_attr) {
        LOG_ERR("Flash data attribute not initialized");
        return BT_GATT_ERR(BT_ATT_ERR_UNLIKELY);
    }

    const uint8_t *data = (const uint8_t *)buf;
    uint8_t command = data[0];

    /* Validate command is 0x01 (read all data) */
    if (command != 0x01) {
        LOG_ERR("Flash control write: invalid command 0x%02x (expected 0x01)", command);
        return BT_GATT_ERR(BT_ATT_ERR_VALUE_NOT_ALLOWED);
    }

    /* Check if already streaming */
    if (flash_stream.active) {
        LOG_WRN("Flash streaming already in progress");
        return BT_GATT_ERR(BT_ATT_ERR_UNLIKELY);
    }

    /* Calculate bytes to transfer */
    uint32_t bytes_to_read = ble_flash_sample_count * 4;  /* 4 bytes per sample */

    LOG_INF("Flash read request (0x01): offset=0x%06x, count=%u samples (%u bytes)",
           (unsigned)ble_flash_offset, (unsigned)ble_flash_sample_count, (unsigned)bytes_to_read);

    /* PAUSE PPG processing to prevent BLE contention and speed up transfer */
    ppg_pause_for_flash_read();
    LOG_INF("PPG processing PAUSED for flash read");

    /* Initialize streaming state */
    flash_stream.offset = ble_flash_offset;
    flash_stream.bytes_remaining = bytes_to_read;
    flash_stream.conn = bt_conn_ref(conn);
    flash_stream.active = true;

    /* Start asynchronous streaming immediately */
    k_work_schedule(&flash_stream.work, K_NO_WAIT);

    return len;
}

/**
 * @brief Flash Status Read Callback
 *
 * Format: [OFFSET(4)] [COUNT(4)] [AVAILABLE(1)]
 * - OFFSET: 4 bytes (uint32_t, little-endian) - Current flash write offset
 * - COUNT: 4 bytes (uint32_t, little-endian) - Number of samples available
 * - AVAILABLE: 1 byte (uint8_t) - Flash status (1=ready, 0=not ready)
 * Total: 9 bytes
 */
static ssize_t on_flash_status_read(struct bt_conn *conn,
                                    const struct bt_gatt_attr *attr,
                                    void *buf, uint16_t len, uint16_t offset)
{
    uint8_t status_data[9];

    /* Pack offset (little-endian) */
    status_data[0] = (ble_flash_offset) & 0xFF;
    status_data[1] = (ble_flash_offset >> 8) & 0xFF;
    status_data[2] = (ble_flash_offset >> 16) & 0xFF;
    status_data[3] = (ble_flash_offset >> 24) & 0xFF;

    /* Pack sample count (little-endian) */
    status_data[4] = (ble_flash_sample_count) & 0xFF;
    status_data[5] = (ble_flash_sample_count >> 8) & 0xFF;
    status_data[6] = (ble_flash_sample_count >> 16) & 0xFF;
    status_data[7] = (ble_flash_sample_count >> 24) & 0xFF;

    /* Pack available flag */
    status_data[8] = (ble_flash_dev != NULL) ? 1 : 0;

    return bt_gatt_attr_read(conn, attr, buf, len, offset, status_data, sizeof(status_data));
}

/**
 * @brief Updates the global 'current_time' struct from the
 * Zephyr system wall clock (backed by GRTC).
 */
static void update_current_time_from_system(void)
{
    struct timespec ts;
    struct tm tm_data;

    // Get current time from system
    if (clock_gettime(CLOCK_REALTIME, &ts) != 0) {
        LOG_ERR("Failed to get CLOCK_REALTIME");
        return;
    }

    // Convert time_t (seconds) to struct tm (GMT/UTC)
    if (gmtime_r(&ts.tv_sec, &tm_data) == NULL) {
        LOG_ERR("Failed to get gmtime_r");
        return;
    }

    // Populate the CTS structure
    current_time.year = tm_data.tm_year + 1900; // tm_year is years since 1900
    current_time.month = tm_data.tm_mon + 1;    // tm_mon is 0-11
    current_time.day = tm_data.tm_mday;
    current_time.hours = tm_data.tm_hour;
    current_time.minutes = tm_data.tm_min;
    current_time.seconds = tm_data.tm_sec;

    // Adjust day of week: tm_wday is 0=Sun...6=Sat
    // CTS is 1=Mon...7=Sun
    if (tm_data.tm_wday == 0) { // Sunday
        current_time.day_of_week = 7;
    } else {
        current_time.day_of_week = tm_data.tm_wday;
    }

    // Get fractions of a second (1/256th) from nanoseconds
    // (ts.tv_nsec / 1_000_000_000) * 256
    // = ts.tv_nsec / (1_000_000_000 / 256)
    // = ts.tv_nsec / 3906250
    current_time.fractions256 = (uint8_t)(ts.tv_nsec / 3906250);
    
    // Adjust reason is not modified, assumed to be part of the client's write
}

static ssize_t read_current_time(struct bt_conn *conn,
                                 const struct bt_gatt_attr *attr,
                                 void *buf, uint16_t len, uint16_t offset)
{
    printk("Current time read by client\n");
    
    // --- NEW LOGIC: Update buffer from system clock ---
    update_current_time_from_system();
    // --- END NEW LOGIC ---

    return bt_gatt_attr_read(conn, attr, buf, len, offset, &current_time,
                             sizeof(current_time));
}

static ssize_t write_current_time(struct bt_conn *conn,
                                  const struct bt_gatt_attr *attr,
                                  const void *buf, uint16_t len, uint16_t offset,
                                  uint8_t flags)
{
    if (len != sizeof(struct cts_current_time)) {
        return BT_GATT_ERR(BT_ATT_ERR_INVALID_ATTRIBUTE_LEN);
    }

    // Copy data into our buffer struct first
    memcpy(&current_time, buf, len);
    
    printk("Current time updated by client\n");
    printk("New time: %04u-%02u-%02u %02u:%02u:%02u\n",
           current_time.year, current_time.month, current_time.day,
           current_time.hours, current_time.minutes, current_time.seconds);

    // --- NEW LOGIC: Set the system wall clock ---
    struct tm new_tm = {0};
    new_tm.tm_year = current_time.year - 1900;
    new_tm.tm_mon = current_time.month - 1;
    new_tm.tm_mday = current_time.day;
    new_tm.tm_hour = current_time.hours;
    new_tm.tm_min = current_time.minutes;
    new_tm.tm_sec = current_time.seconds;
    new_tm.tm_isdst = 0;

    // Use Zephyr's time utility to convert struct tm to time_t (seconds since epoch)
    time_t new_time_t = timeutil_timegm(&new_tm);
    if (new_time_t == -1) {
        LOG_ERR("Invalid time data from client (timeutil_timegm failed)");
        return len; // Still accept the write, but don't set system time
    }

    struct timespec new_ts;
    new_ts.tv_sec = new_time_t;
    // Convert fractions (1/256s) back to nanoseconds
    new_ts.tv_nsec = (uint32_t)current_time.fractions256 * 3906250; 

    // Set the system's real-time clock
    int err = clock_settime(CLOCK_REALTIME, &new_ts);
    if (err) {
         LOG_ERR("Failed to set system time (err %d)", err);
    } else {
         LOG_INF("System wall clock set successfully.");
    }
    // --- END NEW LOGIC ---

    return len;
}

static void current_time_ccc_cfg_changed(const struct bt_gatt_attr *attr,
                                        uint16_t value)
{
    notify_enabled = (value == BT_GATT_CCC_NOTIFY);
    printk("Current time notifications %s\n", notify_enabled ? "enabled" : "disabled");
}


#define RUN_STATUS_LED                  DK_LED1
#define CON_STATUS_LED                  DK_LED2
#define FP_ADV_MODE_STATUS_LED          DK_LED3

#define FP_ADV_MODE_BUTTON_MASK         DK_BTN1_MSK
#define VOLUME_UP_BUTTON_MASK           DK_BTN2_MSK
#define BOND_REMOVE_BUTTON_MASK         DK_BTN3_MSK
#define VOLUME_DOWN_BUTTON_MASK         DK_BTN4_MSK

#define RUN_LED_BLINK_INTERVAL_MS       1000
#define FP_ADV_MODE_SHOW_UI_INDICATION_LED_BLINK_INTERVAL_MS    500
#define FP_ADV_MODE_HIDE_UI_INDICATION_LED_BLINK_INTERVAL_MS    1500

#define FP_DISC_ADV_TIMEOUT_MINUTES     (10)

#define INIT_SEM_TIMEOUT_SECONDS        (60)

// --- ADDED --- Assert that VS HCI is enabled in config
BUILD_ASSERT(IS_ENABLED(CONFIG_BT_HAS_HCI_VS),
         "This app requires Zephyr-specific HCI vendor extensions");
// --- END ADDED ---

static enum bt_fast_pair_adv_mode fp_adv_mode = BT_FAST_PAIR_ADV_MODE_DISC;
static bool show_ui_pairing = true;
static bool new_adv_session = true;
struct bt_conn *peer;  /* Non-static so flash service can access it */

// --- ADDED --- Variables for dynamic Tx power
#define DEVICE_BEACON_TXPOWER_NUM 8
static uint16_t peer_handle;
static const int8_t txpower[DEVICE_BEACON_TXPOWER_NUM] = {4, 0, -3, -8, -15, -18, -23, -30};
static struct k_thread pwr_thread_data;
static K_THREAD_STACK_DEFINE(pwr_thread_stack, 2048);
// --- END ADDED ---

static struct k_work bt_adv_restart;
static struct k_work_delayable fp_adv_mode_status_led_handle;
static struct k_work_delayable fp_disc_adv_timeout;

static void init_work_handle(struct k_work *w);

static K_SEM_DEFINE(init_work_sem, 0, 1);
static K_WORK_DEFINE(init_work, init_work_handle);

// Add this enum and state variable near the top
typedef enum {
    PHY_UNKNOWN,
    PHY_1M,
    PHY_2M,
    PHY_CODED
} phy_type_t;

static phy_type_t current_phy = PHY_UNKNOWN;

// Power mode definitions
typedef enum {
    POWER_MODE_SLEEP,         // Lowest power consumption
    POWER_MODE_AVERAGE,       // Balanced power consumption
    POWER_MODE_HIGH_POWER     // Maximum performance, highest power
} power_mode_t;

// Structure to hold BLE parameters for each power mode
typedef struct {
    phy_type_t phy;           // PHY type (1M, 2M, or Coded)
    uint16_t conn_interval_ms; // Connection interval in milliseconds
    int8_t tx_power_dbm;      // TX power in dBm
    uint16_t latency;         // Connection latency
    uint16_t timeout;         // Supervision timeout (10ms units)
} ble_power_config_t;

// Power mode configurations
static const ble_power_config_t power_mode_configs[] = {
    [POWER_MODE_SLEEP] = {
        .phy = PHY_CODED,         // Coded PHY for long range, low power
        .conn_interval_ms = 500,  // 500ms interval - very long for low power
        .tx_power_dbm = -20,      // -20 dBm - very low TX power
        .latency = 4,             // Higher latency to skip more connection events
        .timeout = 600            // 6 second timeout (600 * 10ms)
    },
    [POWER_MODE_AVERAGE] = {
        .phy = PHY_1M,            // 1M PHY - standard, balanced
        .conn_interval_ms = 100,  // 100ms interval - moderate
        .tx_power_dbm = 0,        // 0 dBm - moderate TX power
        .latency = 2,             // Moderate latency
        .timeout = 400            // 4 second timeout (400 * 10ms)
    },
    [POWER_MODE_HIGH_POWER] = {
        .phy = PHY_2M,            // 2M PHY for maximum throughput
        .conn_interval_ms = 15,   // 15ms interval - very fast
        .tx_power_dbm = 8,        // +8 dBm - maximum TX power
        .latency = 0,             // No latency - respond to every event
        .timeout = 400            // 4 second timeout (400 * 10ms)
    }
};

// Current power mode state
static power_mode_t current_power_mode = POWER_MODE_AVERAGE;

// State variable for the connection interval
static uint16_t current_interval_ms = 30;

// State variables for different advertising intervals
static const uint16_t adv_intervals_ms[] = {30, 150, 500};
static uint8_t adv_interval_idx = 0;

/* STEP 11.2 - Create variable that holds callback for MTU negotiation */
static struct bt_gatt_exchange_params exchange_params;

/* STEP 13.4 - Forward declaration of exchange_func(): */
static void exchange_func(struct bt_conn *conn, uint8_t att_err, struct bt_gatt_exchange_params *params);


// Read callbacks
static ssize_t ems_read_callback(struct bt_conn *conn, const struct bt_gatt_attr *attr, void *buf, uint16_t len, uint16_t offset);
static ssize_t batt_read_callback(struct bt_conn *conn, const struct bt_gatt_attr *attr, void *buf, uint16_t len, uint16_t offset);
static ssize_t charger_read_callback(struct bt_conn *conn, const struct bt_gatt_attr *attr, void *buf, uint16_t len, uint16_t offset);

// Add read callback declaration
static ssize_t charger_batt_read_callback(struct bt_conn *conn, const struct bt_gatt_attr *attr,
                      void *buf, uint16_t len, uint16_t offset);

// Write callbacks
static ssize_t ems_write_cb(struct bt_conn *conn, const struct bt_gatt_attr *attr, const void *buf, uint16_t len, uint16_t offset, uint8_t flags);

// CCC changed callbacks
static void batt_ccc_value_changed(const struct bt_gatt_attr *attr, uint16_t value);

// Add CCC changed callback declaration
static void charger_batt_ccc_value_changed(const struct bt_gatt_attr *attr, uint16_t value);

// Fuel gauge read callback declarations
static ssize_t fuel_gauge_tte_read_callback(struct bt_conn *conn, const struct bt_gatt_attr *attr,
                                            void *buf, uint16_t len, uint16_t offset);
static ssize_t fuel_gauge_ttf_read_callback(struct bt_conn *conn, const struct bt_gatt_attr *attr,
                                            void *buf, uint16_t len, uint16_t offset);
static ssize_t fuel_gauge_chg_status_read_callback(struct bt_conn *conn, const struct bt_gatt_attr *attr,
                                                   void *buf, uint16_t len, uint16_t offset);

// Fuel gauge CCC changed callback declarations
static void fuel_gauge_tte_ccc_changed(const struct bt_gatt_attr *attr, uint16_t value);
static void fuel_gauge_ttf_ccc_changed(const struct bt_gatt_attr *attr, uint16_t value);
static void fuel_gauge_chg_status_ccc_changed(const struct bt_gatt_attr *attr, uint16_t value);

// Power mode function forward declaration
static int apply_power_mode(power_mode_t mode);

// UUIDs
static struct bt_uuid_128 ems_service_uuid = BT_UUID_INIT_128(EMS_SERVICE_UUID_VAL);
static struct bt_uuid_128 ems_control_uuid = BT_UUID_INIT_128(EMS_CONTROL_UUID_VAL);
static struct bt_uuid_128 ems_session_uuid = BT_UUID_INIT_128(EMS_SESSION_UUID_VAL);

static struct bt_uuid_128 pwm_period_uuid = BT_UUID_INIT_128(CHAN1_PWM_PERIOD);
static struct bt_uuid_128 pwm_ontime_uuid = BT_UUID_INIT_128(CHAN1_PWM_DEFAULT_ON_TIME);
static struct bt_uuid_128 pwm_interval_uuid = BT_UUID_INIT_128(POWER_SIGNAL_DEFAULT_INTERVAL);
static struct bt_uuid_128 pwm_duration_uuid = BT_UUID_INIT_128(POWER_SIGNAL_DEFAULT_DURATION);

static struct bt_uuid_128 chan23_duration_uuid = BT_UUID_INIT_128(CHAN23_PWM_DEFAULT_PERIOD_NS);
static struct bt_uuid_128 chan23_on_duration_uuid = BT_UUID_INIT_128(CHAN23_PWM_DEFAULT_ON_TIME_NS);

static struct bt_uuid_128 chan0_playback_uuid = BT_UUID_INIT_128(CHAN0_PLAYBACK_COUNT);
static struct bt_uuid_128 chan0_induct_uuid = BT_UUID_INIT_128(CHAN0_BEFORE_INDUC);
static struct bt_uuid_128 chan0_on_duration_uuid = BT_UUID_INIT_128(CHAN0_DEFAULT_ON_DURATION );
static struct bt_uuid_128 chan0_duration_uuid = BT_UUID_INIT_128(CHAN0_DEFAULT_DURATION);

static struct bt_uuid_16 batt_service_uuid = BT_UUID_INIT_16(0x180f);
static struct bt_uuid_16 batt_val_uuid = BT_UUID_INIT_16(0x2a19);

static struct bt_uuid_128 charger_uuid = BT_UUID_INIT_128(CHARGER_UUID);
static struct bt_uuid_128 charger_on_off_uuid = BT_UUID_INIT_128(CHARGER_ON_OFF);

static struct bt_uuid_128 charger_batt_service_uuid = BT_UUID_INIT_128(CHARGER_BATT_SERVICE_UUID_VAL);
static struct bt_uuid_128 charger_batt_percent_uuid = BT_UUID_INIT_128(CHARGER_BATT_PERCENT_UUID_VAL);

// Power Mode Service UUIDs
static struct bt_uuid_128 power_mode_service_uuid = BT_UUID_INIT_128(POWER_MODE_SERVICE_UUID_VAL);
static struct bt_uuid_128 power_mode_char_uuid = BT_UUID_INIT_128(POWER_MODE_CHAR_UUID_VAL);

// Fuel Gauge Service UUIDs
static struct bt_uuid_128 fuel_gauge_service_uuid = BT_UUID_INIT_128(FUEL_GAUGE_SERVICE_UUID_VAL);
static struct bt_uuid_128 fuel_gauge_tte_uuid = BT_UUID_INIT_128(FUEL_GAUGE_TTE_UUID_VAL);
static struct bt_uuid_128 fuel_gauge_ttf_uuid = BT_UUID_INIT_128(FUEL_GAUGE_TTF_UUID_VAL);
static struct bt_uuid_128 fuel_gauge_chg_status_uuid = BT_UUID_INIT_128(FUEL_GAUGE_CHG_STATUS_UUID_VAL);


static const uint8_t bms_auth_code[] = {'A', 'B', 'C', 'D'};

static const struct bt_data ad[] = {
    BT_DATA_BYTES(BT_DATA_FLAGS, (BT_LE_AD_GENERAL | BT_LE_AD_NO_BREDR)),
    BT_DATA(BT_DATA_NAME_COMPLETE, DEVICE_NAME, DEVICE_NAME_LEN),
};


static const struct bt_data sd[] = {
    BT_DATA_BYTES(BT_DATA_UUID16_ALL, BT_UUID_16_ENCODE(BT_UUID_BMS_VAL),BT_UUID_16_ENCODE(BT_UUID_DIS_VAL)),
};

K_MSGQ_DEFINE(ble_msgq, sizeof(struct ble_msg), 5, 4); // BLE message queue

extern struct k_msgq main_msgq; // Main message queue, defined in main.h

struct ems_def ems_session_data = {0}; // EMS session data

uint8_t disconnect_reason = 0; // Disconnect reason

extern k_tid_t my_tid1;
extern k_tid_t my_tid2;
extern k_tid_t my_tid3;

static struct bt_le_adv_param adv_param;

bool pairing_on = true;

// Add this new state variable
static bool phy_update_pending = false;

uint8_t batt_percent; // Battery percentage

// Add this variable to store charger battery percentage
uint8_t charger_batt_percent = 69;

// Fuel gauge data variables
static float fuel_gauge_tte = 0.0f;  // Time To Empty in seconds
static float fuel_gauge_ttf = 0.0f;  // Time To Full in seconds
static uint8_t fuel_gauge_charging_status = 0;  // Charging status
static bool fuel_gauge_tte_notify_enabled = false;
static bool fuel_gauge_ttf_notify_enabled = false;
static bool fuel_gauge_chg_status_notify_enabled = false;


// Add these new variables for PHY switching hysteresis
static phy_type_t candidate_phy = PHY_UNKNOWN;
static uint8_t stable_rssi_count = 0;
#define PHY_SWITCH_THRESHOLD 3 // Require 3 seconds of stability


static ssize_t on_ppg_control_write(struct bt_conn *conn,
                                    const struct bt_gatt_attr *attr,
                                    const void *buf, uint16_t len,
                                    uint16_t offset, uint8_t flags)
{
    if (len > 0) {
        uint8_t command = ((uint8_t*)buf)[0];
        ppg_cmd_t ppg_cmd;

        if (command == 0x01) {
            ppg_cmd = PPG_CMD_BLE_START;
            LOG_INF("Received BLE command: START");
            // Try to send the message. K_NO_WAIT is safe from an ISR.
            k_msgq_put(&ppg_cmd_q, &ppg_cmd, K_NO_WAIT);
        } else if (command == 0x00) {
            ppg_cmd = PPG_CMD_BLE_STOP;
            LOG_INF("Received BLE command: STOP");
            k_msgq_put(&ppg_cmd_q, &ppg_cmd, K_NO_WAIT);
        }
    }
    return len;
}

// --- ADDED --- Helper functions for dynamic Tx power control
static void read_conn_rssi(uint16_t handle, int8_t *rssi)
{
    struct net_buf *buf, *rsp = NULL;
    struct bt_hci_cp_read_rssi *cp;
    struct bt_hci_rp_read_rssi *rp;

    int err;

    buf = bt_hci_cmd_create(BT_HCI_OP_READ_RSSI, sizeof(*cp));
    if (!buf) {
        LOG_WRN("Unable to allocate command buffer");
        return;
    }

    cp = net_buf_add(buf, sizeof(*cp));
    cp->handle = sys_cpu_to_le16(handle);

    err = bt_hci_cmd_send_sync(BT_HCI_OP_READ_RSSI, buf, &rsp);
    if (err) {
        LOG_ERR("Read RSSI err: %d", err);
        return;
    }

    rp = (void *)rsp->data;
    *rssi = rp->rssi;

    net_buf_unref(rsp);
}

static void set_tx_power(uint8_t handle_type, uint16_t handle, int8_t tx_pwr_lvl)
{
    struct bt_hci_cp_vs_write_tx_power_level *cp;
    struct bt_hci_rp_vs_write_tx_power_level *rp;
    struct net_buf *buf, *rsp = NULL;
    int err;

    buf = bt_hci_cmd_create(BT_HCI_OP_VS_WRITE_TX_POWER_LEVEL, sizeof(*cp));
    if (!buf) {
        LOG_WRN("Unable to allocate command buffer");
        return;
    }

    cp = net_buf_add(buf, sizeof(*cp));
    cp->handle = sys_cpu_to_le16(handle);
    cp->handle_type = handle_type;
    cp->tx_power_level = tx_pwr_lvl;

    err = bt_hci_cmd_send_sync(BT_HCI_OP_VS_WRITE_TX_POWER_LEVEL, buf, &rsp);
    if (err) {
        LOG_ERR("Set Tx power err: %d", err);
        return;
    }

    rp = (void *)rsp->data;
    LOG_INF("Actual Tx Power: %d", rp->selected_tx_power);

    net_buf_unref(rsp);
}

static void get_tx_power(uint8_t handle_type, uint16_t handle, int8_t *tx_pwr_lvl)
{
    struct bt_hci_cp_vs_read_tx_power_level *cp;
    struct bt_hci_rp_vs_read_tx_power_level *rp;
    struct net_buf *buf, *rsp = NULL;
    int err;

    *tx_pwr_lvl = 0xFF;
    buf = bt_hci_cmd_create(BT_HCI_OP_VS_READ_TX_POWER_LEVEL, sizeof(*cp));
    if (!buf) {
        LOG_WRN("Unable to allocate command buffer");
        return;
    }

    cp = net_buf_add(buf, sizeof(*cp));
    cp->handle = sys_cpu_to_le16(handle);
    cp->handle_type = handle_type;

    err = bt_hci_cmd_send_sync(BT_HCI_OP_VS_READ_TX_POWER_LEVEL, buf, &rsp);
    if (err) {
        LOG_ERR("Read Tx power err: %d", err);
        return;
    }

    rp = (void *)rsp->data;
    *tx_pwr_lvl = rp->tx_power_level;

    net_buf_unref(rsp);
}
// --- END ADDED ---

// Power Mode read callback
static ssize_t power_mode_read_callback(struct bt_conn *conn, const struct bt_gatt_attr *attr,
                                        void *buf, uint16_t len, uint16_t offset)
{
    uint8_t mode = (uint8_t)current_power_mode;
    LOG_DBG("Power mode read: %d", mode);
    return bt_gatt_attr_read(conn, attr, buf, len, offset, &mode, sizeof(mode));
}

// Power Mode write callback
static ssize_t power_mode_write_callback(struct bt_conn *conn, const struct bt_gatt_attr *attr,
                                         const void *buf, uint16_t len, uint16_t offset, uint8_t flags)
{
    if (len != 1) {
        LOG_ERR("Invalid power mode data length: %d", len);
        return BT_GATT_ERR(BT_ATT_ERR_INVALID_ATTRIBUTE_LEN);
    }

    uint8_t mode = *((uint8_t *)buf);

    if (mode >= 3) {  // We have 3 modes: 0, 1, 2
        LOG_ERR("Invalid power mode value: %d", mode);
        return BT_GATT_ERR(BT_ATT_ERR_VALUE_NOT_ALLOWED);
    }

    LOG_INF("Power mode write: %d", mode);

    int err = apply_power_mode((power_mode_t)mode);
    if (err) {
        LOG_ERR("Failed to apply power mode: %d", err);
        return BT_GATT_ERR(BT_ATT_ERR_UNLIKELY);
    }

    return len;
}

// EMS Service definition
BT_GATT_SERVICE_DEFINE(
    ems_service,
    BT_GATT_PRIMARY_SERVICE(&ems_service_uuid.uuid),
    BT_GATT_CHARACTERISTIC(&ems_control_uuid.uuid,
                           (BT_GATT_CHRC_WRITE | BT_GATT_CHRC_WRITE_WITHOUT_RESP | BT_GATT_CHRC_READ),
                           (BT_GATT_PERM_WRITE_ENCRYPT | BT_GATT_PERM_READ_ENCRYPT),
                           ems_read_callback, ems_write_cb, NULL),
    BT_GATT_CHARACTERISTIC(&ems_session_uuid.uuid,
                           (BT_GATT_CHRC_READ | BT_GATT_CHRC_WRITE | BT_GATT_CHRC_WRITE_WITHOUT_RESP),
                           (BT_GATT_PERM_WRITE_ENCRYPT | BT_GATT_PERM_READ_ENCRYPT),
                           ems_read_callback, ems_write_cb, NULL),
    BT_GATT_CHARACTERISTIC(&pwm_period_uuid.uuid,
                           (BT_GATT_CHRC_READ | BT_GATT_CHRC_WRITE | BT_GATT_CHRC_WRITE_WITHOUT_RESP),
                           (BT_GATT_PERM_WRITE_ENCRYPT | BT_GATT_PERM_READ_ENCRYPT),
                           ems_read_callback, ems_write_cb, NULL),
    BT_GATT_CHARACTERISTIC(&pwm_ontime_uuid.uuid,
                           (BT_GATT_CHRC_READ | BT_GATT_CHRC_WRITE | BT_GATT_CHRC_WRITE_WITHOUT_RESP),
                           (BT_GATT_PERM_WRITE_ENCRYPT | BT_GATT_PERM_READ_ENCRYPT),
                           ems_read_callback, ems_write_cb, NULL),
    BT_GATT_CHARACTERISTIC(&pwm_interval_uuid.uuid,
                           (BT_GATT_CHRC_READ | BT_GATT_CHRC_WRITE | BT_GATT_CHRC_WRITE_WITHOUT_RESP),
                           (BT_GATT_PERM_WRITE_ENCRYPT | BT_GATT_PERM_READ_ENCRYPT),
                           ems_read_callback, ems_write_cb, NULL),
    BT_GATT_CHARACTERISTIC(&pwm_duration_uuid.uuid,
                           (BT_GATT_CHRC_READ | BT_GATT_CHRC_WRITE | BT_GATT_CHRC_WRITE_WITHOUT_RESP),
                           (BT_GATT_PERM_WRITE_ENCRYPT | BT_GATT_PERM_READ_ENCRYPT),
                           ems_read_callback, ems_write_cb, NULL),
    BT_GATT_CHARACTERISTIC(&chan0_playback_uuid.uuid,
                           (BT_GATT_CHRC_READ | BT_GATT_CHRC_WRITE | BT_GATT_CHRC_WRITE_WITHOUT_RESP),
                           (BT_GATT_PERM_WRITE_ENCRYPT | BT_GATT_PERM_READ_ENCRYPT),
                           ems_read_callback, ems_write_cb, NULL),
    BT_GATT_CHARACTERISTIC(&chan0_induct_uuid.uuid,
                           (BT_GATT_CHRC_READ | BT_GATT_CHRC_WRITE | BT_GATT_CHRC_WRITE_WITHOUT_RESP),
                           (BT_GATT_PERM_WRITE_ENCRYPT | BT_GATT_PERM_READ_ENCRYPT),
                           ems_read_callback, ems_write_cb, NULL),
    BT_GATT_CHARACTERISTIC(&chan0_on_duration_uuid.uuid,
                           (BT_GATT_CHRC_READ | BT_GATT_CHRC_WRITE | BT_GATT_CHRC_WRITE_WITHOUT_RESP),
                           (BT_GATT_PERM_WRITE_ENCRYPT | BT_GATT_PERM_READ_ENCRYPT),
                           ems_read_callback, ems_write_cb, NULL),
    BT_GATT_CHARACTERISTIC(&chan0_duration_uuid.uuid,
                           (BT_GATT_CHRC_READ | BT_GATT_CHRC_WRITE | BT_GATT_CHRC_WRITE_WITHOUT_RESP),
                           (BT_GATT_PERM_WRITE_ENCRYPT | BT_GATT_PERM_READ_ENCRYPT),
                           ems_read_callback, ems_write_cb, NULL),
    BT_GATT_CHARACTERISTIC(&chan23_duration_uuid.uuid,
                           (BT_GATT_CHRC_READ | BT_GATT_CHRC_WRITE | BT_GATT_CHRC_WRITE_WITHOUT_RESP),
                           (BT_GATT_PERM_WRITE_ENCRYPT | BT_GATT_PERM_READ_ENCRYPT),
                           ems_read_callback, ems_write_cb, NULL),
    BT_GATT_CHARACTERISTIC(&chan23_on_duration_uuid.uuid,
                           (BT_GATT_CHRC_READ | BT_GATT_CHRC_WRITE | BT_GATT_CHRC_WRITE_WITHOUT_RESP),
                           (BT_GATT_PERM_WRITE_ENCRYPT | BT_GATT_PERM_READ_ENCRYPT),
                           ems_read_callback, ems_write_cb, NULL),
    BT_GATT_CHARACTERISTIC(&charger_on_off_uuid.uuid,
                           (BT_GATT_CHRC_READ | BT_GATT_CHRC_WRITE | BT_GATT_CHRC_WRITE_WITHOUT_RESP),
                           (BT_GATT_PERM_WRITE_ENCRYPT | BT_GATT_PERM_READ_ENCRYPT),
                           ems_read_callback, ems_write_cb, NULL),
    BT_GATT_CHARACTERISTIC(&charger_uuid.uuid,
                           BT_GATT_CHRC_READ,  // Read-only
                           BT_GATT_PERM_READ_ENCRYPT,  // Read permission with encryption
                           charger_read_callback, NULL, NULL),
);

// Battery Service definition
BT_GATT_SERVICE_DEFINE(
    battery_service,
    BT_GATT_PRIMARY_SERVICE(&batt_service_uuid.uuid),
    BT_GATT_CHARACTERISTIC(&batt_val_uuid.uuid,
                           BT_GATT_CHRC_READ | BT_GATT_CHRC_NOTIFY,
                           BT_GATT_PERM_READ_ENCRYPT,
                           batt_read_callback, NULL, NULL),
    BT_GATT_CCC(batt_ccc_value_changed, BT_GATT_PERM_READ_ENCRYPT | BT_GATT_PERM_WRITE),
    // New battery voltage read-only characteristic
     // New read callback
);

// --- Your MODIFIED service definition ---
BT_GATT_SERVICE_DEFINE(ppg_service,

    // Define the PPG Primary Service
    BT_GATT_PRIMARY_SERVICE(&ppg_service_uuid.uuid),

    // Characteristic 1: PPG Control (Write-only)
    BT_GATT_CHARACTERISTIC(&ppg_control_char_uuid.uuid,
                           BT_GATT_CHRC_WRITE,
                           BT_GATT_PERM_WRITE,
                           NULL,
                           on_ppg_control_write, // Your write callback
                           NULL),
    BT_GATT_CUD("PPG Control", BT_GATT_PERM_READ),

    // Characteristic 2: PPG Data (Notify-only)
    BT_GATT_CHARACTERISTIC(&ppg_data_char_uuid.uuid,
                           BT_GATT_CHRC_NOTIFY,
                           BT_GATT_PERM_NONE, // No read/write on the value itself
                           NULL, NULL, NULL),
    // Add the CCC (Client Characteristic Configuration)
    BT_GATT_CCC(on_ppg_ccc_changed,
                BT_GATT_PERM_READ | BT_GATT_PERM_WRITE),
    BT_GATT_CUD("PPG Data", BT_GATT_PERM_READ),

    // Characteristic 3: HRV Features (Notify-only)
    BT_GATT_CHARACTERISTIC(&ppg_hrv_features_char_uuid.uuid,
                           BT_GATT_CHRC_NOTIFY,
                           BT_GATT_PERM_NONE,
                           NULL, NULL, NULL),
    BT_GATT_CCC(on_hrv_features_ccc_changed,
                BT_GATT_PERM_READ | BT_GATT_PERM_WRITE),
    BT_GATT_CUD("HRV Features", BT_GATT_PERM_READ)
);

/******************************************************************************
 *                     FLASH DATA SERVICE DEFINITION                          *
 ******************************************************************************/
/*
 * Flash Data Service allows reading stored PPG data from flash over BLE.
 *
 * Characteristics:
 * 1. Flash Control (Write): Write [offset(4), count(2)] to request data
 * 2. Flash Data (Notify): Receives flash data in chunks
 * 3. Flash Status (Read): Read [offset(4), count(4), available(1)]
 */
BT_GATT_SERVICE_DEFINE(flash_data_service,

    // Primary Service
    BT_GATT_PRIMARY_SERVICE(&flash_service_uuid.uuid),

    // Characteristic 1: Flash Control (Write-only)
    BT_GATT_CHARACTERISTIC(&flash_control_char_uuid.uuid,
                           BT_GATT_CHRC_WRITE,
                           BT_GATT_PERM_WRITE,
                           NULL,
                           on_flash_control_write,
                           NULL),
    BT_GATT_CUD("Flash Control", BT_GATT_PERM_READ),

    // Characteristic 2: Flash Data (Notify-only)
    BT_GATT_CHARACTERISTIC(&flash_data_char_uuid.uuid,
                           BT_GATT_CHRC_NOTIFY,
                           BT_GATT_PERM_NONE,
                           NULL, NULL, NULL),
    BT_GATT_CCC(on_flash_data_ccc_changed,
                BT_GATT_PERM_READ | BT_GATT_PERM_WRITE),
    BT_GATT_CUD("Flash Data", BT_GATT_PERM_READ),

    // Characteristic 3: Flash Status (Read-only)
    BT_GATT_CHARACTERISTIC(&flash_status_char_uuid.uuid,
                           BT_GATT_CHRC_READ,
                           BT_GATT_PERM_READ,
                           on_flash_status_read,
                           NULL,
                           NULL),
    BT_GATT_CUD("Flash Status", BT_GATT_PERM_READ)
);

/* Current Time Service Declaration */
BT_GATT_SERVICE_DEFINE(cts_svc,
    BT_GATT_PRIMARY_SERVICE(BT_UUID_CTS),
    BT_GATT_CHARACTERISTIC(BT_UUID_CTS_CURRENT_TIME,
                          BT_GATT_CHRC_READ | BT_GATT_CHRC_WRITE | BT_GATT_CHRC_NOTIFY,
                          BT_GATT_PERM_READ | BT_GATT_PERM_WRITE,
                          read_current_time, write_current_time, &current_time),
    BT_GATT_CCC(current_time_ccc_cfg_changed,
                BT_GATT_PERM_READ | BT_GATT_PERM_WRITE),
);


// Add the Charger Battery Service definition
BT_GATT_SERVICE_DEFINE(
    charger_battery_service,
    BT_GATT_PRIMARY_SERVICE(&charger_batt_service_uuid.uuid),
    BT_GATT_CHARACTERISTIC(&charger_batt_percent_uuid.uuid,
                           BT_GATT_CHRC_READ | BT_GATT_CHRC_NOTIFY,
                           BT_GATT_PERM_READ_ENCRYPT,
                           charger_batt_read_callback, NULL, NULL),
                           // User description for the characteristic
    BT_GATT_CUD("Charger Battery Level", BT_GATT_PERM_READ),
    BT_GATT_CCC(charger_batt_ccc_value_changed, BT_GATT_PERM_READ_ENCRYPT | BT_GATT_PERM_WRITE),
);

// Power Mode Service definition
BT_GATT_SERVICE_DEFINE(
    power_mode_service,
    BT_GATT_PRIMARY_SERVICE(&power_mode_service_uuid.uuid),
    BT_GATT_CHARACTERISTIC(&power_mode_char_uuid.uuid,
                           BT_GATT_CHRC_READ | BT_GATT_CHRC_WRITE,
                           BT_GATT_PERM_READ | BT_GATT_PERM_WRITE,
                           power_mode_read_callback, power_mode_write_callback, NULL),
    BT_GATT_CUD("Power Mode (0=Sleep, 1=Average, 2=High)", BT_GATT_PERM_READ),
);

// Fuel Gauge Service definition
BT_GATT_SERVICE_DEFINE(
    fuel_gauge_service,
    BT_GATT_PRIMARY_SERVICE(&fuel_gauge_service_uuid.uuid),

    // Time To Empty characteristic (Read + Notify)
    BT_GATT_CHARACTERISTIC(&fuel_gauge_tte_uuid.uuid,
                           BT_GATT_CHRC_READ | BT_GATT_CHRC_NOTIFY,
                           BT_GATT_PERM_READ_ENCRYPT,
                           fuel_gauge_tte_read_callback, NULL, NULL),
    BT_GATT_CUD("TTE (seconds)", BT_GATT_PERM_READ),
    BT_GATT_CCC(fuel_gauge_tte_ccc_changed, BT_GATT_PERM_READ_ENCRYPT | BT_GATT_PERM_WRITE),

    // Time To Full characteristic (Read + Notify)
    BT_GATT_CHARACTERISTIC(&fuel_gauge_ttf_uuid.uuid,
                           BT_GATT_CHRC_READ | BT_GATT_CHRC_NOTIFY,
                           BT_GATT_PERM_READ_ENCRYPT,
                           fuel_gauge_ttf_read_callback, NULL, NULL),
    BT_GATT_CUD("TTF (seconds)", BT_GATT_PERM_READ),
    BT_GATT_CCC(fuel_gauge_ttf_ccc_changed, BT_GATT_PERM_READ_ENCRYPT | BT_GATT_PERM_WRITE),

    // Charging Status characteristic (Read + Notify)
    BT_GATT_CHARACTERISTIC(&fuel_gauge_chg_status_uuid.uuid,
                           BT_GATT_CHRC_READ | BT_GATT_CHRC_NOTIFY,
                           BT_GATT_PERM_READ_ENCRYPT,
                           fuel_gauge_chg_status_read_callback, NULL, NULL),
    BT_GATT_CUD("Charge Status (0=Idle,1=Done,2=Trickle,3=CC,4=CV)", BT_GATT_PERM_READ),
    BT_GATT_CCC(fuel_gauge_chg_status_ccc_changed, BT_GATT_PERM_READ_ENCRYPT | BT_GATT_PERM_WRITE),
);


/**
 * @brief Send PPG data via BLE notification.
 *
 * This function is called from the ppg_thread.
 *
 * @param data Pointer to buffer containing packed PPG samples (4 bytes per sample, big-endian)
 * @param length Number of bytes in the buffer (sample_count × 4)
 */
void ble_send_ppg_data(const uint8_t *data, uint16_t length)
{
    // Check if anyone is connected AND if they've enabled notifications
    if (!peer || !ppg_notify_enabled || !data || length == 0) {
        return;
    }

    /* Send the notification with the packed PPG samples.
     * The attribute to notify is the declaration of the characteristic.
     * In the BT_GATT_SERVICE_DEFINE macro above:
     * [0] = Primary Service
     * [1] = Control Characteristic Declaration
     * [2] = Control Characteristic Value
     * [3] = Control CUD
     * [4] = Data Characteristic Declaration <-- This is what we need
     */
    int err = bt_gatt_notify(peer,
                             &ppg_service.attrs[4], // The attribute for the PPG Data Characteristic
                             data,
                             length);
    if (err) {
        /* ENOMEM (-12) means buffers are full - this is expected at high data rates */
        /* We simply drop this packet and continue with the next one */
        if (err != -ENOMEM) {
            LOG_WRN("bt_gatt_notify failed (err %d)", err);
        }
    }
}

/**
 * @brief Send HRV features data via BLE notification
 *
 * Sends the computed HRV features (SQI, HR, SDNN, RMSSD, IBI, Activity)
 * to the connected BLE peer via the HRV Features characteristic.
 *
 * @param data Pointer to the HRV features data buffer (21 bytes)
 * @param length Length of the data buffer
 */
void ble_send_hrv_features_data(const uint8_t *data, uint16_t length)
{
    // Check if anyone is connected AND if they've enabled notifications
    if (!peer || !hrv_features_notify_enabled || !data || length == 0) {
        return;
    }

    /* Send notification to HRV Features characteristic
     * Attribute indices in ppg_service:
     * [0] = Primary Service
     * [1] = Control Characteristic Declaration
     * [2] = Control Characteristic Value
     * [3] = Control CUD
     * [4] = Data Characteristic Declaration
     * [5] = Data Characteristic Value
     * [6] = Data CCC
     * [7] = Data CUD
     * [8] = HRV Features Characteristic Declaration <-- This is what we need
     */
    int err = bt_gatt_notify(peer,
                             &ppg_service.attrs[8], // The attribute for the HRV Features Characteristic
                             data,
                             length);
    if (err) {
        /* ENOMEM (-12) means buffers are full - this is expected at high data rates */
        /* We simply drop this packet and continue with the next one */
        if (err != -ENOMEM) {
            LOG_WRN("bt_gatt_notify (HRV features) failed (err %d)", err);
        }
    }
}

/******************************************************************************
 *                     FLASH DATA SERVICE PUBLIC API                          *
 ******************************************************************************/

/**
 * @brief Set flash parameters for BLE flash data service
 *
 * This function should be called by the PPG module after flash data is written.
 * It updates the flash offset and sample count that will be reported via BLE.
 *
 * @param flash_device Pointer to flash device
 * @param offset Flash offset where data was written
 * @param sample_count Number of samples written
 */
void ble_flash_set_params(const struct device *flash_device, off_t offset, size_t sample_count)
{
    ble_flash_dev = flash_device;
    ble_flash_offset = offset;
    ble_flash_sample_count = sample_count;

    LOG_INF("BLE Flash service updated: offset=0x%06x, count=%u samples",
           (unsigned)offset, (unsigned)sample_count);
}

/**
 * @brief Get flash device pointer
 *
 * @return Pointer to flash device or NULL if not set
 */
const struct device *ble_flash_get_device(void)
{
    return ble_flash_dev;
}

/**
 * @brief Get current flash parameters
 *
 * @param offset Pointer to store flash offset (can be NULL)
 * @param sample_count Pointer to store sample count (can be NULL)
 * @return true if flash device is set, false otherwise
 */
bool ble_flash_get_params(off_t *offset, size_t *sample_count)
{
    if (offset) {
        *offset = ble_flash_offset;
    }
    if (sample_count) {
        *sample_count = ble_flash_sample_count;
    }
    return (ble_flash_dev != NULL);
}

/**
 * @brief Set the BLE power mode (public API)
 *
 * This function allows other modules to set the BLE power mode.
 *
 * @param mode The power mode to set (0=Sleep, 1=Average, 2=High Power)
 * @return 0 on success, negative error code on failure
 */
int ble_set_power_mode(ble_power_mode_t mode)
{
    if (mode >= 3) {
        LOG_ERR("Invalid power mode: %d", mode);
        return -EINVAL;
    }

    return apply_power_mode((power_mode_t)mode);
}

/**
 * @brief Get the current BLE power mode (public API)
 *
 * @return The current power mode
 */
ble_power_mode_t ble_get_power_mode(void)
{
    return (ble_power_mode_t)current_power_mode;
}


static void send_time_notification(void)
{
    if (!notify_enabled || !peer) {
        return;
    }

    //update_current_time();
    
    int err = bt_gatt_notify(peer, &cts_svc.attrs[1], 
                            &current_time, sizeof(current_time));
    if (err) {
        printk("Failed to send notification (err %d)\n", err);
    } else {
        printk("Time notification sent: %04u-%02u-%02u %02u:%02u:%02u\n",
               current_time.year, current_time.month, current_time.day,
               current_time.hours, current_time.minutes, current_time.seconds);
    }
}

static void time_update_handler(struct k_timer *timer_id)
{
    // --- NEW LOGIC ---
    // Update the global buffer from the system's real-time clock
    update_current_time_from_system();
    // --- END NEW LOGIC ---

    // send_time_notification() will just read this buffer
    send_time_notification();

    /* * The printk below is now redundant because send_time_notification()
     * also prints. You can remove it if you like.
     */
    // printk("Time notification sent: %04u-%02u-%02u %02u:%02u:%02u\n",
    //        current_time.year, current_time.month, current_time.day,
    //        current_time.hours, current_time.minutes, current_time.seconds);
}

K_TIMER_DEFINE(time_update_timer, time_update_handler, NULL);


// ... (rest of the original functions: update_main_msgq, u8_array_to_u32, all read/write/ccc callbacks, etc.) ...
// Update main message queue
static void update_main_msgq(struct main_msg_data *data) {
    k_msgq_put(&main_msgq, data, K_NO_WAIT);
}

// Convert 4 byte array to 32-bit unsigned integer
static uint32_t u8_array_to_u32(uint8_t *src) {
    uint32_t res = 0;
    res |= src[0];
    res <<= 8;
    res |= src[1];
    res <<= 8;
    res |= src[2];
    res <<= 8;
    res |= src[3];
    return res;
}


// Read callback for EMS service
static ssize_t ems_read_callback(struct bt_conn *conn, const struct bt_gatt_attr *attr, void *buf, uint16_t len, uint16_t offset) {
    LOG_DBG("EMS read");
    if (bt_uuid_cmp(attr->uuid, &ems_session_uuid.uuid) == 0) {
        return bt_gatt_attr_read(conn, attr, buf, len, offset, &ems_session_data.status.session.current_session_len,
                                 sizeof(ems_session_data.status.session.current_session_len));
    } else if (bt_uuid_cmp(attr->uuid, &ems_control_uuid.uuid) == 0) {
        return bt_gatt_attr_read(conn, attr, buf, len, offset, &ems_session_data.status.control,
                                 sizeof(ems_session_data.status.control));

    } else {
        return BT_GATT_ERR(BT_ATT_ERR_ATTRIBUTE_NOT_FOUND);
    }
}

static ssize_t charger_read_callback(struct bt_conn *conn, const struct bt_gatt_attr *attr, void *buf, uint16_t len, uint16_t offset) {
    return bt_gatt_attr_read(conn, attr, buf, len, offset, &charger_state, sizeof(charger_state));
}

// Read callback for battery service
static ssize_t batt_read_callback(struct bt_conn *conn, const struct bt_gatt_attr *attr, void *buf, uint16_t len, uint16_t offset) {
    return bt_gatt_attr_read(conn, attr, buf, len, offset, &batt_percent, sizeof(batt_percent));
}

// Add the read callback implementation
static ssize_t charger_batt_read_callback(struct bt_conn *conn, const struct bt_gatt_attr *attr,
                                          void *buf, uint16_t len, uint16_t offset) {
    LOG_DBG("Charger battery read: %d%%", charger_batt_percent);
    return bt_gatt_attr_read(conn, attr, buf, len, offset, &charger_batt_percent, sizeof(charger_batt_percent));
}

// Fuel gauge read callback implementations
static ssize_t fuel_gauge_tte_read_callback(struct bt_conn *conn, const struct bt_gatt_attr *attr,
                                            void *buf, uint16_t len, uint16_t offset) {
    LOG_DBG("Fuel gauge TTE read: %.0f", (double)fuel_gauge_tte);
    return bt_gatt_attr_read(conn, attr, buf, len, offset, &fuel_gauge_tte, sizeof(fuel_gauge_tte));
}

static ssize_t fuel_gauge_ttf_read_callback(struct bt_conn *conn, const struct bt_gatt_attr *attr,
                                            void *buf, uint16_t len, uint16_t offset) {
    LOG_DBG("Fuel gauge TTF read: %.0f", (double)fuel_gauge_ttf);
    return bt_gatt_attr_read(conn, attr, buf, len, offset, &fuel_gauge_ttf, sizeof(fuel_gauge_ttf));
}

static ssize_t fuel_gauge_chg_status_read_callback(struct bt_conn *conn, const struct bt_gatt_attr *attr,
                                                   void *buf, uint16_t len, uint16_t offset) {
    LOG_DBG("Fuel gauge charging status read: %d", fuel_gauge_charging_status);
    return bt_gatt_attr_read(conn, attr, buf, len, offset, &fuel_gauge_charging_status, sizeof(fuel_gauge_charging_status));
}


// This is a PSEUDO-CODE example. Your function will look different.
// This function is called by the Zephyr BLE stack on a write.


// Write callback for EMS service
static ssize_t ems_write_cb(struct bt_conn *conn, const struct bt_gatt_attr *attr, const void *buf, uint16_t len, uint16_t offset,
                            uint8_t flags) {
    LOG_INF("EMS Data update");

    uint8_t *data = (uint8_t *)buf;
    struct main_msg_data m_data = {
        .src = MAIN_MSG_DATA_SRC_BLE
    };

    if (bt_uuid_cmp(attr->uuid, &ems_control_uuid.uuid) == 0) {
        m_data.data.ble.id = BLE_MSG_ID_EMS_CONTROL;
        m_data.data.ble.data.ems.status.control = *data;
        update_main_msgq(&m_data);
        LOG_INF("EMS Control updated to: %u", *data);
        return len;
    } else if (bt_uuid_cmp(attr->uuid, &ems_session_uuid.uuid) == 0) {
        uint32_t new_value = u8_array_to_u32(data);
        m_data.data.ble.id = BLE_MSG_ID_EMS_SESSION;
        m_data.data.ble.data.ems.status.session.target_session_len = new_value;
        update_main_msgq(&m_data);
        LOG_INF("EMS Session updated to: %u", new_value);
        return len;
    } else if (bt_uuid_cmp(attr->uuid, &pwm_period_uuid.uuid) == 0) {
        m_data.data.ble.id = BLE_MSG_ID_PWM_PERIOD;
        m_data.data.ble.data.ems.status.period = *data;
        update_main_msgq(&m_data);
        LOG_INF("PWM Period updated to: %u", *data);
        return len;
    } else if (bt_uuid_cmp(attr->uuid, &pwm_ontime_uuid.uuid) == 0) {
        m_data.data.ble.id = BLE_MSG_ID_PWM_ONTIME;
        m_data.data.ble.data.ems.status.ontime = *data;
        update_main_msgq(&m_data);
        LOG_INF("PWM On Time updated to: %u", *data);
        return len;
    } else if (bt_uuid_cmp(attr->uuid, &pwm_interval_uuid.uuid) == 0) {
        m_data.data.ble.id = BLE_MSG_ID_PWM_INTERVAL;
        m_data.data.ble.data.ems.status.interval = *data;
        update_main_msgq(&m_data);
        LOG_INF("PWM Interval updated to: %u", *data);
        return len;
    } else if (bt_uuid_cmp(attr->uuid, &pwm_duration_uuid.uuid) == 0) {
        m_data.data.ble.id = BLE_MSG_ID_PWM_DURATION;
        m_data.data.ble.data.ems.status.duration = *data;
        update_main_msgq(&m_data);
        LOG_INF("PWM Duration updated to: %u", *data);
        return len;
    }
    else if (bt_uuid_cmp(attr->uuid, &chan0_playback_uuid.uuid) == 0) {
        m_data.data.ble.id = BLE_MSG_ID_CHAN0_PLAYBACK_COUNT;
        m_data.data.ble.data.ems.status.chan0playback = *data;
        update_main_msgq(&m_data);
        LOG_INF("CHAN0 playback updated to: %u", *data);
        return len;
    }
    else if (bt_uuid_cmp(attr->uuid, &chan0_induct_uuid.uuid) == 0) {
        m_data.data.ble.id = BLE_MSG_ID_CHAN0_INUCT_DURATION;
        m_data.data.ble.data.ems.status.chan0inductor = *data;
        update_main_msgq(&m_data);
        LOG_INF("CHAN0 INUCTOR updated to: %u", *data);
        return len;
    }
    else if (bt_uuid_cmp(attr->uuid, &chan0_on_duration_uuid.uuid) == 0) {
        m_data.data.ble.id = BLE_MSG_ID_CHAN0_ON_DURATION;
        m_data.data.ble.data.ems.status.chan0ontime = *data;
        update_main_msgq(&m_data);
        LOG_INF("CHAN0 Duration updated to: %u", *data);
        return len;
    }
    else if (bt_uuid_cmp(attr->uuid, &chan0_duration_uuid.uuid) == 0) {
        m_data.data.ble.id = BLE_MSG_ID_CHAN0_DURATION;
        m_data.data.ble.data.ems.status.chan0time = *data;
        update_main_msgq(&m_data);
        LOG_INF("CHAN0 ON_Duration updated to: %u", *data);
        return len;
    }

        else if (bt_uuid_cmp(attr->uuid, &chan23_duration_uuid.uuid) == 0) {
        m_data.data.ble.id = BLE_MSG_ID_CHAN23_PWM_PERIOD_NS;
        m_data.data.ble.data.ems.status.pwm23time = *data;
        update_main_msgq(&m_data);
        LOG_INF("PWM_23 Duration updated to: %u", *data);
        return len;
    }
    else if (bt_uuid_cmp(attr->uuid, &chan23_on_duration_uuid.uuid) == 0) {
        m_data.data.ble.id = BLE_MSG_ID_CHAN23_PWM_ON_TIME_NS;
        m_data.data.ble.data.ems.status.pwm23ontime = *data;
        update_main_msgq(&m_data);
        LOG_INF("PWM_23 ON_Duration updated to: %u", *data);
        return len;
    }

    else if (bt_uuid_cmp(attr->uuid, &charger_on_off_uuid.uuid) == 0) {
        m_data.data.ble.id = BLE_MSG_ID_CHARGER_ON_OFF;
        m_data.data.ble.data.ems.status.chargeronoff = *data;
        update_main_msgq(&m_data);
        LOG_INF("CHARGER ON OFF updated to: %u", *data);


        return len;
    }

    LOG_ERR("Unsupported EMS attribute");
    return BT_GATT_ERR(BT_ATT_ERR_NOT_SUPPORTED);
}

// CCC value changed callback for battery service
static void batt_ccc_value_changed(const struct bt_gatt_attr *attr, uint16_t value) {

    if (value & BT_GATT_CCC_NOTIFY) {
        //LOG_INF("BATT notifications enabled");
    } else {
        //LOG_INF("BATT notifications disabled");
    }
}

// Add the CCC value changed callback implementation
static void charger_batt_ccc_value_changed(const struct bt_gatt_attr *attr, uint16_t value) {
    if (value & BT_GATT_CCC_NOTIFY) {
        LOG_INF("Charger battery notifications enabled");
    } else {
        LOG_INF("Charger battery notifications disabled");
    }
}

// Fuel gauge CCC changed callback implementations
static void fuel_gauge_tte_ccc_changed(const struct bt_gatt_attr *attr, uint16_t value) {
    fuel_gauge_tte_notify_enabled = (value & BT_GATT_CCC_NOTIFY) != 0;
    if (fuel_gauge_tte_notify_enabled) {
        LOG_INF("Fuel gauge TTE notifications enabled");
    } else {
        LOG_INF("Fuel gauge TTE notifications disabled");
    }
}

static void fuel_gauge_ttf_ccc_changed(const struct bt_gatt_attr *attr, uint16_t value) {
    fuel_gauge_ttf_notify_enabled = (value & BT_GATT_CCC_NOTIFY) != 0;
    if (fuel_gauge_ttf_notify_enabled) {
        LOG_INF("Fuel gauge TTF notifications enabled");
    } else {
        LOG_INF("Fuel gauge TTF notifications disabled");
    }
}

static void fuel_gauge_chg_status_ccc_changed(const struct bt_gatt_attr *attr, uint16_t value) {
    fuel_gauge_chg_status_notify_enabled = (value & BT_GATT_CCC_NOTIFY) != 0;
    if (fuel_gauge_chg_status_notify_enabled) {
        LOG_INF("Fuel gauge charging status notifications enabled");
    } else {
        LOG_INF("Fuel gauge charging status notifications disabled");
    }
}


static void bond_cnt_cb(const struct bt_bond_info *info, void *user_data)
{
    size_t *cnt = user_data;

    (*cnt)++;
}

static size_t bond_cnt(void)
{
    size_t cnt = 0;

    bt_foreach_bond(BT_ID_DEFAULT, bond_cnt_cb, &cnt);

    return cnt;
}

static bool can_pair(void)
{
    return (bond_cnt() < CONFIG_BT_MAX_PAIRED);
}

static void advertising_stop(void)
{
    int ret = k_work_cancel_delayable(&fp_disc_adv_timeout);

    __ASSERT_NO_MSG((ret & ~(K_WORK_CANCELING)) == 0);

    ret = bt_adv_helper_adv_stop();
    if (ret) {
        LOG_ERR("Failed to stop advertising (err %d)", ret);
    }
}

static void advertising_start(void)
{
    int err;
    int ret;

    ARG_UNUSED(ret);

    if (!can_pair()) {
        if ((fp_adv_mode == BT_FAST_PAIR_ADV_MODE_DISC) || show_ui_pairing) {
            LOG_INF("Automatically switching to not discoverable advertising, hide UI "
                "indication, because all bond slots are taken");
            fp_adv_mode = BT_FAST_PAIR_ADV_MODE_DISC;
            show_ui_pairing = false;

            ret = k_work_reschedule(&fp_adv_mode_status_led_handle, K_NO_WAIT);
            __ASSERT_NO_MSG((ret == 0) || (ret == 1));
        }
    }

    bt_le_adv_prov_fast_pair_show_ui_pairing(show_ui_pairing);

    err = bt_adv_helper_adv_start((fp_adv_mode == BT_FAST_PAIR_ADV_MODE_DISC), new_adv_session);

    new_adv_session = false;

    ret = k_work_cancel_delayable(&fp_disc_adv_timeout);

    /* The advertising_start function may be called from discoverable advertising timeout work
     * handler. In that case work would initially be in a running state.
     */
    __ASSERT_NO_MSG((ret & ~(K_WORK_RUNNING | K_WORK_CANCELING)) == 0);

    if ((fp_adv_mode == BT_FAST_PAIR_ADV_MODE_DISC) && !err) {
        ret = k_work_reschedule(&fp_disc_adv_timeout,
                        K_MINUTES(FP_DISC_ADV_TIMEOUT_MINUTES));

        __ASSERT_NO_MSG(ret == 1);
    }

    if (!err) {
        if (fp_adv_mode == BT_FAST_PAIR_ADV_MODE_DISC) {
            LOG_INF("Discoverable advertising started");
        } else {
            LOG_INF("Not discoverable advertising started, %s UI indication enabled",
                show_ui_pairing ? "show" : "hide");
        }
    } else {
        LOG_ERR("Advertising failed to start (err %d)", err);
    }
}

static void bt_adv_restart_fn(struct k_work *w)
{
    advertising_start();
}

static void fp_adv_mode_status_led_handle_fn(struct k_work *w)
{
    ARG_UNUSED(w);

    static bool led_on = true;
    int ret;

    ARG_UNUSED(ret);

    switch (fp_adv_mode) {
    case BT_FAST_PAIR_ADV_MODE_DISC:
        //dk_set_led_on(FP_ADV_MODE_STATUS_LED);
        break;

    case BT_FAST_PAIR_ADV_MODE_NOT_DISC:
        //dk_set_led(FP_ADV_MODE_STATUS_LED, led_on);
        led_on = !led_on;
        ret = k_work_reschedule(&fp_adv_mode_status_led_handle, show_ui_pairing ?
            K_MSEC(FP_ADV_MODE_SHOW_UI_INDICATION_LED_BLINK_INTERVAL_MS) :
            K_MSEC(FP_ADV_MODE_HIDE_UI_INDICATION_LED_BLINK_INTERVAL_MS));
        __ASSERT_NO_MSG(ret == 1);
        break;

    default:
        __ASSERT_NO_MSG(false);
    }
}

static void fp_disc_adv_timeout_fn(struct k_work *w)
{
    ARG_UNUSED(w);

    __ASSERT_NO_MSG(fp_adv_mode == BT_FAST_PAIR_ADV_MODE_DISC);
    __ASSERT_NO_MSG(!peer);

    LOG_INF("Discoverable advertising timed out");

    /* Switch to not discoverable advertising showing UI indication. */
    fp_adv_mode = BT_FAST_PAIR_ADV_MODE_DISC;
    show_ui_pairing = true;

    fp_adv_mode_status_led_handle_fn(NULL);
    advertising_start();
}

/* STEP 7.1 - Define the function to update the connection's PHY */
/* REVISED STEP 1: A dynamic function to update the connection's PHY */
static void update_phy(struct bt_conn *conn, phy_type_t new_phy)
{
    int err;
    struct bt_conn_le_phy_param preferred_phy = {
        .options = BT_CONN_LE_PHY_OPT_NONE,
        .pref_rx_phy = 0, // Will be set in the switch
        .pref_tx_phy = 0, // Will be set in the switch
    };

    switch (new_phy) {
        case PHY_1M:
            LOG_INF("Requesting 1M PHY...");
            preferred_phy.pref_rx_phy = BT_GAP_LE_PHY_1M;
            preferred_phy.pref_tx_phy = BT_GAP_LE_PHY_1M;
            break;
        case PHY_2M:
            LOG_INF("Requesting 2M PHY...");
            preferred_phy.pref_rx_phy = BT_GAP_LE_PHY_2M;
            preferred_phy.pref_tx_phy = BT_GAP_LE_PHY_2M;
            break;
        case PHY_CODED:
            LOG_INF("Requesting Coded PHY (Long Range)...");
            preferred_phy.pref_rx_phy = BT_GAP_LE_PHY_CODED;
            preferred_phy.pref_tx_phy = BT_GAP_LE_PHY_CODED;
            break;
        default:
            LOG_WRN("Invalid PHY type requested for update.");
            return;
    }

    err = bt_conn_le_phy_update(conn, &preferred_phy);
    if (err) {
        LOG_ERR("bt_conn_le_phy_update() returned %d", err);
    }
}

/* STEP 10 - Define the function to update the connection's data length */
static void update_data_length(struct bt_conn *conn)
{
    int err;
    struct bt_conn_le_data_len_param my_data_len = {
        .tx_max_len = BT_GAP_DATA_LEN_MAX,
        .tx_max_time = BT_GAP_DATA_TIME_MAX,
    };
    err = bt_conn_le_data_len_update(conn, &my_data_len);
    if (err) {
        LOG_ERR("data_len_update failed (err %d)", err);
    }
}

/* STEP 11.1 - Define the function to update the connection's MTU */
static void update_mtu(struct bt_conn *conn)
{
    int err;
    exchange_params.func = exchange_func;

    err = bt_gatt_exchange_mtu(conn, &exchange_params);
    if (err) {
        LOG_ERR("bt_gatt_exchange_mtu failed (err %d)", err);
    }
}


static void request_conn_param_update(void)
{
    struct bt_le_conn_param param;
    int err;

    // Convert milliseconds to the 1.25ms units required by the stack
    // For a fixed interval, min and max are the same.
    uint16_t interval_units = (uint16_t)(current_interval_ms / 1.25);
    param.interval_min = interval_units;
    param.interval_max = interval_units;
    param.latency = 3;
    param.timeout = 400; // 4 second supervision timeout

    err = bt_conn_le_param_update(peer, &param);
    if (err) {
        LOG_ERR("Connection parameter update request failed (err %d)", err);
    } else {
        LOG_INF("Requested new connection interval: %d ms", current_interval_ms);
    }
}

/**
 * @brief Apply a power mode configuration to the BLE connection
 *
 * This function configures all BLE parameters (PHY, connection interval,
 * TX power, latency) according to the selected power mode.
 *
 * @param mode The power mode to apply (SLEEP, AVERAGE, or HIGH_POWER)
 * @return 0 on success, negative error code on failure
 */
static int apply_power_mode(power_mode_t mode)
{
    if (mode >= sizeof(power_mode_configs) / sizeof(power_mode_configs[0])) {
        LOG_ERR("Invalid power mode: %d", mode);
        return -EINVAL;
    }

    const ble_power_config_t *config = &power_mode_configs[mode];
    const char *mode_names[] = {"SLEEP", "AVERAGE_POWER", "HIGH_POWER"};

    LOG_INF("Applying power mode: %s", mode_names[mode]);
    LOG_INF("  PHY: %d, Interval: %d ms, TX Power: %d dBm, Latency: %d, Timeout: %d",
            config->phy, config->conn_interval_ms, config->tx_power_dbm,
            config->latency, config->timeout);

    // Update the current power mode
    current_power_mode = mode;

    // Update connection interval
    current_interval_ms = config->conn_interval_ms;

    // If we have an active connection, apply the changes
    if (peer != NULL) {
        int err;
        struct bt_le_conn_param param;

        // Update connection parameters
        uint16_t interval_units = (uint16_t)(config->conn_interval_ms / 1.25);
        param.interval_min = interval_units;
        param.interval_max = interval_units;
        param.latency = config->latency;
        param.timeout = config->timeout;

        err = bt_conn_le_param_update(peer, &param);
        if (err) {
            LOG_ERR("Failed to update connection parameters (err %d)", err);
            return err;
        }

        // Update PHY
        update_phy(peer, config->phy);

        // Update TX power
        uint16_t handle;
        err = bt_hci_get_conn_handle(peer, &handle);
        if (err) {
            LOG_ERR("Failed to get connection handle (err %d)", err);
        } else {
            set_tx_power(BT_HCI_VS_LL_HANDLE_TYPE_CONN, handle, config->tx_power_dbm);
        }

        LOG_INF("Power mode %s applied successfully", mode_names[mode]);
    } else {
        LOG_INF("Power mode %s will be applied on next connection", mode_names[mode]);
    }

    return 0;
}

/**
 * @brief Get the current power mode
 * @return The current power mode
 */
static power_mode_t get_current_power_mode(void)
{
    return current_power_mode;
}


static void connected(struct bt_conn *conn, uint8_t err)
{
    int ret = k_work_cancel_delayable(&fp_disc_adv_timeout);

    __ASSERT_NO_MSG(ret == 0);
    ret = k_work_cancel(&bt_adv_restart);
    __ASSERT_NO_MSG(ret == 0);
    ARG_UNUSED(ret);

    /* Multiple simultaneous connections are not supported by the sample. */
    __ASSERT_NO_MSG(!peer);

    if (err) {
        LOG_WRN("Connection failed, err 0x%02x %s", err, bt_hci_err_to_str(err));
        ret = k_work_submit(&bt_adv_restart);
        __ASSERT_NO_MSG(ret == 1);
        return;
    }

    LOG_INF("Connected");

    peer = conn;


    //dk_set_led_on(CON_STATUS_LED);

    // --- ADDED --- Get connection handle for RSSI reading and Tx power control
    ret = bt_hci_get_conn_handle(peer, &peer_handle);
    if (ret) {
        LOG_ERR("Could not get connection handle (err %d)", ret);
    } else {
        LOG_INF("Connection handle is %d", peer_handle);
    }
    // --- END ADDED ---

   


    /* STEP 1.1 - Declare a structure to store the connection parameters */
    struct bt_conn_info info;
    err = bt_conn_get_info(conn, &info);
    if (err) {
        LOG_ERR("bt_conn_get_info() returned %d", err);
        return;
    }
    /* STEP 1.2 - Add the connection parameters to your log */
    double connection_interval = info.le.interval*1.25; // in ms
    uint16_t supervision_timeout = info.le.timeout*10; // in ms
    LOG_INF("Connection parameters: interval %.2f ms, latency %d intervals, timeout %d ms", connection_interval, info.le.latency, supervision_timeout);
    /* STEP 7.2 - Update the PHY mode */
    /* STEP 13.5 - Update the data length and MTU */
    k_sleep(K_MSEC(1000));  // Delay added to avoid link layer collisions.
    update_data_length(conn);
    update_mtu(conn);

     k_sem_give(&connection_sem);
}

static void disconnected(struct bt_conn *conn, uint8_t reason)
{
    LOG_INF("Disconnected, reason 0x%02x %s", reason, bt_hci_err_to_str(reason));

    //dk_set_led_off(CON_STATUS_LED);
    peer = NULL;

    // --- ADDED --- Invalidate the connection handle
    peer_handle = 0;
    // --- END ADDED ---

    /* Cancel any ongoing flash streaming */
    if (flash_stream.active) {
        k_work_cancel_delayable(&flash_stream.work);
        flash_stream.active = false;
        if (flash_stream.conn) {
            bt_conn_unref(flash_stream.conn);
            flash_stream.conn = NULL;
        }
        ppg_resume_after_flash_read();
        LOG_INF("Flash streaming cancelled due to disconnect");
    }

    int ret = k_work_submit(&bt_adv_restart);

    __ASSERT_NO_MSG(ret == 1);
    ARG_UNUSED(ret);

    new_adv_session = true;

}

void on_le_param_updated(struct bt_conn *conn, uint16_t interval, uint16_t latency, uint16_t timeout)
{
    double connection_interval = interval*1.25;         // in ms
    uint16_t supervision_timeout = timeout*10;          // in ms
    LOG_INF("Connection parameters updated: interval %.2f ms, latency %d intervals, timeout %d ms", connection_interval, latency, supervision_timeout);
}
/* STEP 8.1 - Write a callback function to inform about updates in the PHY */
/* REVISED STEP 2: Update our state variable when the PHY change is confirmed */
void on_le_phy_updated(struct bt_conn *conn, struct bt_conn_le_phy_info *param)
{
    if (param->tx_phy == BT_CONN_LE_TX_POWER_PHY_1M) {
        LOG_INF("PHY updated. New PHY: 1M");
        current_phy = PHY_1M; // Update state
    } else if (param->tx_phy == BT_CONN_LE_TX_POWER_PHY_2M) {
        LOG_INF("PHY updated. New PHY: 2M");
        current_phy = PHY_2M; // Update state
    } else if (param->tx_phy == BT_CONN_LE_TX_POWER_PHY_CODED_S8) {
        LOG_INF("PHY updated. New PHY: Coded (Long Range)");
        current_phy = PHY_CODED; // Update state
    }

    phy_update_pending = false; // <-- CLEAR FLAG AFTER COMPLETION
}

void modulate_tx_power(void *p1, void *p2, void *p3)
{
    int8_t txp_get = 0;
    uint8_t idx = 0;
    int8_t current_tx_power = 127; 

    while (1) {
        if (!peer) {
            /* --- Disconnected State --- */
            printk("Advertising... waiting for connection or 60s timeout.\n");
            
            /* Reset state variables on disconnect */
            current_tx_power = 127; 
            current_phy = PHY_UNKNOWN; // <-- ADD THIS RESET
            stable_rssi_count = 0; // <-- ADD THIS RESET
            candidate_phy = PHY_UNKNOWN; // <-- ADD THIS RESET

            int ret = k_sem_take(&connection_sem, K_SECONDS(60));

            if (ret == -EAGAIN) { 
                printk("60s timeout. Changing advertising power.\n");
                printk("Set Tx power level to %d\n", txpower[idx]);
                set_tx_power(BT_HCI_VS_LL_HANDLE_TYPE_ADV, 0, txpower[idx]);
                idx = (idx + 1) % DEVICE_BEACON_TXPOWER_NUM;

                	/* 2. Only change interval and restart advertising if NOT in discoverable mode
				 * to comply with the Fast Pair specification.
				 */
				if (fp_adv_mode != BT_FAST_PAIR_ADV_MODE_DISC) {
                    /* Stop advertising to apply new parameters */
				    advertising_stop();
					printk("Non-discoverable mode: Increasing advertising interval.\n");
					bt_adv_helper_increase_interval();
					advertising_start();
				}
                
            } else if (ret == 0) {
                printk("Connection occurred, initial setup in progress.\n");
            }
        } else {
            /* --- Connected State: Adapt Tx power AND PHY based on RSSI --- */
            int8_t rssi = 0xFF;
            read_conn_rssi(peer_handle, &rssi);
            printk("Connected (%d) - RSSI = %d, Current PHY = %d\n",
                   peer_handle, rssi, current_phy);

                     // Increment the desired interval by 30ms
            // current_interval_ms += 30;

            // // If it exceeds the max, reset it back to the start
            // if (current_interval_ms > 250) {
            //     current_interval_ms = 30; // Reset to 30ms
            // }

            // // Call our function to send the update request
            // request_conn_param_update();

            /* --- NEW: Adaptive PHY Logic --- */
            phy_type_t desired_phy;
            if (rssi > -90) {
                // Signal is strong, prefer high speed
                desired_phy = PHY_2M;
            } else {
                // Signal is weaker, prefer stability/range
                desired_phy = PHY_1M;
            }

             if (desired_phy == candidate_phy) {
                // The desired PHY is consistent, increment counter
                if (stable_rssi_count < PHY_SWITCH_THRESHOLD) {
                    stable_rssi_count++;
                }
            } else {
                // The desired PHY has changed, reset counter and set new candidate
                stable_rssi_count = 1;
                candidate_phy = desired_phy;
            }

              /* Only request an update if:
             * 1. The RSSI has been stable for the required time.
             * 2. No other update is currently pending.
             * 3. The stable candidate is different from our actual current PHY.
             */
            if ((stable_rssi_count >= PHY_SWITCH_THRESHOLD) &&
                !phy_update_pending &&
                (candidate_phy != current_phy)) {
                
                phy_update_pending = true;
                update_phy(peer, candidate_phy);
            }
            
            

            /* --- END of Adaptive PHY Logic --- */

            // (Your existing adaptive Tx power logic remains here)
            int8_t txp_adaptive;
            if (rssi > -65) {
                txp_adaptive = 0;
            } else {
                txp_adaptive = 4;
            }

            if (txp_adaptive != current_tx_power) {
                printk("Adaptive Tx power selected = %d (Previous = %d)\n",
                       txp_adaptive, current_tx_power);
                set_tx_power(BT_HCI_VS_LL_HANDLE_TYPE_CONN,
                             peer_handle, txp_adaptive);
                current_tx_power = txp_adaptive;
            }

            /* Check connection status every second */
            k_sleep(K_SECONDS(1));
        }
    }
}

/* STEP 13.1 - Write a callback function to inform about updates in data length */
void on_le_data_len_updated(struct bt_conn *conn, struct bt_conn_le_data_len_info *info)
{
    uint16_t tx_len     = info->tx_max_len;
    uint16_t tx_time    = info->tx_max_time;
    uint16_t rx_len     = info->rx_max_len;
    uint16_t rx_time    = info->rx_max_time;
    LOG_INF("Data length updated. Length %d/%d bytes, time %d/%d us", tx_len, rx_len, tx_time, rx_time);
}

static void security_changed(struct bt_conn *conn, bt_security_t level, enum bt_security_err err)
{
    char addr[BT_ADDR_LE_STR_LEN];

    bt_addr_le_to_str(bt_conn_get_dst(conn), addr, sizeof(addr));

    if (!err) {
        LOG_INF("Security changed: %s level %u", addr, level);
    } else {
        LOG_WRN("Security failed: %s level %u err %d %s", addr, level, err,
            bt_security_err_to_str(err));

        /* =================== MODIFIED LOGIC START =================== */
        /*
         * If security fails, it's very likely the peer (phone) has
         * deleted its bond. We should remove our side of the bond
         * and make the device discoverable again to allow re-pairing.
         */
        int unpair_err = bt_unpair(BT_ID_DEFAULT, bt_conn_get_dst(conn));

        if (unpair_err) {
            LOG_ERR("Failed to unpair after security error (err %d)", unpair_err);
        } else {
            LOG_INF("Unpaired from %s due to security failure. Entering discoverable mode.",
                addr);

            /* Set the mode to discoverable for the next advertising session */
            fp_adv_mode = BT_FAST_PAIR_ADV_MODE_DISC;
            show_ui_pairing = true;

            /* Update the status LED to reflect the new mode immediately. */
            int ret = k_work_reschedule(&fp_adv_mode_status_led_handle, K_NO_WAIT);

            __ASSERT_NO_MSG((ret == 0) || (ret == 1));
            ARG_UNUSED(ret);
        }
        /* =================== MODIFIED LOGIC END ===================== */
    }
}

BT_CONN_CB_DEFINE(conn_callbacks) = {
    .connected          = connected,
    .disconnected         = disconnected,
    .security_changed   = security_changed,
    /* STEP 4.1 - Add the callback for connection parameter updates */
    .le_param_updated   = on_le_param_updated,
    /* STEP 8.3 - Add the callback for PHY mode updates */
    .le_phy_updated     = on_le_phy_updated,
    /* STEP 13.2 - Add the callback for data length updates */
    .le_data_len_updated    = on_le_data_len_updated,
};


static void exchange_func(struct bt_conn *conn, uint8_t att_err,
                      struct bt_gatt_exchange_params *params)
{
    LOG_INF("MTU exchange %s", att_err == 0 ? "successful" : "failed");
    if (!att_err) {
        uint16_t payload_mtu = bt_gatt_get_mtu(conn) - 3;   // 3 bytes used for Attribute headers.
        LOG_INF("New MTU: %d bytes", payload_mtu);
    }
}



static void pairing_complete(struct bt_conn *conn, bool bonded)
{
    if (bonded && (fp_adv_mode == BT_FAST_PAIR_ADV_MODE_DISC)) {
        fp_adv_mode = BT_FAST_PAIR_ADV_MODE_DISC;
        show_ui_pairing = true;
        int ret = k_work_reschedule(&fp_adv_mode_status_led_handle, K_NO_WAIT);

        __ASSERT_NO_MSG((ret == 0) || (ret == 1));
        ARG_UNUSED(ret);
    }
}

static enum bt_security_err pairing_accept(struct bt_conn *conn,
                               const struct bt_conn_pairing_feat *const feat)
{
    ARG_UNUSED(conn);
    ARG_UNUSED(feat);

    enum bt_security_err ret;

    if (fp_adv_mode != BT_FAST_PAIR_ADV_MODE_DISC) {
        LOG_WRN("Normal Bluetooth pairing not allowed outside of pairing mode");
        ret = BT_SECURITY_ERR_PAIR_NOT_ALLOWED;
    } else {
        LOG_INF("Accept normal Bluetooth pairing");
        ret = BT_SECURITY_ERR_SUCCESS;
    }

    return ret;
}

// ... (rest of the original functions: volume_change_to_str, hid_volume_control_send, button handlers, etc.) ...
static const char *volume_change_to_str(enum hids_helper_volume_change volume_change)
{
	const char *res = NULL;

	switch (volume_change) {
	case HIDS_HELPER_VOLUME_CHANGE_DOWN:
		res = "Decrease";
		break;

	case HIDS_HELPER_VOLUME_CHANGE_NONE:
		break;

	case HIDS_HELPER_VOLUME_CHANGE_UP:
		res = "Increase";
		break;

	default:
		/* Should not happen. */
		__ASSERT_NO_MSG(false);
		break;
	}

	return res;
}

static void hid_volume_control_send(enum hids_helper_volume_change volume_change)
{
	const char *operation_str = volume_change_to_str(volume_change);
	int err = hids_helper_volume_ctrl(volume_change);

	if (!err) {
		if (operation_str) {
			LOG_INF("%s audio volume", operation_str);
		}
	} else {
		/* HID host not connected or not subscribed. Silently drop HID data. */
	}
}

static void volume_control_btn_handle(uint32_t button_state, uint32_t has_changed)
{
	static enum hids_helper_volume_change volume_change = HIDS_HELPER_VOLUME_CHANGE_NONE;
	enum hids_helper_volume_change new_volume_change = volume_change;

	if (has_changed & VOLUME_UP_BUTTON_MASK) {
		if (button_state & VOLUME_UP_BUTTON_MASK) {
			new_volume_change = HIDS_HELPER_VOLUME_CHANGE_UP;
		} else if (volume_change == HIDS_HELPER_VOLUME_CHANGE_UP) {
			new_volume_change = HIDS_HELPER_VOLUME_CHANGE_NONE;
		}
	}

	if (has_changed & VOLUME_DOWN_BUTTON_MASK) {
		if (button_state & VOLUME_DOWN_BUTTON_MASK) {
			new_volume_change = HIDS_HELPER_VOLUME_CHANGE_DOWN;
		} else if (volume_change == HIDS_HELPER_VOLUME_CHANGE_DOWN) {
			new_volume_change = HIDS_HELPER_VOLUME_CHANGE_NONE;
		}
	}

	if (volume_change != new_volume_change) {
		volume_change = new_volume_change;
		hid_volume_control_send(volume_change);
	}
}

static void fp_adv_mode_btn_handle(uint32_t button_state, uint32_t has_changed)
{
	uint32_t button_pressed = button_state & has_changed;

	if (button_pressed & FP_ADV_MODE_BUTTON_MASK) {
		if (fp_adv_mode == BT_FAST_PAIR_ADV_MODE_DISC) {
			fp_adv_mode = BT_FAST_PAIR_ADV_MODE_DISC;
			show_ui_pairing = true;
		} else {
			if (show_ui_pairing) {
				show_ui_pairing = false;
			} else {
				fp_adv_mode = BT_FAST_PAIR_ADV_MODE_DISC;
			}
		}

		if (!peer) {
			new_adv_session = true;
			advertising_start();
		}

		int ret = k_work_reschedule(&fp_adv_mode_status_led_handle, K_NO_WAIT);

		__ASSERT_NO_MSG((ret == 0) || (ret == 1));
		ARG_UNUSED(ret);
	}
}

static void bond_remove_btn_handle(uint32_t button_state, uint32_t has_changed)
{
	uint32_t button_pressed = button_state & has_changed;

	if (button_pressed & BOND_REMOVE_BUTTON_MASK) {
		advertising_stop();

		int err = bt_unpair(BT_ID_DEFAULT, NULL);

		if (err) {
			LOG_ERR("Cannot remove bonds (err %d)", err);
		} else {
			LOG_INF("Bonds removed");
		}

		if (!peer) {
			new_adv_session = true;
			advertising_start();
		}
	}
}

void bt_adv_restart_init(void)
{

    fp_adv_mode = BT_FAST_PAIR_ADV_MODE_DISC;
    if (!peer) {
			new_adv_session = true;
			advertising_start();
		}
    
}

static void button_changed(uint32_t button_state, uint32_t has_changed)
{
	__ASSERT_NO_MSG(!k_is_in_isr());
	__ASSERT_NO_MSG(!k_is_preempt_thread());

	fp_adv_mode_btn_handle(button_state, has_changed);
	volume_control_btn_handle(button_state, has_changed);
	bond_remove_btn_handle(button_state, has_changed);
}

static void fp_account_key_written(struct bt_conn *conn)
{
	LOG_INF("Fast Pair Account Key has been written");
}

static bool bms_authorize(struct bt_conn *conn,
			  struct bt_bms_authorize_params *params)
{
	if ((params->code_len == sizeof(bms_auth_code)) &&
	    (memcmp(bms_auth_code, params->code, sizeof(bms_auth_code)) == 0)) {
		LOG_INF("Authorization of BMS operation is successful\n");
		return true;
	}

	LOG_INF("Authorization of BMS operation has failed\n");
	return false;
}

static struct bt_bms_cb bms_callbacks = {
	.authorize = bms_authorize,
};

static int bms_init(void)
{
	struct bt_bms_init_params init_params = {0};

	/* Enable all possible operation codes */
	init_params.features.delete_requesting.supported = true;
	init_params.features.delete_rest.supported = true;
	init_params.features.delete_all.supported = true;

	/* Require authorization code for operations that
	 * also delete bonding information for other devices
	 * than the requesting client.
	 */
	init_params.features.delete_rest.authorize = true;
	init_params.features.delete_all.authorize = true;

	init_params.cbs = &bms_callbacks;

	return bt_bms_init(&init_params);
}

/**
 * @brief Saves the current time to flash and prepares for sleep.
 * * CALL THIS from your application logic right before entering deep sleep.
 */
/**
 * @brief Saves the current time and GRTC snapshot to flash.
 * CALL THIS from your application logic right before entering deep sleep.
 */
void prepare_for_sleep(void)
{
    struct persistent_time snapshot;
    int err;

    // 1. Get the current, accurate wall time
    err = clock_gettime(CLOCK_REALTIME, &snapshot.wall_time);
    if (err) {
        LOG_ERR("Failed to get time before sleep (err %d)", err);
        return;
    }

    // 2. Get the current, accurate GRTC ticks using your nrfx function
    nrfx_grtc_syscounter_get(&snapshot.grtc_ticks);

    // 3. Save the *entire snapshot* to flash
    err = settings_save_one("ble/time/time_snapshot", &snapshot, sizeof(snapshot));
    if (err) {
        LOG_ERR("Failed to save time snapshot to flash (err %d)", err);
    } else {
        LOG_INF("Saved time snapshot to flash. Preparing to sleep.");
    }
    
    // 4. (Your application code to enter sleep goes here)
    // LOG_INF("Entering deep sleep...");
}

static void init_work_handle(struct k_work *w)
{
    int err;
    static const struct bt_conn_auth_cb conn_auth_callbacks = {
        .pairing_accept = pairing_accept,
    };
    static struct bt_conn_auth_info_cb auth_info_cb = {
        .pairing_complete = pairing_complete
    };
    static struct bt_fast_pair_info_cb fp_info_callbacks = {
        .account_key_written = fp_account_key_written,
    };

    /* It is assumed that this function executes in the cooperative thread context. */
    __ASSERT_NO_MSG(!k_is_preempt_thread());
    __ASSERT_NO_MSG(!k_is_in_isr());

    err = bt_conn_auth_cb_register(&conn_auth_callbacks);
    if (err) {
        LOG_ERR("Registering authentication callbacks failed (err %d)", err);
        return;
    }

    err = bt_conn_auth_info_cb_register(&auth_info_cb);
    if (err) {
        LOG_ERR("Registering authentication info callbacks failed (err %d)", err);
        return;
    }

    err = bt_fast_pair_info_cb_register(&fp_info_callbacks);
    if (err) {
        LOG_ERR("Registering Fast Pair info callbacks failed (err %d)", err);
        return;
    }

    err = hids_helper_init();
    if (err) {
        LOG_ERR("HIDS init failed (err %d)", err);
        return;
    }

    err = bt_enable(NULL);
    if (err) {
        LOG_ERR("Bluetooth init failed (err %d)", err);
        return;
    }

    LOG_INF("Bluetooth initialized");

    /* Initialize flash data attribute pointer
     * Attribute indices in flash_data_service:
     * [0] = Primary Service
     * [1] = Flash Control CHRC declaration
     * [2] = Flash Control value
     * [3] = Flash Control CUD
     * [4] = Flash Data CHRC declaration
     * [5] = Flash Data value <-- This is what we need for notifications
     */
    flash_data_attr = &flash_data_service.attrs[5];
    LOG_INF("Flash data service initialized");

    err = settings_load();
    if (err) {
        LOG_ERR("Settings load failed (err: %d)", err);
        return;
    }

    LOG_INF("Settings loaded");

// 2. Now, *directly* load our time snapshot
    err = settings_load_subtree_direct("ble/time", time_load_cb, NULL);
    if (err) {
        LOG_ERR("Failed to load time snapshot subtree (err %d)", err);
    }
    
    // 3. The rest of your time-restore logic stays THE SAME
    uint32_t reset_reason;
    err = hwinfo_get_reset_cause(&reset_reason);
    
    if (err == 0 ) {
        if (last_saved_time.wall_time.tv_sec > 0) {
            
            // 1. Get current GRTC ticks
            uint64_t current_ticks;
            nrfx_grtc_syscounter_get(&current_ticks);

            // 2. Get GRTC frequency
            const uint32_t grtc_freq = GRTC_FREQ_HZ;

            // 3. Calculate delta (sleep duration)
            uint64_t delta_ticks = current_ticks - last_saved_time.grtc_ticks;
            
            // 4. Convert delta to timespec
            struct timespec delta_ts;
            delta_ts.tv_sec = delta_ticks / grtc_freq;
            delta_ts.tv_nsec = ((delta_ticks % grtc_freq) * NSEC_PER_SEC) / grtc_freq;

            // 5. Calculate new time
            struct timespec new_time;
            new_time.tv_sec = last_saved_time.wall_time.tv_sec + delta_ts.tv_sec;
            new_time.tv_nsec = last_saved_time.wall_time.tv_nsec; // Add nsec
            if (new_time.tv_nsec >= NSEC_PER_SEC) { // Handle overflow
                new_time.tv_sec++;
                new_time.tv_nsec -= NSEC_PER_SEC;
            }

            // 6. Set the system clock
            err = clock_settime(CLOCK_REALTIME, &new_time);
            if (err) {
                LOG_ERR("Failed to restore system time (err %d)", err);
            } else {
                LOG_INF("System wall clock restored. Sleep duration: %u sec", (uint32_t)delta_ts.tv_sec);
            }

        } else {
            LOG_WRN("Woke from sleep, but no valid time snapshot in flash.");
        }
    } else {
        LOG_INF("Power-on reset, not restoring time. (Reason: 0x%x)", reset_reason);
    }
    // --- END REPLACED/MODIFIED LOGIC ---

    err = bt_fast_pair_enable();
    if (err) {
        LOG_ERR("Fast Pair enable failed (err: %d)", err);
        return;
    }

    // err = dk_leds_init();
    // if (err) {
    //  LOG_ERR("LEDs init failed (err %d)", err);
    //  return;
    // }

    err = battery_module_init();
    if (err) {
        LOG_ERR("Battery module init failed (err %d)", err);
        return;
    }

    err = bt_le_adv_prov_fast_pair_set_battery_mode(BT_FAST_PAIR_ADV_BATTERY_MODE_SHOW_UI_IND);
    if (err) {
        LOG_ERR("Setting advertising battery mode failed (err %d)", err);
        return;
    }

     err = bms_init();

    if (err) {
        printk("Failed to init BMS (err:%d)\n", err);
        return 0;
    }


    k_work_init(&bt_adv_restart, bt_adv_restart_fn);
    k_work_init_delayable(&fp_adv_mode_status_led_handle, fp_adv_mode_status_led_handle_fn);
    k_work_init_delayable(&fp_disc_adv_timeout, fp_disc_adv_timeout_fn);
    k_work_init_delayable(&flash_stream.work, flash_stream_work_handler);

    int ret = k_work_schedule(&fp_adv_mode_status_led_handle, K_NO_WAIT);

    __ASSERT_NO_MSG(ret == 1);
    ret = k_work_submit(&bt_adv_restart);
    __ASSERT_NO_MSG(ret == 1);
    ARG_UNUSED(ret);

    // err = dk_buttons_init(button_changed);
    // if (err) {
    //  LOG_ERR("Buttons init failed (err %d)", err);
    //  return;
    // }

    k_sem_give(&init_work_sem);
}



// BLE thread main function
int ble_thread_main() {

    int err;
    int8_t txp_get = 0xFF;

    struct ble_msg msgq_data;

    register_thread(k_current_get());

   // bt_conn_cb_register(&connection_callbacks);


    bool run_led_on = true;


    LOG_INF("Starting Bluetooth Fast Pair input device sample");

    /* Switch to the cooperative thread context before interaction
     * with the Fast Pair API.
     */
    (void) k_work_submit(&init_work);
    err = k_sem_take(&init_work_sem, K_SECONDS(INIT_SEM_TIMEOUT_SECONDS));
    if (err) {
        k_panic();
        return 0;
    }

    LOG_INF("Sample has started");

    printk("Get Tx power level ->");
    get_tx_power(BT_HCI_VS_LL_HANDLE_TYPE_ADV, 0, &txp_get);
    printk("-> default TXP = %d\n", txp_get);


    // --- ADDED --- Create and start the dynamic Tx power thread
    k_thread_create(&pwr_thread_data, pwr_thread_stack,
                    K_THREAD_STACK_SIZEOF(pwr_thread_stack),
                    modulate_tx_power, NULL, NULL, NULL,
                    K_PRIO_COOP(10), 0, K_NO_WAIT);
    k_thread_name_set(&pwr_thread_data, "DYN_TX_POWER");
    LOG_INF("Dynamic Tx Power thread started");

      /* Start periodic time updates every 60 seconds */
    k_timer_start(&time_update_timer, K_SECONDS(1), K_SECONDS(1));
    // --- END ADDED ---


    while (1) {

            // Update thread health
        heartbeat();


        k_msgq_get(&ble_msgq, &msgq_data, K_FOREVER);

        switch (msgq_data.id) {
            case BLE_MSG_ID_EMS_CONTROL: {
                memcpy(&ems_session_data, &msgq_data.data.ems, sizeof(ems_session_data));
                break;
            }
            case BLE_MSG_ID_BATT_UPDATE: {
                float batt_range = BATT_MAX_VOLTAGE_MV - BATT_MIN_VOLTAGE_MV;
                batt_percent = (uint8_t)(((float)(msgq_data.data.batt_mv) / batt_range) * 100);
                if(batt_percent > 100)
                {
                    batt_percent =100;
                }
              //  LOG_DBG("Batt read, Percent %d", batt_percent);

                if (bt_gatt_is_subscribed(peer, &battery_service.attrs[1], BT_GATT_CCC_NOTIFY)) {
                    bt_gatt_notify(peer, &battery_service.attrs[1], &batt_percent, sizeof(batt_percent));
                } else {
                    //LOG_WRN("BATT notification not enabled");
                }
                break;
            }

            // Add this case in the ble_thread_main() switch statement to handle charger battery updates
case BLE_MSG_ID_CHARGER_BATT_UPDATE: {
    // Assuming the charger battery voltage range (adjust as needed)


    charger_batt_percent = msgq_data.data.charger_batt_mv;



    LOG_DBG("Charger battery read, Percent %d", charger_batt_percent);

    // Notify if subscribed
    if (bt_gatt_is_subscribed(peer, &charger_battery_service.attrs[1], BT_GATT_CCC_NOTIFY)) {
        bt_gatt_notify(peer, &charger_battery_service.attrs[1], &charger_batt_percent, sizeof(charger_batt_percent));
    } else {
        LOG_WRN("Charger battery notification not enabled");
    }
    break;
}

            case BLE_MSG_ID_FUEL_GAUGE_UPDATE: {
                // Update fuel gauge data from message
                fuel_gauge_tte = msgq_data.data.fuel_gauge.tte;
                fuel_gauge_ttf = msgq_data.data.fuel_gauge.ttf;
                fuel_gauge_charging_status = msgq_data.data.fuel_gauge.chg_status;

                // Update battery percentage from SoC
                batt_percent = (uint8_t)msgq_data.data.fuel_gauge.soc;
                if (batt_percent > 100) {
                    batt_percent = 100;
                }

                LOG_DBG("Fuel gauge: SoC=%d%%, TTE=%.0f, TTF=%.0f, Status=%d",
                        batt_percent, (double)fuel_gauge_tte, (double)fuel_gauge_ttf, fuel_gauge_charging_status);

                // Notify battery percentage (standard battery service 0x180F)
                if (bt_gatt_is_subscribed(peer, &battery_service.attrs[1], BT_GATT_CCC_NOTIFY)) {
                    bt_gatt_notify(peer, &battery_service.attrs[1], &batt_percent, sizeof(batt_percent));
                }

                // Notify TTE
                if (bt_gatt_is_subscribed(peer, &fuel_gauge_service.attrs[2], BT_GATT_CCC_NOTIFY)) {
                    bt_gatt_notify(peer, &fuel_gauge_service.attrs[2], &fuel_gauge_tte, sizeof(fuel_gauge_tte));
                }

                // Notify TTF
                if (bt_gatt_is_subscribed(peer, &fuel_gauge_service.attrs[6], BT_GATT_CCC_NOTIFY)) {
                    bt_gatt_notify(peer, &fuel_gauge_service.attrs[6], &fuel_gauge_ttf, sizeof(fuel_gauge_ttf));
                }

                // Notify charging status
                if (bt_gatt_is_subscribed(peer, &fuel_gauge_service.attrs[10], BT_GATT_CCC_NOTIFY)) {
                    bt_gatt_notify(peer, &fuel_gauge_service.attrs[10], &fuel_gauge_charging_status, sizeof(fuel_gauge_charging_status));
                }
                break;
            }

            case BLE_MSG_ID_REINIT: {
                (void)bt_le_adv_stop();
                k_sleep(K_MSEC(100));
                if (bt_disable() == 0) {
                    k_sleep(K_MSEC(100));
                    if (bt_enable(NULL) == 0) {

                        LOG_INF("BLE reinit");
                    }
                }
                break;
            }
            case BLE_MSG_ID_DEINIT: {
                (void)bt_le_adv_stop();
                k_sleep(K_MSEC(100));
                (void)bt_disable();
                k_sleep(K_FOREVER);
                break;
            }
            default: {
                break;
            }
        }
    }

    return 0;
}
K_THREAD_DEFINE(ble_thread, 4096, ble_thread_main, NULL, NULL, NULL, 1, K_ESSENTIAL, 0);