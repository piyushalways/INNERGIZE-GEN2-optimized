#include <zephyr/kernel.h>
#include <zephyr/device.h>
#include <zephyr/drivers/i2c.h>
#include <zephyr/logging/log.h>
#include <zephyr/drivers/flash.h>
#include <zephyr/devicetree.h>

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/
#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <math.h>

#include "as7058_chiplib.h"
#include "as7058_extract.h"
#include "error_codes.h"
#include "ppg.h"
#include "bluetooth_manager.h"
#include "ppg_workspace_f.h"
#include "core_modules_f.h"
#include "utility_f.h"
#include "bma580_features.h"
#include "bma5.h"
#include "stim_logic_f.h"

K_MSGQ_DEFINE(ppg_cmd_q, sizeof(ppg_cmd_t), 10, 4);

/******************************************************************************
 *                    BMA580 ACCELEROMETER CONFIGURATION                      *
 ******************************************************************************/

/*! Earth's gravity in m/s^2 */
#define GRAVITY_EARTH  (9.80665f)

/*! BMA580 I2C address */
#define BMA580_I2C_ADDR  0x18

/* I2C device pointer for BMA580 */
static const struct device *bma_i2c_dev = NULL;

/* BMA580 device structure */
static struct bma5_dev bma_dev;

/******************************************************************************
 *                       FLASH STORAGE CONFIGURATION                          *
 ******************************************************************************/

/* PPG data flash storage configuration */
#define PPG_RAM_BUFFER_SIZE     1024          /* Store 1024 samples = 4KB */
#define PAGE_SIZE               256

/* Define the total flash region for storing all our chunks */
#define DATA_REGION_START_OFFSET 0x000000      /* Start of our data log */
#define DATA_REGION_TOTAL_SIZE  8388608u      /* 8,388,608 bytes (8 MB) total for logging */

/* How much to print */
#define DUMP_HEAD_COUNT         20            /* first N numbers to print */
#define DUMP_TAIL_COUNT         10            /* last  N numbers to print */
#define WRITE_PROGRESS_BYTES    (16u * 1024u) /* print every 16 KiB written */
#define ERASE_CHUNK_BYTES       (32u * 1024u) /* erase in 32 KiB chunks */

/* Devicetree and Sizing */
#if DT_HAS_COMPAT_STATUS_OKAY(nordic_qspi_nor)
#define FLASH_COMPAT nordic_qspi_nor
#elif DT_HAS_COMPAT_STATUS_OKAY(jedec_spi_nor)
#define FLASH_COMPAT jedec_spi_nor
#elif DT_HAS_COMPAT_STATUS_OKAY(jedec_mspi_nor)
#define FLASH_COMPAT jedec_mspi_nor
#else
#warning "No compatible SPI/QSPI NOR flash found - flash storage will be disabled"
#define FLASH_STORAGE_AVAILABLE 0
#endif

#ifndef FLASH_STORAGE_AVAILABLE
#define FLASH_STORAGE_AVAILABLE 1
#endif

#define ROUND_UP(x,a)           ((((x) + ((a) - 1)) / (a)) * (a))

#define PPG_ELEM_SIZE           sizeof(uint32_t)
/* Calculate storage bytes for a *single chunk* of PPG samples */
#define CHUNK_DATA_BYTES        (PPG_RAM_BUFFER_SIZE * PPG_ELEM_SIZE)
#define CHUNK_PAGED_BYTES       ROUND_UP(CHUNK_DATA_BYTES, PAGE_SIZE)

LOG_MODULE_REGISTER(ppg_manager, LOG_LEVEL_INF);

/******************************************************************************
 *                    BLE SERVICE - TWO CHARACTERISTICS                       *
 ******************************************************************************/
/*
 * Data is transmitted via a single BLE service with TWO characteristics:
 *
 * CHARACTERISTIC 1: Raw PPG Data (ble_send_ppg_data)
 *   Format: [SAMPLE1][SAMPLE2]...[SAMPLE_N]
 *   - Each SAMPLE: 4 bytes (int32_t, big-endian)
 *   - Up to 48 samples per packet
 *   - Total size: N × 4 bytes (max 192 bytes)
 *   - Update rate: ~40 Hz (every FIFO threshold)
 *
 * CHARACTERISTIC 2: HRV Features (ble_send_hrv_features_data)
 *   Format: [SQI][HR][SDNN][RMSSD][IBI][ACT]
 *   - SQI:   4 bytes (float, little-endian) - Signal Quality Index (0.0-1.0)
 *   - HR:    4 bytes (float, little-endian) - Heart Rate (BPM)
 *   - SDNN:  4 bytes (float, little-endian) - Std dev of NN intervals (ms)
 *   - RMSSD: 4 bytes (float, little-endian) - Root mean square successive diff (ms)
 *   - IBI:   4 bytes (float, little-endian) - Inter-beat interval mean (ms)
 *   - ACT:   1 byte  (uint8_t) - Activity level
 *   - Total size: 21 bytes
 *   - Update rate: Every 5 seconds
 */

/******************************************************************************
 *                                  GLOBALS                                   *
 ******************************************************************************/

/*! Metadata for storing state of FIFO data extraction. */
static volatile as7058_extract_metadata_t g_extract_metadata;

/*! Sample period of PPG1 and PPG2 signals. */
static volatile double g_ppg_sample_period_s;

/*! The total number of sub-samples received. */
static volatile uint32_t g_sub_sample_cnt[AS7058_SUB_SAMPLE_ID_NUM];

/******************************************************************************
 *                          HRM ALGORITHM GLOBALS                             *
 ******************************************************************************/

/* HRM workspace for processing */
static ppg_workspace_f_t ws;

/* Ring buffers for overlapping window processing */
static float ppg_ring[WIN_SAMP_PPG];
static float ax_ring[WIN_SAMP_ACC];
static float ay_ring[WIN_SAMP_ACC];
static float az_ring[WIN_SAMP_ACC];

/* Ring buffer write indices */
static int ppg_wr = 0;
static int acc_wr = 0;

/* Sample counters */
static int ppg_samples_collected = 0;
static int acc_samples_collected = 0;

/* Processing configuration */
#define STEP_SEC   5
#define STEP_PPG   (STEP_SEC * FS_PPG)
#define STEP_ACC   (STEP_SEC * FS_ACC)

/******************************************************************************
 *                      FLASH STORAGE GLOBALS                                 *
 ******************************************************************************/

#if FLASH_STORAGE_AVAILABLE
/* Flash device pointer */
static const struct device *flash_dev = NULL;

/* RAM Buffer for PPG data */
static uint32_t ppg_ram_buf[PPG_RAM_BUFFER_SIZE];
static size_t ppg_flash_sample_count = 0;

/* Flash write offset */
static off_t current_write_offset = 0;

/* Track total samples written to flash across all chunks */
static uint32_t total_flash_samples_written = 0;

/* Flag to indicate if we should save to flash */
static volatile bool ppg_flash_storage_enabled = false;
static volatile bool ppg_flash_buffer_full = false;

/* Flag to pause PPG processing during flash read operations */
static volatile bool ppg_paused_for_flash_read = false;
#endif

/******************************************************************************
 *                               LOCAL FUNCTIONS                              *
 ******************************************************************************/

/******************************************************************************
 *                     BMA580 INTERFACE FUNCTIONS                             *
 ******************************************************************************/

/*!
 * @brief Zephyr I2C read function for BMA5 driver
 */
static int8_t bma5_i2c_read(uint8_t reg_addr, uint8_t *data, uint32_t len, void *intf_ptr)
{
    int ret;

    if (bma_i2c_dev == NULL) {
        return -1;
    }

    ret = i2c_write_read(bma_i2c_dev, BMA580_I2C_ADDR, &reg_addr, 1, data, len);

    return (ret == 0) ? 0 : -1;
}

/*!
 * @brief Zephyr I2C write function for BMA5 driver
 */
static int8_t bma5_i2c_write(uint8_t reg_addr, const uint8_t *data, uint32_t len, void *intf_ptr)
{
    int ret;
    uint8_t buf[len + 1];

    if (bma_i2c_dev == NULL) {
        return -1;
    }

    buf[0] = reg_addr;
    for (uint32_t i = 0; i < len; i++) {
        buf[i + 1] = data[i];
    }

    ret = i2c_write(bma_i2c_dev, buf, len + 1, BMA580_I2C_ADDR);

    return (ret == 0) ? 0 : -1;
}

/*!
 * @brief Zephyr delay function in microseconds
 */
static void bma5_delay_us(uint32_t period, void *intf_ptr)
{
    k_usleep(period);
}

/*!
 * @brief This internal API converts raw sensor values(LSB) to meters per seconds square.
 *
 *  @param[in] val       : Raw sensor value.
 *  @param[in] g_range   : Accel Range selected (2G, 4G, 8G, 16G).
 *  @param[in] bit_width : Resolution of the sensor.
 *
 *  @return Accel values in meters per second square.
 */
static float lsb_to_ms2(int16_t val, float g_range, uint8_t bit_width)
{
    /* Calculate 2^bit_width / 2 without using pow() */
    float half_scale = (float)(1 << (bit_width - 1));

    return (GRAVITY_EARTH * val * g_range) / half_scale;
}

/*!
 * @brief Initialize BMA5 interface for Zephyr OS
 */
static int8_t bma5_interface_init(struct bma5_dev *dev, uint8_t intf, enum bma5_context context)
{
    /* Get I2C device from device tree */
    bma_i2c_dev = DEVICE_DT_GET(DT_NODELABEL(i2c21));

    if (!device_is_ready(bma_i2c_dev)) {
        LOG_ERR("BMA580: I2C device not ready - accelerometer will be unavailable");
        bma_i2c_dev = NULL;
        return -1;
    }

    LOG_INF("BMA580: I2C device ready");

    /* Configure the BMA5 device structure */
    dev->intf = intf;
    dev->bus_read = bma5_i2c_read;
    dev->bus_write = bma5_i2c_write;
    dev->delay_us = bma5_delay_us;
    dev->intf_ptr = NULL;
    dev->context = context;
    dev->dummy_byte = 0;

    return 0;
}

/******************************************************************************
 *                           RING BUFFER FUNCTIONS                            *
 ******************************************************************************/

/*! Push a PPG sample to the ring buffer */
static inline void ring_push_ppg(float v)
{
    ppg_ring[ppg_wr] = v;
    ppg_wr = (ppg_wr + 1) % WIN_SAMP_PPG;
    if (ppg_samples_collected < WIN_SAMP_PPG)
        ppg_samples_collected++;
}

/*! Push accelerometer sample to the ring buffer */
static inline void ring_push_acc(float x, float y, float z)
{
    ax_ring[acc_wr] = x;
    ay_ring[acc_wr] = y;
    az_ring[acc_wr] = z;
    acc_wr = (acc_wr + 1) % WIN_SAMP_ACC;
    if (acc_samples_collected < WIN_SAMP_ACC)
        acc_samples_collected++;
}

/*! Load window from ring buffer to workspace (implements overlapping) */
static void load_window_from_ring(ppg_workspace_f_t *w)
{
    /* Load PPG samples - oldest to newest */
    for (int i = 0; i < WIN_SAMP_PPG; i++) {
        int idx = (ppg_wr + i) % WIN_SAMP_PPG;
        w->buf_ppg[i] = ppg_ring[idx];
    }

    /* Load accelerometer samples - oldest to newest */
    for (int i = 0; i < WIN_SAMP_ACC; i++) {
        int idx = (acc_wr + i) % WIN_SAMP_ACC;
        w->acc_x[i] = ax_ring[idx];
        w->acc_y[i] = ay_ring[idx];
        w->acc_z[i] = az_ring[idx];
    }
}

/******************************************************************************
 *                           FLASH HELPER FUNCTIONS                           *
 ******************************************************************************/

#if FLASH_STORAGE_AVAILABLE

/* Pretty-print helper */
static void dump_head_tail_u32(const char *label, const uint32_t *p, size_t count)
{
    LOG_INF("%s (count=%u)", label, (unsigned)count);

    size_t head = (count < DUMP_HEAD_COUNT) ? count : DUMP_HEAD_COUNT;
    size_t tail = (count < DUMP_TAIL_COUNT) ? count : DUMP_TAIL_COUNT;

    if (head) {
        LOG_INF("  head[%u]:", (unsigned)head);
        for (size_t i = 0; i < head; i++) {
            printk("%u ", (unsigned)p[i]);
        }
        printk("\n");
    }

    if (tail && count > head) {
        LOG_INF("  tail[%u]:", (unsigned)tail);
        for (size_t i = count - tail; i < count; i++) {
            printk("%u ", (unsigned)p[i]);
        }
        printk("\n");
    }
}

/* Erase in friendly chunks with progress */
static int erase_region_progress(const struct device *flash, off_t off, size_t bytes)
{
    uint64_t t0 = k_uptime_get();
    size_t erased = 0;

    while (erased < bytes) {
        size_t chunk = bytes - erased;
        if (chunk > ERASE_CHUNK_BYTES) chunk = ERASE_CHUNK_BYTES;

        int rc = flash_erase(flash, off + erased, chunk);
        if (rc) {
            LOG_ERR("ERASE FAIL at 0x%06x (%d)", (unsigned)(off + erased), rc);
            return rc;
        }
        erased += chunk;

        uint64_t now = k_uptime_get();
        LOG_INF("  Erased %u / %u bytes (%.1f%%) in %llums",
               (unsigned)erased, (unsigned)bytes,
               (erased * 100.0) / bytes,
               (unsigned long long)(now - t0));
        k_sleep(K_MSEC(1));
    }
    LOG_INF("Erase complete. Total %u bytes.", (unsigned)bytes);
    return 0;
}

/* Scan flash to find next empty slot, erase if full */
static off_t find_next_write_offset(const struct device *flash)
{
    LOG_INF("Scanning flash for next available %u-byte slot...", (unsigned)CHUNK_PAGED_BYTES);
    uint32_t first_word;
    int rc;

    const uint32_t max_chunks = DATA_REGION_TOTAL_SIZE / CHUNK_PAGED_BYTES;
    LOG_INF("Data region: 0x%06x to 0x%06x (%u chunks total)",
           (unsigned)DATA_REGION_START_OFFSET,
           (unsigned)(DATA_REGION_START_OFFSET + DATA_REGION_TOTAL_SIZE),
           max_chunks);

    for (uint32_t i = 0; i < max_chunks; i++) {
        off_t current_offset = DATA_REGION_START_OFFSET + (i * CHUNK_PAGED_BYTES);

        rc = flash_read(flash, current_offset, &first_word, sizeof(first_word));
        if (rc) {
            LOG_WRN("Flash read fail @ 0x%06x (%d). Assuming full/error.",
                   (unsigned)current_offset, rc);
            break;
        }

        if (first_word == 0xFFFFFFFF) {
            LOG_INF("Found empty slot %u at offset 0x%06x",
                   i, (unsigned)current_offset);
            return current_offset;
        }
    }

    LOG_INF("Flash region is full. Wrapping around to beginning (circular buffer mode).");
    LOG_INF("Old data will be overwritten as new chunks are written.");
    LOG_INF("Note: Individual sectors will be erased before writing.");

    /* Return to start - will wrap around and overwrite old data */
    return DATA_REGION_START_OFFSET;
}

/* Flush PPG RAM buffer to flash */
static int flush_ppg_to_flash(const struct device *flash, off_t off,
                              const uint32_t *buffer, size_t sample_count)
{
    const uint8_t *src = (const uint8_t *)buffer;
    uint32_t data_bytes = sample_count * PPG_ELEM_SIZE;
    uint32_t paged_bytes = ROUND_UP(data_bytes, PAGE_SIZE);

    uint8_t tail_pad[PAGE_SIZE] = {0};
    uint32_t written = 0;
    uint32_t next_prog = WRITE_PROGRESS_BYTES;
    uint64_t t0 = k_uptime_get();

    LOG_INF("Flushing %u bytes (paged=%u) to flash @0x%06x ...",
           (unsigned)data_bytes, (unsigned)paged_bytes, (unsigned)off);

    /* Erase this sector before writing (required for flash overwrites) */
    LOG_INF("Erasing sector at offset 0x%06x (%u bytes)...", (unsigned)off, (unsigned)paged_bytes);
    int rc = flash_erase(flash, off, paged_bytes);
    if (rc) {
        LOG_ERR("ERASE FAIL at 0x%06x (%d)", (unsigned)off, rc);
        return rc;
    }

    while (written < paged_bytes) {
        const uint8_t *page_ptr;
        if (written + PAGE_SIZE <= data_bytes) {
            page_ptr = src + written;
        } else {
            size_t remain = (data_bytes > written) ? (data_bytes - written) : 0;
            if (remain > 0) {
                memcpy(tail_pad, src + written, remain);
                if (remain < PAGE_SIZE) {
                    memset(tail_pad + remain, 0, PAGE_SIZE - remain);
                }
            }
            page_ptr = tail_pad;
        }

        int rc = flash_write(flash, off + written, page_ptr, PAGE_SIZE);
        if (rc) {
            LOG_ERR("WRITE FAIL at 0x%06x (%d)", (unsigned)(off + written), rc);
            return rc;
        }
        written += PAGE_SIZE;

        if (written >= next_prog && paged_bytes > next_prog) {
            uint64_t now = k_uptime_get();
            LOG_INF("  Written %u / %u bytes (%.1f%%) in %llums",
                   (unsigned)written, (unsigned)paged_bytes,
                   (written * 100.0) / paged_bytes,
                   (unsigned long long)(now - t0));
            next_prog += WRITE_PROGRESS_BYTES;
        }
    }

    uint64_t t1 = k_uptime_get();
    LOG_INF("Flush done. Total %llums", (unsigned long long)(t1 - t0));
    return 0;
}

/* Read back excerpts from flash */
static int read_flash_excerpts_ppg(const struct device *flash, off_t off, size_t sample_count)
{
    uint32_t head_buf[DUMP_HEAD_COUNT] = {0};
    size_t head_elems = (sample_count < DUMP_HEAD_COUNT) ? sample_count : DUMP_HEAD_COUNT;
    size_t head_bytes = head_elems * PPG_ELEM_SIZE;
    int rc = flash_read(flash, off, head_buf, head_bytes);
    if (rc) {
        LOG_ERR("READ head fail (%d)", rc);
        return rc;
    }

    uint32_t tail_buf[DUMP_TAIL_COUNT] = {0};
    size_t tail_elems = (sample_count < DUMP_TAIL_COUNT) ? sample_count : DUMP_TAIL_COUNT;

    if (sample_count <= head_elems) {
        tail_elems = 0;
    }

    off_t tail_off = off + (sample_count - tail_elems) * PPG_ELEM_SIZE;
    rc = flash_read(flash, tail_off, tail_buf, tail_elems * PPG_ELEM_SIZE);
    if (rc) {
        LOG_ERR("READ tail fail (%d)", rc);
        return rc;
    }

    LOG_INF("FLASH excerpts (count=%u) from @0x%06x", (unsigned)sample_count, (unsigned)off);
    if (head_elems > 0) {
        LOG_INF("  head[%u]:", (unsigned)head_elems);
        for (size_t i = 0; i < head_elems; i++) printk("%u ", (unsigned)head_buf[i]);
        printk("\n");
    }
    if (tail_elems > 0) {
        LOG_INF("  tail[%u]:", (unsigned)tail_elems);
        for (size_t i = 0; i < tail_elems; i++) printk("%u ", (unsigned)tail_buf[i]);
        printk("\n");
    }
    return 0;
}

#endif /* FLASH_STORAGE_AVAILABLE */

/******************************************************************************
 *                           BLE FEATURE TRANSMISSION                         *
 ******************************************************************************/

/*! Send HRV features via BLE (separate characteristic in same service)
 *  Format: [SQI(4)] [HR(4)] [SDNN(4)] [RMSSD(4)] [IBI(4)] [Activity(1)]
 *          [BaselineCount(2)] [BaselineTarget(2)] [Z_HR(4)] [STIM(1)]
 *  Total: 32 bytes
 */
static void ble_send_hrv_features(float sqi, FeaturesF *features, int activity,
                                   int baseline_count, int baseline_target,
                                   float z_hr, bool stim)
{
    uint8_t feature_buffer[40];
    uint16_t index = 0;

    /* Pack SQI as float (4 bytes, little-endian) */
    uint32_t sqi_bits;
    memcpy(&sqi_bits, &sqi, sizeof(float));
    feature_buffer[index++] = (sqi_bits) & 0xFF;
    feature_buffer[index++] = (sqi_bits >> 8) & 0xFF;
    feature_buffer[index++] = (sqi_bits >> 16) & 0xFF;
    feature_buffer[index++] = (sqi_bits >> 24) & 0xFF;

    /* Pack HR_mean as float (4 bytes) */
    uint32_t hr_bits;
    memcpy(&hr_bits, &features->HR_mean, sizeof(float));
    feature_buffer[index++] = (hr_bits) & 0xFF;
    feature_buffer[index++] = (hr_bits >> 8) & 0xFF;
    feature_buffer[index++] = (hr_bits >> 16) & 0xFF;
    feature_buffer[index++] = (hr_bits >> 24) & 0xFF;

    /* Pack SDNN as float (4 bytes) */
    uint32_t sdnn_bits;
    memcpy(&sdnn_bits, &features->SDNN, sizeof(float));
    feature_buffer[index++] = (sdnn_bits) & 0xFF;
    feature_buffer[index++] = (sdnn_bits >> 8) & 0xFF;
    feature_buffer[index++] = (sdnn_bits >> 16) & 0xFF;
    feature_buffer[index++] = (sdnn_bits >> 24) & 0xFF;

    /* Pack RMSSD as float (4 bytes) */
    uint32_t rmssd_bits;
    memcpy(&rmssd_bits, &features->RMSSD, sizeof(float));
    feature_buffer[index++] = (rmssd_bits) & 0xFF;
    feature_buffer[index++] = (rmssd_bits >> 8) & 0xFF;
    feature_buffer[index++] = (rmssd_bits >> 16) & 0xFF;
    feature_buffer[index++] = (rmssd_bits >> 24) & 0xFF;

    /* Pack IBI_mean as float (4 bytes) */
    uint32_t ibi_bits;
    memcpy(&ibi_bits, &features->ibi_mean, sizeof(float));
    feature_buffer[index++] = (ibi_bits) & 0xFF;
    feature_buffer[index++] = (ibi_bits >> 8) & 0xFF;
    feature_buffer[index++] = (ibi_bits >> 16) & 0xFF;
    feature_buffer[index++] = (ibi_bits >> 24) & 0xFF;

    /* Pack activity as uint8_t (1 byte) */
    feature_buffer[index++] = (uint8_t)activity;

    /* Pack baseline_count as uint16_t (2 bytes, little-endian) */
    feature_buffer[index++] = (baseline_count) & 0xFF;
    feature_buffer[index++] = (baseline_count >> 8) & 0xFF;

    /* Pack baseline_target as uint16_t (2 bytes, little-endian) */
    feature_buffer[index++] = (baseline_target) & 0xFF;
    feature_buffer[index++] = (baseline_target >> 8) & 0xFF;

    /* Pack z_hr as float (4 bytes) */
    uint32_t z_hr_bits;
    memcpy(&z_hr_bits, &z_hr, sizeof(float));
    feature_buffer[index++] = (z_hr_bits) & 0xFF;
    feature_buffer[index++] = (z_hr_bits >> 8) & 0xFF;
    feature_buffer[index++] = (z_hr_bits >> 16) & 0xFF;
    feature_buffer[index++] = (z_hr_bits >> 24) & 0xFF;

    /* Pack stim decision as uint8_t (1 byte) */
    feature_buffer[index++] = (uint8_t)stim;

    /* Send to HRV Features characteristic (separate from raw PPG data) */
    ble_send_hrv_features_data(feature_buffer, index);

    LOG_DBG("Sent HRV features via BLE: %d bytes", index);
}

/******************************************************************************
 *                       ACCELEROMETER SAMPLING THREAD                        *
 ******************************************************************************/

/*! Real BMA580 accelerometer thread - reads actual sensor data at 10 Hz */
void acc_sampling_thread(void)
{
    const uint32_t acc_period_ms = 1000 / FS_ACC;  /* 100 ms for 10 Hz */
    int8_t rslt;
    uint8_t sensor_ctrl;
    struct bma5_acc_conf acc_cfg;
    struct bma5_accel sens_data;
    struct bma5_sensor_status status;
    enum bma5_context context = BMA5_SMARTPHONE;
    bool sensor_initialized = false;

    LOG_INF("BMA580 ACC thread started at %d ms intervals (%.1f Hz)",
           acc_period_ms, 1000.0f / acc_period_ms);

    /* Initialize BMA580 sensor */
    rslt = bma5_interface_init(&bma_dev, BMA5_I2C_INTF, context);
    if (rslt != BMA5_OK) {
        LOG_WRN("BMA580: Interface init failed (%d) - accelerometer disabled, continuing without it", rslt);
        sensor_initialized = false;
    } else {
        rslt = bma580_init(&bma_dev);
        if (rslt != BMA5_OK) {
            LOG_WRN("BMA580: Sensor init failed (%d) - accelerometer disabled, continuing without it", rslt);
            sensor_initialized = false;
        } else {
            LOG_INF("BMA580: Chip ID: 0x%X", bma_dev.chip_id);

            /* Get current accel configuration */
            rslt = bma5_get_acc_conf(&acc_cfg, &bma_dev);
            if (rslt != BMA5_OK) {
                LOG_WRN("BMA580: Get config failed (%d) - accelerometer disabled, continuing without it", rslt);
                sensor_initialized = false;
            } else {
                /* Set accel configurations for 10 Hz operation */
                acc_cfg.acc_odr = BMA5_ACC_ODR_HZ_25;           /* 25 Hz ODR (closest to 10 Hz) */
                acc_cfg.acc_bwp = BMA5_ACC_BWP_NORM_AVG4;
                acc_cfg.power_mode = BMA5_POWER_MODE_HPM;
                acc_cfg.acc_range = BMA5_ACC_RANGE_MAX_2G;      /* ±2g range */
                acc_cfg.acc_iir_ro = BMA5_ACC_IIR_RO_DB_40;
                acc_cfg.noise_mode = BMA5_NOISE_MODE_LOWER_POWER;
                acc_cfg.acc_drdy_int_auto_clear = BMA5_ACC_DRDY_INT_AUTO_CLEAR_ENABLED;

                rslt = bma5_set_acc_conf(&acc_cfg, &bma_dev);
                if (rslt != BMA5_OK) {
                    LOG_WRN("BMA580: Set config failed (%d) - accelerometer disabled, continuing without it", rslt);
                    sensor_initialized = false;
                } else {
                    /* Enable accelerometer */
                    sensor_ctrl = BMA5_SENSOR_CTRL_ENABLE;
                    rslt = bma5_set_acc_conf_0(sensor_ctrl, &bma_dev);
                    if (rslt != BMA5_OK) {
                        LOG_WRN("BMA580: Enable sensor failed (%d) - accelerometer disabled, continuing without it", rslt);
                        sensor_initialized = false;
                    } else {
                        sensor_initialized = true;
                        LOG_INF("BMA580: Accelerometer initialized and enabled successfully");
                        LOG_INF("BMA580: Range=±2G, ODR=25Hz, Mode=HPM");
                    }
                }
            }
        }
    }

    /* Main sampling loop */
    while (1) {
        if (sensor_initialized) {
            /* Get sensor status to check if data is ready */
            rslt = bma5_get_sensor_status(&status, &bma_dev);
            if (rslt == BMA5_OK) {
                /* Read accelerometer data */
                rslt = bma5_get_acc(&sens_data, &bma_dev);

                if (rslt == BMA5_OK) {
                    /* Converting lsb to meter per second squared for 16 bit resolution at 2G range */
                    float x_ms2 = lsb_to_ms2(sens_data.x, 2.0f, BMA5_16_BIT_RESOLUTION);
                    float y_ms2 = lsb_to_ms2(sens_data.y, 2.0f, BMA5_16_BIT_RESOLUTION);
                    float z_ms2 = lsb_to_ms2(sens_data.z, 2.0f, BMA5_16_BIT_RESOLUTION);

                    /* Convert from m/s² to mg (milligrams) for HRM algorithm */
                    /* 1g = 9.80665 m/s² = 1000 mg */
                    /* mg = (m/s²) * (1000 / 9.80665) */
                    float x_mg = x_ms2 * (1000.0f / GRAVITY_EARTH);
                    float y_mg = y_ms2 * (1000.0f / GRAVITY_EARTH);
                    float z_mg = z_ms2 * (1000.0f / GRAVITY_EARTH);

                    /* Push real accelerometer data to ring buffer */
                    ring_push_acc(x_mg, y_mg, z_mg);
                } else {
                    LOG_WRN("BMA580: Read data failed (%d)", rslt);
                }
            }
        } else {
            /* Sensor not initialized - log error only once every 100 iterations to reduce log spam */
            static uint32_t error_count = 0;
            if ((error_count % 100) == 0) {
                LOG_WRN("BMA580: Sensor not initialized - no accelerometer data available (count: %u)", error_count);
            }
            error_count++;
        }

        /* Sleep until next sample */
        k_sleep(K_MSEC(acc_period_ms));
    }
}

/*! Callback that is called by the Chip Library when new data is available, see ::as7058_callback_t. */
static void as7058_callback(err_code_t error, const uint8_t *p_fifo_data, uint16_t fifo_data_size,
                            const agc_status_t *p_agc_statuses, uint8_t agc_statuses_num,
                            as7058_status_events_t sensor_events, const void *p_cb_param)
{
    int sub_sample_id_index;
    err_code_t result;
    double sub_sample_period;
    uint32_t samples[48];
    uint16_t sample_cnt;
    static uint8_t ppg_buffer[192];  // Buffer for BLE: 48 samples × 4 bytes each

    /* Mark parameter as unused to silence warnings. */
    M_UNUSED_PARAM(p_cb_param);
    M_UNUSED_PARAM(p_agc_statuses);
    M_UNUSED_PARAM(agc_statuses_num);
    M_UNUSED_PARAM(sensor_events);

    /* Check if error occurred in the Chip Library. */
    if (error != ERR_SUCCESS) {
        LOG_ERR("Received error code %d from Chip Library", error);
        return;
    }

    /* Extract and process samples for PPG1_SUB1. */
    sub_sample_id_index = AS7058_SUB_SAMPLE_ID_PPG1_SUB1;
    sub_sample_period = g_ppg_sample_period_s;

    /* Call the FIFO data extract function, which copies all samples of a given sub-sample to a signed 32-bit array. */
    sample_cnt = sizeof(samples) / sizeof(samples[0]);
    result = as7058_extract_samples(sub_sample_id_index, p_fifo_data, fifo_data_size, samples, &sample_cnt,
                                    (as7058_extract_metadata_t *)&g_extract_metadata);

    if (result == ERR_SUCCESS && sample_cnt > 0) {
#if FLASH_STORAGE_AVAILABLE
        /* Skip all processing if paused for flash read */
        if (ppg_paused_for_flash_read) {
            /* Silently drop samples during flash read to avoid BLE contention */
            return;
        }
#endif

        /* Push each PPG sample to the ring buffer for HRM processing */
        for (int i = 0; i < sample_cnt; i++) {
            ring_push_ppg((float)samples[i]);
        }

#if FLASH_STORAGE_AVAILABLE
        /* Store PPG data in flash RAM buffer */
        if (ppg_flash_storage_enabled && !ppg_flash_buffer_full) {
            for (int i = 0; i < sample_cnt; i++) {
                if (ppg_flash_sample_count < PPG_RAM_BUFFER_SIZE) {
                    ppg_ram_buf[ppg_flash_sample_count] = (uint32_t)samples[i];
                    ppg_flash_sample_count++;

                    /* Print progress every 256 samples (1KB) */
                    if ((ppg_flash_sample_count % 256) == 0) {
                        LOG_INF("Flash buffer: %u / %u samples (%u KB / 4 KB)",
                               (unsigned)ppg_flash_sample_count,
                               (unsigned)PPG_RAM_BUFFER_SIZE,
                               (unsigned)(ppg_flash_sample_count * 4) / 1024);
                    }

                    /* Check if we've reached 4KB (1024 samples) */
                    if (ppg_flash_sample_count >= PPG_RAM_BUFFER_SIZE) {
                        LOG_INF("*** [Collection] Flash RAM Buffer is full (4KB). Ready to flush.");
                        ppg_flash_buffer_full = true;
                        break;
                    }
                }
            }
        }
#endif

        /* Pack ALL samples into BLE buffer (4 bytes per sample, big-endian) */
        uint16_t buffer_index = 0;
        for (int i = 0; i < sample_cnt && buffer_index < sizeof(ppg_buffer); i++) {
            int32_t sample = (int32_t)samples[i];
            ppg_buffer[buffer_index++] = (sample >> 24) & 0xFF;
            ppg_buffer[buffer_index++] = (sample >> 16) & 0xFF;
            ppg_buffer[buffer_index++] = (sample >> 8) & 0xFF;
            ppg_buffer[buffer_index++] = sample & 0xFF;
        }

        /* Send notification to Raw PPG Data characteristic */
        ble_send_ppg_data(ppg_buffer, buffer_index);

        g_sub_sample_cnt[sub_sample_id_index] += sample_cnt;
    }
}

static err_code_t ppg_configure_registers(void)
{
    err_code_t result = ERR_SUCCESS;
    LOG_INF("Configuring AS7058 registers for PPG...");

    /**************************************************************************
     *                           CHIP CONFIGURATION                           *
     **************************************************************************
     * This section uses the Chip Library to apply a configuration to the     *
     * AS7058 device that enables PPG measurement.                            *
     **************************************************************************/

    /* Configure register group POWER. */
    const as7058_reg_group_power_t power_config = {{
        .pwr_on = 31,
        .pwr_iso = 0,
        .clk_cfg = 7,
        .ref_cfg1 = 63,
        .ref_cfg2 = 14,
        .ref_cfg3 = 160,
        .standby_on1 = 0,
        .standby_on2 = 0,
        .standby_en1 = 4,
        .standby_en2 = 2,
        .standby_en3 = 4,
        .standby_en4 = 0,
        .standby_en5 = 3,
        .standby_en6 = 16,
        .standby_en7 = 16,
        .standby_en8 = 4,
        .standby_en9 = 0,
        .standby_en10 = 3,
        .standby_en11 = 16,
        .standby_en12 = 16,
        .standby_en13 = 16,
        .standby_en14 = 16,
    }};
    result = as7058_set_reg_group(AS7058_REG_GROUP_ID_PWR, power_config.reg_buffer, sizeof(as7058_reg_group_power_t));
    if (result != ERR_SUCCESS) {
        LOG_ERR("Writing register group AS7058_REG_GROUP_ID_PWR returned error %d", result);
        return result;
    }

    /* Configure register group CONTROL. */
    const as7058_reg_group_control_t control_config = {{
        .i2c_mode = 0,
        .int_cfg = 0,
        .if_cfg = 72,
        .gpio_cfg1 = 0,
        .gpio_cfg2 = 0,
        .io_cfg = 0,
    }};
    result = as7058_set_reg_group(AS7058_REG_GROUP_ID_CTRL, control_config.reg_buffer, sizeof(as7058_reg_group_control_t));
    if (result != ERR_SUCCESS) {
        LOG_ERR("Writing register group AS7058_REG_GROUP_ID_CTRL returned error %d", result);
        return result;
    }

    /* Configure register group LED. */
    const as7058_reg_group_led_t led_config = {{
        .vcsel_password = 87,
        .vcsel_cfg = 192,
        .vcsel_mode = 0,
        .led_cfg = 1,
        .led_drv1 = 0,
        .led_drv2 = 0,
        .led1_ictrl = 9,
        .led2_ictrl = 0,
        .led3_ictrl = 0,
        .led4_ictrl = 0,
        .led5_ictrl = 0,
        .led6_ictrl = 0,
        .led7_ictrl = 0,
        .led8_ictrl = 0,
        .led_irng1 = 63,
        .led_irng2 = 0,
        .led_sub1 = 1,
        .led_sub2 = 0,
        .led_sub3 = 0,
        .led_sub4 = 0,
        .led_sub5 = 0,
        .led_sub6 = 0,
        .led_sub7 = 0,
        .led_sub8 = 0,
        .lowvds_wait = 0,
    }};
    result = as7058_set_reg_group(AS7058_REG_GROUP_ID_LED, led_config.reg_buffer, sizeof(as7058_reg_group_led_t));
    if (result != ERR_SUCCESS) {
        LOG_ERR("Writing register group AS7058_REG_GROUP_ID_LED returned error %d", result);
        return result;
    }

    /* Configure register group PD. */
    const as7058_reg_group_pd_t pd_config = {{
        .pdsel_cfg = 0,
        .ppg1_pdsel1 = 2,
        .ppg1_pdsel2 = 0,
        .ppg1_pdsel3 = 0,
        .ppg1_pdsel4 = 0,
        .ppg1_pdsel5 = 0,
        .ppg1_pdsel6 = 7,
        .ppg1_pdsel7 = 0,
        .ppg1_pdsel8 = 0,
        .ppg2_pdsel1 = 0,
        .ppg2_pdsel2 = 0,
        .ppg2_pdsel3 = 0,
        .ppg2_pdsel4 = 0,
        .ppg2_pdsel5 = 0,
        .ppg2_pdsel6 = 1,
        .ppg2_pdsel7 = 0,
        .ppg2_pdsel8 = 1,
        .ppg2_afesel1 = 0,
        .ppg2_afesel2 = 0,
        .ppg2_afesel3 = 0,
        .ppg2_afesel4 = 0,
        .ppg2_afeen = 0,
    }};
    result = as7058_set_reg_group(AS7058_REG_GROUP_ID_PD, pd_config.reg_buffer, sizeof(as7058_reg_group_pd_t));
    if (result != ERR_SUCCESS) {
        LOG_ERR("Writing register group AS7058_REG_GROUP_ID_PD returned error %d", result);
        return result;
    }

    /* Configure register group IOS. */
    const as7058_reg_group_ios_t ios_config = {{
        .ios_ppg1_sub1 = 72,
        .ios_ppg1_sub2 = 0,
        .ios_ppg1_sub3 = 0,
        .ios_ppg1_sub4 = 0,
        .ios_ppg1_sub5 = 0,
        .ios_ppg1_sub6 = 0,
        .ios_ppg1_sub7 = 0,
        .ios_ppg1_sub8 = 0,
        .ios_ppg2_sub1 = 0,
        .ios_ppg2_sub2 = 0,
        .ios_ppg2_sub3 = 0,
        .ios_ppg2_sub4 = 0,
        .ios_ppg2_sub5 = 0,
        .ios_ppg2_sub6 = 0,
        .ios_ppg2_sub7 = 0,
        .ios_ppg2_sub8 = 0,
        .ios_ledoff = 0,
        .ios_cfg = 0,
        .aoc_sar_thres = 0,
        .aoc_sar_range = 0,
        .aoc_sar_ppg1 = 0,
        .aoc_sar_ppg2 = 0,
    }};
    result = as7058_set_reg_group(AS7058_REG_GROUP_ID_IOS, ios_config.reg_buffer, sizeof(as7058_reg_group_ios_t));
    if (result != ERR_SUCCESS) {
        LOG_ERR("Writing register group AS7058_REG_GROUP_ID_IOS returned error %d", result);
        return result;
    }

    /* Configure register group PPG. */
    const as7058_reg_group_ppg_t ppg_config = {{
        .ppgmod_cfg1 = 0,
        .ppgmod_cfg2 = 0,
        .ppgmod_cfg3 = 0,
        .ppgmod1_cfg1 = 135,
        .ppgmod1_cfg2 = 84,
        .ppgmod1_cfg3 = 7,
        .ppgmod2_cfg1 = 7,
        .ppgmod2_cfg2 = 84,
        .ppgmod2_cfg3 = 7,
    }};
    result = as7058_set_reg_group(AS7058_REG_GROUP_ID_PPG, ppg_config.reg_buffer, sizeof(as7058_reg_group_ppg_t));
    if (result != ERR_SUCCESS) {
        LOG_ERR("Writing register group AS7058_REG_GROUP_ID_PPG returned error %d", result);
        return result;
    }

    /* Configure register group ECG. */
    const as7058_reg_group_ecg_t ecg_config = {{
        .bioz_cfg = 0,
        .bioz_excit = 0,
        .bioz_mixer = 0,
        .bioz_select = 0,
        .bioz_gain = 0,
        .ecgmod_cfg1 = 0,
        .ecgmod_cfg2 = 0,
        .ecgimux_cfg1 = 0,
        .ecgimux_cfg2 = 0,
        .ecgimux_cfg3 = 0,
        .ecgamp_cfg1 = 0,
        .ecgamp_cfg2 = 0,
        .ecgamp_cfg3 = 0,
        .ecgamp_cfg4 = 0,
        .ecgamp_cfg5 = 0,
        .ecgamp_cfg6 = 0,
        .ecgamp_cfg7 = 0,
        .ecg_bioz = 0,
        .leadoff_cfg = 0,
        .leadoff_thresl = 0,
        .leadoff_thresh = 0,
    }};
    result = as7058_set_reg_group(AS7058_REG_GROUP_ID_ECG, ecg_config.reg_buffer, sizeof(as7058_reg_group_ecg_t));
    if (result != ERR_SUCCESS) {
        LOG_ERR("Writing register group AS7058_REG_GROUP_ID_ECG returned error %d", result);
        return result;
    }

    /* Configure register group SINC. */
    const as7058_reg_group_sinc_t sinc_config = {{
        .ppg_sinc_cfga = 2,
        .ppg_sinc_cfgb = 3,
        .ppg_sinc_cfgc = 0,
        .ppg_sinc_cfgd = 0,
        .ecg1_sinc_cfga = 0,
        .ecg1_sinc_cfgb = 0,
        .ecg1_sinc_cfgc = 0,
        .ecg2_sinc_cfga = 0,
        .ecg2_sinc_cfgb = 0,
        .ecg2_sinc_cfgc = 0,
        .ecg_sinc_cfg = 0,
    }};
    result = as7058_set_reg_group(AS7058_REG_GROUP_ID_SINC, sinc_config.reg_buffer, sizeof(as7058_reg_group_sinc_t));
    if (result != ERR_SUCCESS) {
        LOG_ERR("Writing register group AS7058_REG_GROUP_ID_SINC returned error %d", result);
        return result;
    }

    /* Configure register group SEQ. */
    const as7058_reg_group_seq_t seq_config = {{
        .irq_enable = 255,
        .ppg_sub_wait = 0,
        .ppg_sar_wait = 0,
        .ppg_led_init = 10,
        .ppg_freql = 31,
        .ppg_freqh = 3,
        .ppg1_sub_en = 1,
        .ppg2_sub_en = 0,
        .ppg_mode_1 = 0,
        .ppg_mode_2 = 0,
        .ppg_mode_3 = 0,
        .ppg_mode_4 = 0,
        .ppg_mode_5 = 0,
        .ppg_mode_6 = 0,
        .ppg_mode_7 = 0,
        .ppg_mode_8 = 0,
        .ppg_cfg = 6,
        .ecg_freql = 0,
        .ecg_freqh = 0,
        .ecg1_freqdivl = 0,
        .ecg1_freqdivh = 0,
        .ecg2_freqdivl = 0,
        .ecg2_freqdivh = 0,
        .ecg_subs = 0,
        .leadoff_initl = 0,
        .leadoff_inith = 0,
        .ecg_initl = 0,
        .ecg_inith = 0,
        .sample_num = 0,
    }};
    result = as7058_set_reg_group(AS7058_REG_GROUP_ID_SEQ, seq_config.reg_buffer, sizeof(as7058_reg_group_seq_t));
    if (result != ERR_SUCCESS) {
        LOG_ERR("Writing register group AS7058_REG_GROUP_ID_SEQ returned error %d", result);
        return result;
    }

    /* Configure register group PP. */
    const as7058_reg_group_pp_t post_config = {{
        .pp_cfg = 0,
        .ppg1_pp1 = 0,
        .ppg1_pp2 = 0,
        .ppg2_pp1 = 0,
        .ppg2_pp2 = 0,
    }};
    result = as7058_set_reg_group(AS7058_REG_GROUP_ID_PP, post_config.reg_buffer, sizeof(as7058_reg_group_pp_t));
    if (result != ERR_SUCCESS) {
        LOG_ERR("Writing register group AS7058_REG_GROUP_ID_PP returned error %d", result);
        return result;
    }

    /* Configure register group FIFO. */
    const as7058_reg_group_fifo_t fifo_config = {{
        .fifo_threshold = 39,
        .fifo_ctrl = 0,
    }};
    result = as7058_set_reg_group(AS7058_REG_GROUP_ID_FIFO, fifo_config.reg_buffer, sizeof(as7058_reg_group_fifo_t));
    if (result != ERR_SUCCESS) {
        LOG_ERR("Writing register group AS7058_REG_GROUP_ID_FIFO returned error %d", result);
        return result;
    }

    /**************************************************************************
     *                     AGC CONFIGURATION                                  *
     **************************************************************************/

    /* Configure automatic gain control (AGC) for LED current optimization. */
    const agc_configuration_t agc_config = {
        .mode = AGC_MODE_DEFAULT,
        .led_control_mode = AGC_AMPL_CNTL_MODE_AUTO,
        .channel = AS7058_SUB_SAMPLE_ID_PPG1_SUB1,
        .led_current_min = 5,
        .led_current_max = 30,
        .rel_amplitude_min_x100 = 5,
        .rel_amplitude_max_x100 = 20,
        .rel_amplitude_motion_x100 = 50,
        .num_led_steps = 1,
        .reserved = {0, 0, 0},
        .threshold_min = 300000,
        .threshold_max = 800000,
    };
    result = as7058_set_agc_config(&agc_config, 1);
    if (result != ERR_SUCCESS) {
        LOG_ERR("as7058_set_agc_config returned error code %d", result);
        return result;
    }
    LOG_INF("AGC configured successfully for PPG1_SUB1");

    LOG_INF("Register configuration complete.");
    return result;
}

/******************************************************************************
 *                              GLOBAL FUNCTIONS                              *
 ******************************************************************************/

int ppg_thread_main(void)
{
    ppg_cmd_t cmd;
    static ppg_state_t state = PPG_STATE_OFF;
    err_code_t result;
    bool hrm_buffers_filled = false;

    LOG_INF("PPG thread started");

      /* init baseline state */
    stim_state_init_f(&ws);

#if FLASH_STORAGE_AVAILABLE
    /**************************************************************************
     *                     FLASH INITIALIZATION                               *
     **************************************************************************/
    /* Initialize the Flash Device */
    flash_dev = DEVICE_DT_GET_ONE(FLASH_COMPAT);
    if (!device_is_ready(flash_dev)) {
        LOG_WRN("Flash device not ready - flash storage disabled");
        flash_dev = NULL;
    } else {
        LOG_INF("=== PPG Flash Storage Initialized ===");
        LOG_INF("Flash Device: %s", flash_dev->name);
        LOG_INF("RAM Buffer: %u samples (%u bytes per chunk)",
               (unsigned)PPG_RAM_BUFFER_SIZE, (unsigned)CHUNK_PAGED_BYTES);
        LOG_INF("Total Flash Capacity: %u bytes (%.2f MB)",
               (unsigned)DATA_REGION_TOTAL_SIZE,
               (double)DATA_REGION_TOTAL_SIZE / (1024.0 * 1024.0));
        LOG_INF("Max Chunks: %u (Total: %u samples)",
               (unsigned)(DATA_REGION_TOTAL_SIZE / CHUNK_PAGED_BYTES),
               (unsigned)(DATA_REGION_TOTAL_SIZE / CHUNK_PAGED_BYTES * PPG_RAM_BUFFER_SIZE));

        /* Find the offset to write to for this run */
        current_write_offset = find_next_write_offset(flash_dev);

        /* Calculate total samples already written based on current offset
         * NOTE: After wraparound/reboot, we can only detect samples currently in flash,
         * not the historical total. The counter resets to reflect available flash data.
         */
        if (current_write_offset > DATA_REGION_START_OFFSET) {
            uint32_t chunks_written = (current_write_offset - DATA_REGION_START_OFFSET) / CHUNK_PAGED_BYTES;
            total_flash_samples_written = chunks_written * PPG_RAM_BUFFER_SIZE;
            LOG_INF("Detected %u existing chunks (%u samples) in flash",
                   chunks_written, (unsigned)total_flash_samples_written);

            /* Check if we're at the end (wrapped around before reboot) */
            uint32_t max_chunks = DATA_REGION_TOTAL_SIZE / CHUNK_PAGED_BYTES;
            if (chunks_written >= max_chunks - 1) {
                LOG_INF("Flash is at/near capacity - may have wrapped before reboot");
            }
        } else {
            total_flash_samples_written = 0;
            LOG_INF("Starting from beginning - either fresh or after wraparound");
        }

        ppg_flash_storage_enabled = true;
        LOG_INF("Flash storage ready at offset 0x%06x", (unsigned)current_write_offset);
    }
#endif

    // This thread loops forever, waiting for messages or processing HRM
    while (1) {
        // Wait for a command with timeout (STEP_SEC) to allow periodic HRM processing
        int ret = k_msgq_get(&ppg_cmd_q, &cmd, K_SECONDS(STEP_SEC));

        // If timeout occurred and we're measuring, process HRM features
        if (ret == -EAGAIN && state == PPG_STATE_MEASURING) {
#if FLASH_STORAGE_AVAILABLE
            /* Skip HRM processing if paused for flash read */
            if (ppg_paused_for_flash_read) {
                continue;
            }
#endif

            // Check if buffers are filled
            if (!hrm_buffers_filled) {
                if (ppg_samples_collected >= WIN_SAMP_PPG &&
                    acc_samples_collected >= WIN_SAMP_ACC) {
                    hrm_buffers_filled = true;
                    LOG_INF("===========================================");
                    LOG_INF("HRM pipeline started!");
                    LOG_INF("Window: %d s, Step: %d s", WIN_SEC, STEP_SEC);
                    LOG_INF("===========================================");
                } else {
                    // Still filling buffers, log progress occasionally
                    static int progress_counter = 0;
                    if (progress_counter % 3 == 0) {
                        LOG_INF("Filling buffers: PPG=%d/%d, ACC=%d/%d",
                               ppg_samples_collected, WIN_SAMP_PPG,
                               acc_samples_collected, WIN_SAMP_ACC);
                    }
                    progress_counter++;
                    continue;
                }
            }

            // Process HRM features if buffers are filled
            if (hrm_buffers_filled) {
                load_window_from_ring(&ws);

                // Run HRM processing pipeline
                acc_prepare_vm_f(&ws);
                preprocess_ppg_f(&ws);

                /* ---------- FLATLINE CHECK (after preprocessing) ---------- */

        float seg_max = custom_max_f(ws.buf_filt, WIN_SAMP_PPG);
        float seg_min = custom_min_f(ws.buf_filt, WIN_SAMP_PPG);
        float seg_range = seg_max - seg_min;

        /* median */
        float seg_median = custom_median_f_ws(ws.buf_filt,
                                            WIN_SAMP_PPG,
                                            ws.scratch1);

        /* MAD = median(|x - median|) */
        for (int i = 0; i < WIN_SAMP_PPG; i++) {
            ws.scratch2[i] = fabsf(ws.buf_filt[i] - seg_median);
        }
        float seg_mad = custom_median_f_ws(ws.scratch2,
                                        WIN_SAMP_PPG,
                                        ws.scratch1);

        /* thresholds */
        float abs_med = fabsf(seg_median);
        float flatline_thresh1 = 1e-3f * fmaxf(1.0f, abs_med);
        float flatline_thresh2 = 1e-6f * fmaxf(1.0f, abs_med);

        /* flatline decision */
        int flatline = (seg_range < flatline_thresh1) ||
                    (seg_mad   < flatline_thresh2);

        /* ---------- SQI + FEATURE LOGIC ---------- */

        float sqi;

        if (flatline) {

            sqi = 0.0f;
            make_nan_features_f_ws(&ws);

        } else {

            sqi = SQI_PPG_f(&ws);

            if (sqi > 0.8f) {
                feature_extraction_PPG_f(&ws);
            } else {
                make_nan_features_f_ws(&ws);
            }
        }

        int activity = Acc_activity_f(&ws);

        /* ---- BASELINE UPDATE (only until ready) ---- */
        stim_baseline_update_f(&ws, sqi, activity, ws.features.HR_mean);

        /* ---- DECISION (only after baseline ready) ---- */
        stim_decide_f(&ws, sqi, activity, ws.features.HR_mean);

        printk("BASELINE: %d/%d  SQI=%.2f HR=%.1f SDNN=%.2f RMSSD=%.2f IBI=%.1f ACT=%d zHR=%.2f DEC=%s\n",
               ws.stim_state.baseline_count,
               ws.stim_state.baseline_target,
               (double)sqi,
               (double)ws.features.HR_mean,
               (double)ws.features.SDNN,
               (double)ws.features.RMSSD,
               (double)ws.features.ibi_mean,
               activity,
               (double)ws.stim_state.z_hr,
               ws.stim_state.stim ? "STIM" : "NO STIM");


                // Send features via BLE
                ble_send_hrv_features(sqi, &ws.features, activity,
                                      ws.stim_state.baseline_count,
                                      ws.stim_state.baseline_target,
                                      ws.stim_state.z_hr,
                                      ws.stim_state.stim);
            }

#if FLASH_STORAGE_AVAILABLE
            // Check if flash buffer is full and needs to be flushed
            // Skip if paused for flash read to avoid conflicts
            if (ppg_flash_buffer_full && ppg_flash_storage_enabled && flash_dev && !ppg_paused_for_flash_read) {
                LOG_INF("========================================");
                LOG_INF("*** [Flush] 4KB PPG data collected! ***");
                LOG_INF("========================================");
                LOG_INF("Offloading %u collected samples to flash.", (unsigned)ppg_flash_sample_count);

                if (ppg_flash_sample_count > 0) {
                    /* Dump a few values from RAM to show it worked */
                    dump_head_tail_u32("RAM (PPG) excerpts", ppg_ram_buf, ppg_flash_sample_count);

                    /* Flush RAM->flash */
                    if (flush_ppg_to_flash(flash_dev, current_write_offset, ppg_ram_buf, ppg_flash_sample_count) == 0) {
                        /* Read back excerpts from flash */
                        LOG_INF("*** Reading back FLASH excerpts for verification ***");
                        if (read_flash_excerpts_ppg(flash_dev, current_write_offset, ppg_flash_sample_count) == 0) {
                            LOG_INF("*** FLASH VERIFICATION SUCCESSFUL ***");
                            LOG_INF("All %u samples (%u bytes) stored and verified!",
                                   (unsigned)ppg_flash_sample_count,
                                   (unsigned)(ppg_flash_sample_count * 4));

                            /* Update total samples written counter */
                            total_flash_samples_written += ppg_flash_sample_count;

                            /* Calculate how many samples are actually in flash (limited by capacity) */
                            uint32_t max_samples_in_flash = (DATA_REGION_TOTAL_SIZE / CHUNK_PAGED_BYTES) * PPG_RAM_BUFFER_SIZE;
                            uint32_t samples_available = (total_flash_samples_written < max_samples_in_flash)
                                                       ? total_flash_samples_written
                                                       : max_samples_in_flash;

                            /* Update BLE flash service to read available flash data */
                            LOG_INF("Updating BLE Flash service for remote access...");
                            LOG_INF("BLE will read from offset 0x%06x with %u samples (of %u total written)",
                                   DATA_REGION_START_OFFSET, (unsigned)samples_available,
                                   (unsigned)total_flash_samples_written);
                            ble_flash_set_params(flash_dev, DATA_REGION_START_OFFSET, samples_available);
                            LOG_INF("BLE Flash service ready! %u samples available for reading.",
                                   (unsigned)samples_available);

                            /* Update write offset for next chunk */
                            current_write_offset += CHUNK_PAGED_BYTES;

                            /* Check if we need to wrap around (circular buffer) */
                            if (current_write_offset >= (DATA_REGION_START_OFFSET + DATA_REGION_TOTAL_SIZE)) {
                                LOG_WRN("========================================");
                                LOG_WRN("Flash full! Wrapping to start (circular buffer mode)");
                                LOG_WRN("Old data will be overwritten");
                                LOG_WRN("========================================");
                                current_write_offset = DATA_REGION_START_OFFSET;
                                /* Note: total_flash_samples_written keeps counting up */
                            }

                            /* Calculate and display flash usage statistics */
                            uint32_t current_chunk = (current_write_offset - DATA_REGION_START_OFFSET) / CHUNK_PAGED_BYTES;
                            uint32_t max_chunks = DATA_REGION_TOTAL_SIZE / CHUNK_PAGED_BYTES;
                            uint32_t bytes_used = current_write_offset - DATA_REGION_START_OFFSET;
                            float percent_used = (bytes_used * 100.0f) / DATA_REGION_TOTAL_SIZE;

                            LOG_INF("Next write offset: 0x%06x", (unsigned)current_write_offset);
                            LOG_INF("Flash Usage: Chunk %u/%u (%.2f MB / %.2f MB = %.1f%%)",
                                   current_chunk, max_chunks,
                                   bytes_used / (1024.0f * 1024.0f),
                                   DATA_REGION_TOTAL_SIZE / (1024.0f * 1024.0f),
                                   percent_used);
                            LOG_INF("Total samples written: %u (%.2f MB) - Flash holds latest %.2f MB",
                                   (unsigned)total_flash_samples_written,
                                   (total_flash_samples_written * 4) / (1024.0f * 1024.0f),
                                   DATA_REGION_TOTAL_SIZE / (1024.0f * 1024.0f));

                            /* Warn when approaching full capacity (first time) */
                            if (percent_used >= 90.0f && total_flash_samples_written < (max_chunks * PPG_RAM_BUFFER_SIZE)) {
                                LOG_WRN("WARNING: Flash is %.1f%% full! Will wrap around at 100%%", percent_used);
                            }
                        }
                    } else {
                        LOG_ERR("ERROR: Flash write failed!");
                    }
                } else {
                    LOG_WRN("No samples collected, skipping flash write.");
                }

                LOG_INF("========================================");
                LOG_INF("*** Flash storage complete! ***");
                LOG_INF("========================================");

                /* Reset flash buffer for next collection */
                ppg_flash_sample_count = 0;
                ppg_flash_buffer_full = false;
                LOG_INF("Flash buffer reset for next collection");
            }
#endif

            continue;  // Go back to waiting for next command/timeout
        }

        // If we got a command (not timeout), process it
        if (ret == 0) {
            switch (cmd) {

            case PPG_CMD_BLE_START:
                if (state == PPG_STATE_OFF) {
                    LOG_INF("START command received. Initializing PPG sensor.");

                    // Reset HRM buffers and counters
                    ppg_samples_collected = 0;
                    acc_samples_collected = 0;
                    ppg_wr = 0;
                    acc_wr = 0;
                    hrm_buffers_filled = false;

#if FLASH_STORAGE_AVAILABLE
                    // Reset flash storage buffers (but keep total_flash_samples_written!)
                    ppg_flash_sample_count = 0;
                    ppg_flash_buffer_full = false;
                    // NOTE: total_flash_samples_written is NOT reset - it persists across PPG start/stop
                    // This ensures BLE can always read ALL data in flash, not just new data
                    LOG_INF("Flash storage buffer reset (total samples preserved: %u)",
                           (unsigned)total_flash_samples_written);
#endif

                    // --- 1. INITIALIZE ---
                    result = as7058_initialize(as7058_callback, NULL, NULL, NULL);
                    if (result != ERR_SUCCESS) {
                        LOG_ERR("AS7058: Initialize failed: %d - PPG sensor not available, staying in OFF state", result);
                        LOG_ERR("AS7058: System will continue without PPG functionality");
                        state = PPG_STATE_OFF;
                        continue;
                    }

                    // --- 2. CONFIGURE ---
                    result = ppg_configure_registers();
                    if (result != ERR_SUCCESS) {
                        LOG_ERR("AS7058: Configure registers failed: %d - PPG sensor not available", result);
                        LOG_ERR("AS7058: System will continue without PPG functionality");
                        state = PPG_STATE_OFF;
                        as7058_shutdown();
                        continue;
                    }

                    // --- 3. GET MEASUREMENT CONFIG ---
                    as7058_meas_config_t meas_config;
                    result = as7058_get_measurement_config(&meas_config);
                    if (result != ERR_SUCCESS) {
                        LOG_ERR("AS7058: Get measurement config failed: %d - PPG sensor not available", result);
                        LOG_ERR("AS7058: System will continue without PPG functionality");
                        state = PPG_STATE_OFF;
                        as7058_shutdown();
                        continue;
                    }

                    // Initialize extract metadata
                    g_extract_metadata.copy_recent_to_current = FALSE;
                    g_extract_metadata.fifo_map = meas_config.fifo_map;
                    g_extract_metadata.current.ppg1_sub = 0;
                    g_extract_metadata.current.ppg2_sub = 0;
                    g_extract_metadata.recent.ppg1_sub = 0;
                    g_extract_metadata.recent.ppg2_sub = 0;

                    // Save the sample period
                    g_ppg_sample_period_s = (double)meas_config.ppg_sample_period_us / 1000 / 1000;

                    // Reset sample count
                    for (int i = 0; i < AS7058_SUB_SAMPLE_ID_NUM; i++) {
                        g_sub_sample_cnt[i] = 0;
                    }

                    // --- 4. START MEASUREMENT ---
                    result = as7058_start_measurement(AS7058_MEAS_MODE_NORMAL);
                    if (result != ERR_SUCCESS) {
                        LOG_ERR("AS7058: Start measurement failed: %d - PPG sensor not available", result);
                        LOG_ERR("AS7058: System will continue without PPG functionality");
                        state = PPG_STATE_OFF;
                        as7058_shutdown();
                    } else {
                        LOG_INF("*** AS7058: PPG measurement started successfully");
                        LOG_INF("HRM processing will start after %d seconds", WIN_SEC);
                        state = PPG_STATE_MEASURING;
                    }
                } else {
                    LOG_WRN("START command received but state is not OFF (%d)", state);
                }
                break;

            case PPG_CMD_BLE_STOP:
                if (state == PPG_STATE_MEASURING) {
                    LOG_INF("STOP command received. Shutting down PPG sensor.");

                    // --- STOP AND SHUTDOWN ---
                    result = as7058_stop_measurement();
                    if (result != ERR_SUCCESS) {
                        LOG_ERR("stop_measurement failed: %d", result);
                    }

                    (void)as7058_shutdown();

                    state = PPG_STATE_OFF;
                    hrm_buffers_filled = false;
                    LOG_INF("HRM processing stopped.");
                } else {
                    LOG_WRN("STOP command received but sensor already off.");
                }
                break;

            case PPG_CMD_INTERNAL_FIFO_READY:
                // Data is already processed in the callback
                // This command is not used in PPG mode but kept for potential future use
                break;
            } // end switch
        } // end if (ret == 0)
    } // end while(1)
}

/******************************************************************************
 *                        FLASH READ PAUSE/RESUME API                         *
 ******************************************************************************/

/**
 * @brief Pause PPG processing during flash read operations
 *
 * Call this before starting a large flash read to prevent:
 * - PPG data collection (flash buffer writes)
 * - HRM algorithm processing
 * - Real-time BLE streaming
 * This allows flash read to complete faster without BLE contention.
 */
void ppg_pause_for_flash_read(void)
{
#if FLASH_STORAGE_AVAILABLE
    ppg_paused_for_flash_read = true;
    LOG_INF("PPG processing PAUSED for flash read operation");
#endif
}

/**
 * @brief Resume PPG processing after flash read completes
 *
 * Call this after flash read completes to resume normal operation.
 */
void ppg_resume_after_flash_read(void)
{
#if FLASH_STORAGE_AVAILABLE
    ppg_paused_for_flash_read = false;
    LOG_INF("PPG processing RESUMED after flash read");
#endif
}

/******************************************************************************
 *                              THREAD DEFINITIONS                            *
 ******************************************************************************/

/* Define PPG management thread with HRM processing: 8KB stack, priority -1 */
K_THREAD_DEFINE(ppg_thread, 8196, ppg_thread_main, NULL, NULL, NULL, 0, K_ESSENTIAL, 0);

/* Define accelerometer stub thread: 2KB stack, priority -2 */
K_THREAD_DEFINE(acc_thread, 2048, acc_sampling_thread, NULL, NULL, NULL, 2, 0, 0);
