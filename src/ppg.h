#ifndef PPG_H
#define PPG_H

#include <zephyr/kernel.h>
#include <zephyr/device.h>

/* 1. Define the states for PPG manager */
typedef enum {
    PPG_STATE_OFF,
    PPG_STATE_MEASURING,
} ppg_state_t;

/* 2. Define the commands for the message queue */
typedef enum {
    PPG_CMD_BLE_START,
    PPG_CMD_BLE_STOP,
    PPG_CMD_INTERNAL_FIFO_READY,
} ppg_cmd_t;

/* 3. Define the message queue */
// The message queue will hold one 'ppg_cmd_t' message at a time.
extern struct k_msgq ppg_cmd_q;

/* 4. BLE functions - separate characteristics in same service */
extern void ble_send_ppg_data(const uint8_t *data, uint16_t length);        // Raw PPG data characteristic
extern void ble_send_hrv_features_data(const uint8_t *data, uint16_t length); // HRV features characteristic

/* 5. Flash read pause/resume functions */
extern void ppg_pause_for_flash_read(void);   // Pause PPG processing during flash read
extern void ppg_resume_after_flash_read(void); // Resume PPG processing after flash read

#endif // PPG_H
