#ifndef MAIN_H
#define MAIN_H

#include <zephyr/kernel.h>

#include "core_types.h"
#include "bluetooth_manager.h"

#define MAIN_MSG_DATA_SRC_MOTION_DETECTOR       1
#define MAIN_MSG_DATA_SRC_BLE                   2

/**
 * @brief data structure for main message queue
 * 
 */
/* struct to store the ble ems data and acces it in main */
//extern K_THREAD_STACK_DEFINE(led_stack_area, 512);
struct main_msg_data{
    int src;
    union{
        struct ble_msg ble;
    }data;
};

#endif