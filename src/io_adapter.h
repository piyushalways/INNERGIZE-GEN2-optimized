#ifndef APP_IO_H
#define APP_IO_H

#include <stdint.h>
#include <stdbool.h>

#define BTN_PRESSED     1
#define BTN_RELEASED    0


extern  int32_t initial_value;
extern  int32_t current_value;

extern int32_t batt_val_mv;

extern uint16_t raw_batt_val ;

extern uint8_t charger_state;

extern uint8_t battery_low;

void start_blue_led_thread(uint32_t period);

void stop_blue_led_thread(void);

void stop_red_led_thread(void);

void start_red_led_thread(void);

void start_green_led_thread(uint32_t period);

void stop_green_led_thread(void);
/**
 * @brief Power off, write p0.31 to 0
 * 
 */
#endif
