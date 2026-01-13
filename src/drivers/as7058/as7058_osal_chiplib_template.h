
#include <zephyr/kernel.h>
#include <zephyr/device.h>
#include <zephyr/drivers/i2c.h>
#include <zephyr/drivers/sensor.h>
#include <zephyr/logging/log.h>
#include <zephyr/sys/ring_buffer.h>
#include <zephyr/drivers/gpio.h>
#include <hal/nrf_gpio.h>

#include "error_codes.h"
#include "std_inc.h"


 err_code_t as7058_osal_irq_enable(bool en);