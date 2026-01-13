/******************************************************************************
 * Copyright © 2022 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

/*
This template shall help to implement your own OSAL
which can be called by the AS7058 Chip Library.
All code lines which start with '// TODO' must be replaced by your own implementations.
*/

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include "as7058_osal_chiplib.h"
#include "error_codes.h"

#include <zephyr/drivers/gpio.h>
#include <zephyr/drivers/i2c.h>
#include <zephyr/device.h>

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

/*! internal structure which saves OSAL internal parameter */
struct device_config {
    volatile uint8_t init_done;                /*!< 0 < ::as7058_osal_initialize was successful called */
    volatile as7058_osal_interrupt_t callback; /*!< saves the link to the callback function of the chiplib */
};

/******************************************************************************
 *                                  GLOBALS                                   *
 ******************************************************************************/

/*! I2C address of the AS7058 */
static const uint8_t g_i2c_address = 0x55;



/*! Create internal instance of the device configuration */
static struct device_config g_device_config;

/* Pull the GPIO spec from DT: */
static const struct gpio_dt_spec sens_int = GPIO_DT_SPEC_GET(DT_PATH(zephyr_user), my_sensor_int_gpios);
/* Declare the callback object */
// Add this near the top with other definitions
static struct gpio_callback as7058_cb_data;

const struct device *i2c_dev1 = DEVICE_DT_GET(DT_NODELABEL(i2c21));

static K_SEM_DEFINE(as7058_irq_sem, 0, 1);     /* ISR gives, worker takes */
static struct k_work as7058_bottom_half;

static void as7058_bottom_half_work(struct k_work *work);
static void as7058_interrupt_handler(const struct device *dev,
                                     struct gpio_callback *cb,
                                     uint32_t pins);

/******************************************************************************
 *                               LOCAL FUNCTIONS                              *
 ******************************************************************************/

/* --- Bottom-half worker: safe context for I2C/chiplib --- */
static void as7058_bottom_half_work(struct k_work *work)
{
    if (!g_device_config.init_done || g_device_config.callback == NULL) {
        return;
    }

    /* Drain until INT de-asserts (handles coalesced/fast IRQs) */
    for (;;) {
        err_code_t res = g_device_config.callback();

        int lvl = gpio_pin_get_dt(&sens_int);
        //printk("chiplib cb res=%d, line=%d\n", res, lvl);

        /* Re-read line; if inactive, we're done */
        int pin_state = gpio_pin_get_dt(&sens_int);
        if (res != ERR_SUCCESS || pin_state) {
            /* pin_state == 1 means line is HIGH. If ACTIVE_LOW, HIGH == idle */
            break;
        }
        /* Optional: yield a bit if needed */
        /* k_yield(); */
    }
}

/* --- Top-half ISR: keep it tiny --- */
static void as7058_interrupt_handler(const struct device *dev,
                                     struct gpio_callback *cb,
                                     uint32_t pins)
{
    ARG_UNUSED(dev);
    ARG_UNUSED(cb);
    ARG_UNUSED(pins);


     int lvl = gpio_pin_get_dt(&sens_int);
   // printk("AS7058 IRQ fired, line now=%d (0=active if ACTIVE_LOW)\n", lvl);
    /* Wake the bottom half. If IRQs can coalesce, a sem is fine too: */
    k_work_submit(&as7058_bottom_half);
}

/* --- Init: configure GPIO + IRQ + worker --- */
err_code_t as7058_osal_initialize(void)
{
    err_code_t result = ERR_SUCCESS;

    if (g_device_config.init_done) {
        as7058_osal_shutdown();
    }

    if (!device_is_ready(i2c_dev1)) {
        return ERR_SYSTEM_CONFIG;
    }
    if (!gpio_is_ready_dt(&sens_int)) {
        return ERR_SYSTEM_CONFIG;
    }

    /* If line is open-drain active-low, ensure DT has PULL_UP|ACTIVE_LOW.
       Here we just configure as input; flags come from DT. */
    int ret = gpio_pin_configure_dt(&sens_int, GPIO_INPUT);
    if (ret) {
        return ERR_SYSTEM_CONFIG;
    }

    k_work_init(&as7058_bottom_half, as7058_bottom_half_work);

    gpio_init_callback(&as7058_cb_data, as7058_interrupt_handler,
                       BIT(sens_int.pin));
    gpio_add_callback(sens_int.port, &as7058_cb_data);

    /* If DT has GPIO_ACTIVE_LOW, EDGE_TO_ACTIVE => falling edge.
       Otherwise, pick rising/falling explicitly per your wiring. */
    // ret = gpio_pin_interrupt_configure_dt(&as7058_sensor_spec,
    //                                       GPIO_INT_EDGE_TO_ACTIVE);

    g_device_config.callback = NULL; /* will be set by register_int_handler */
    g_device_config.init_done = TRUE;
    return result;
}

 err_code_t as7058_osal_irq_enable(bool en)
{
    if (!g_device_config.init_done) return ERR_PERMISSION;

    if (en) {
        /* With ACTIVE_LOW in DT, TO_ACTIVE == falling edge */
        int ret = gpio_pin_interrupt_configure_dt(&sens_int, GPIO_INT_EDGE_RISING);
        return ret ? ERR_SYSTEM_CONFIG : ERR_SUCCESS;
    } else {
        gpio_pin_interrupt_configure_dt(&sens_int, GPIO_INT_DISABLE);
        return ERR_SUCCESS;
    }
}





err_code_t as7058_osal_write_registers(uint8_t address,
                                      uint16_t number,
                                      const uint8_t *p_values)
{
   if (FALSE == g_device_config.init_done) {
        return ERR_PERMISSION;
    }

    M_CHECK_NULL_POINTER(p_values);

    /* Build [reg + data] buffer */
    uint8_t buf[number + 1];
    buf[0] = address;
    memcpy(&buf[1], p_values, number);

    int ret = i2c_write(i2c_dev1, buf, number + 1, g_i2c_address);
    if (ret < 0) {
        return ERR_DATA_TRANSFER;
    }

    return ERR_SUCCESS;
}


err_code_t as7058_osal_read_registers(uint8_t address, uint16_t number, uint8_t *p_values)
{
    if (FALSE == g_device_config.init_done) {
        return ERR_PERMISSION;
    }

    M_CHECK_NULL_POINTER(p_values);

    /* Repeated-start: write 1 byte (reg addr), then read `number` bytes */
    int ret = i2c_write_read(i2c_dev1, g_i2c_address, &address, 1, p_values, number);
    if (ret < 0) {
        return ERR_DATA_TRANSFER;
    }

    return ERR_SUCCESS;
}

/* As before, but keep the log to verify registration happens */
err_code_t as7058_osal_register_int_handler(as7058_osal_interrupt_t cb_fn)
{
    if (!g_device_config.init_done) return ERR_PERMISSION;
   // printk("as7058_osal_register_int_handler called, cb=%p\n", (void*)cb_fn);
    g_device_config.callback = cb_fn;
    return ERR_SUCCESS;
}


err_code_t as7058_osal_shutdown(void)
{
    gpio_pin_interrupt_configure_dt(&sens_int, GPIO_INT_DISABLE);
    gpio_remove_callback(sens_int.port, &as7058_cb_data);

    memset(&g_device_config, 0, sizeof(g_device_config));
    return ERR_SUCCESS;
}