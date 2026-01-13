/******************************************************************************
 * Copyright by ams AG                                                        *
 * All rights are reserved.                                                   *
 *                                                                            *
 * IMPORTANT - PLEASE READ CAREFULLY BEFORE COPYING, INSTALLING OR USING      *
 * THE SOFTWARE.                                                              *
 *                                                                            *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS        *
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT          *
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS          *
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT   *
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,      *
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT           *
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,      *
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY      *
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT        *
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE      *
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.       *
 ******************************************************************************/

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include "error_codes.h"
#include "lis2dh12.h"
#include "std_inc.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/
#define MAX_I2C_BUFF_SIZE 32
#define MAX_FIFO_SAMPLES 31

/*! States of accelerometer driver. */
typedef enum {
    LIS2DH12_STATE_UNINITIALIZED = 0, /*!< Uninitialized state. */
    LIS2DH12_STATE_UNCONFIGURED,      /*!< Not configured state. */
    LIS2DH12_STATE_CONFIGURED,        /*!< Configuration state. */
    LIS2DH12_STATE_PROCESSING         /*!< Processing state. */
} lis2dh12_state_t;

typedef struct lis2dh12_descr {
    volatile lis2dh12_state_t lib_state;
    i2c_transfer_callback p_i2c_transfer;
    void *p_callback_param;
    uint8_t i2c_addr;
    stmdev_ctx_t stmdev_ctx;
    lis2dh12_config_t cfg;
} lis2dh12_descr_t;

/******************************************************************************
 *                                  GLOBALS                                   *
 ******************************************************************************/
static lis2dh12_descr_t g_lis2dh12_descr;

/******************************************************************************
 *                               LOCAL FUNCTIONS                              *
 ******************************************************************************/
static int32_t __stmdev_write(void *p_handle, uint8_t reg, uint8_t *p_data, uint16_t len)
{
    uint32_t i;
    static uint8_t i2c_buff[MAX_I2C_BUFF_SIZE + 1];
    err_code_t err = ERR_SUCCESS;
    lis2dh12_descr_t *p_dev = (lis2dh12_descr_t *)p_handle;

    M_CHECK_NULL_POINTER(p_dev);
    M_CHECK_NULL_POINTER(p_data);
    M_CHECK_ARGUMENT_LOWER_EQUAL(len, MAX_I2C_BUFF_SIZE);

    i2c_buff[0] = (len > 1) ? (reg | 0x80) : (reg);
    for (i = 0; i < len; i++) {
        i2c_buff[i + 1] = p_data[i];
    }

    err = p_dev->p_i2c_transfer(p_dev->p_callback_param, (uint8_t)p_dev->i2c_addr, i2c_buff, len + 1, NULL, 0);
    return (int32_t)err;
}

static int32_t __stmdev_read(void *p_handle, uint8_t reg, uint8_t *p_data, uint16_t len)
{
    err_code_t err = ERR_SUCCESS;
    lis2dh12_descr_t *p_dev = (lis2dh12_descr_t *)p_handle;

    M_CHECK_NULL_POINTER(p_dev);
    M_CHECK_NULL_POINTER(p_data);

    reg = (len > 1) ? (reg | 0x80) : (reg);
    err = p_dev->p_i2c_transfer(p_dev->p_callback_param, (uint8_t)p_dev->i2c_addr, &reg, sizeof(reg), p_data, len);
    return (int32_t)err;
}

static err_code_t __lis2dh12_data_read(lis2dh12_data_t *p_data, uint8_t *p_samples)
{
    lis2dh12_reg_t reg;
    uint8_t samples = 0;
    err_code_t err = ERR_SUCCESS;
    stmdev_ctx_t *p_ctx = &g_lis2dh12_descr.stmdev_ctx;

    while (samples < *p_samples && ERR_SUCCESS == err) {
        /* check for new data */
        err = lis2dh12_xl_data_ready_get(p_ctx, &reg.byte);

        /* Read accelerometer data */
        if (ERR_SUCCESS == err) {
            if (reg.byte) {
                err = lis2dh12_acceleration_raw_get(p_ctx, p_data[samples].u8bit);
                if (ERR_SUCCESS == err) {
                    samples++;
                }

            } else {
                break;
            }
        }

        if (ERR_SUCCESS != err) {
            err = ERR_DATA_TRANSFER;
        }
    }

    *p_samples = samples;
    return err;
}

static err_code_t __lis2dh12_fifo_read(lis2dh12_data_t *p_data, uint8_t *p_samples)
{
    uint8_t samples, fifo_lvl;
    err_code_t err = ERR_SUCCESS;
    stmdev_ctx_t *p_ctx = &g_lis2dh12_descr.stmdev_ctx;

    samples = 0;
    /* check for new data */
    fifo_lvl = 0;
    err = lis2dh12_fifo_data_level_get(p_ctx, &fifo_lvl);

    if ((ERR_SUCCESS == err) && ((MAX_FIFO_SAMPLES - 1) <= fifo_lvl)) {
        err = ERR_OVERFLOW;
    }

    /* read fifo data */
    while ((fifo_lvl) && (samples < *p_samples) && (ERR_SUCCESS == err)) {
        err = lis2dh12_acceleration_raw_get(p_ctx, p_data[samples].u8bit);
        if (ERR_SUCCESS == err) {
            samples++;
            fifo_lvl--;
        }
    }

    if ((ERR_SUCCESS != err) && (ERR_OVERFLOW != err)) {
        err = ERR_DATA_TRANSFER;
    }

    *p_samples = samples;
    return err;
}

/******************************************************************************
 *                              GLOBAL FUNCTIONS                              *
 ******************************************************************************/
err_code_t lis2dh12_initialize(uint8_t i2c_addr, i2c_transfer_callback p_i2c_transfer, void *p_callback_param)
{
    uint8_t id;
    err_code_t err;
    stmdev_ctx_t *p_ctx = &g_lis2dh12_descr.stmdev_ctx;

    M_CHECK_NULL_POINTER(p_i2c_transfer);

    (void)lis2dh12_shutdown();

    /* initialize config structure and check device id */
    g_lis2dh12_descr.i2c_addr = i2c_addr;
    g_lis2dh12_descr.p_i2c_transfer = p_i2c_transfer;
    g_lis2dh12_descr.p_callback_param = p_callback_param;
    g_lis2dh12_descr.stmdev_ctx.write_reg = __stmdev_write;
    g_lis2dh12_descr.stmdev_ctx.read_reg = __stmdev_read;
    g_lis2dh12_descr.stmdev_ctx.handle = &g_lis2dh12_descr;

    err = lis2dh12_device_id_get(p_ctx, &id);
    if (ERR_SUCCESS != err) {
        /* Do nothing */
    } else if (id != LIS2DH12_ID) {
        err = ERR_IDENTIFICATION;
    } else {
        g_lis2dh12_descr.lib_state = LIS2DH12_STATE_UNCONFIGURED;
    }

    if (ERR_SUCCESS != err) {
        /* Cleanup the interface in case of errors */
        (void)lis2dh12_shutdown();
    }

    return err;
}

err_code_t lis2dh12_configure(const lis2dh12_config_t *p_cfg)
{
    if ((LIS2DH12_STATE_CONFIGURED != g_lis2dh12_descr.lib_state) &&
        (LIS2DH12_STATE_UNCONFIGURED != g_lis2dh12_descr.lib_state)) {
        return ERR_PERMISSION;
    }
    M_CHECK_NULL_POINTER(p_cfg);

    g_lis2dh12_descr.cfg = *p_cfg;
    g_lis2dh12_descr.lib_state = LIS2DH12_STATE_CONFIGURED;

    return ERR_SUCCESS;
}

err_code_t lis2dh12_start()
{
    err_code_t err;
    stmdev_ctx_t *p_ctx = &g_lis2dh12_descr.stmdev_ctx;
    lis2dh12_config_t *p_cfg = &g_lis2dh12_descr.cfg;

    if (LIS2DH12_STATE_CONFIGURED != g_lis2dh12_descr.lib_state) {
        return ERR_PERMISSION;
    }

    /* Enable Block Data Update. */
    err = lis2dh12_block_data_update_set(p_ctx, PROPERTY_ENABLE);

    /* Set scale. */
    if (ERR_SUCCESS == err) {
        err = lis2dh12_full_scale_set(p_ctx, p_cfg->fs);
    }

    /* Set device in continuous mode with given resolution. */
    if (ERR_SUCCESS == err) {
        err = lis2dh12_operating_mode_set(p_ctx, p_cfg->op_md);
    }

    /* clear fifo before setting another mode */
    if (ERR_SUCCESS == err) {
        err = lis2dh12_fifo_mode_set(p_ctx, LIS2DH12_BYPASS_MODE);
    }

    /* enable fifo mode if requested */
    if (ERR_SUCCESS == err && p_cfg->fifo_en) {
        err = lis2dh12_fifo_mode_set(p_ctx, LIS2DH12_FIFO_MODE);
    }

    if (ERR_SUCCESS == err) {
        err = lis2dh12_fifo_set(p_ctx, p_cfg->fifo_en);
    }

    /* Set Output Data Rate. */
    if (ERR_SUCCESS == err) {
        err = lis2dh12_data_rate_set(p_ctx, p_cfg->odr);
    }

    if (ERR_SUCCESS == err) {
        g_lis2dh12_descr.lib_state = LIS2DH12_STATE_PROCESSING;
    }

    return err;
}

err_code_t lis2dh12_stop()
{
    err_code_t err;
    stmdev_ctx_t *p_ctx = &g_lis2dh12_descr.stmdev_ctx;

    if (LIS2DH12_STATE_CONFIGURED > g_lis2dh12_descr.lib_state) {
        return ERR_PERMISSION;
    }

    /* Power down the device. */
    err = lis2dh12_data_rate_set(p_ctx, LIS2DH12_POWER_DOWN);

    /* set fifo mode to bypass for clearing fifo */
    if (ERR_SUCCESS == err) {
        err = lis2dh12_fifo_mode_set(p_ctx, LIS2DH12_BYPASS_MODE);
    }

    if (ERR_SUCCESS == err) {
        g_lis2dh12_descr.lib_state = LIS2DH12_STATE_CONFIGURED;
    }

    return err;
}

err_code_t lis2dh12_read(lis2dh12_data_t *p_data, uint8_t *p_samples)
{
    err_code_t err;
    lis2dh12_config_t *p_cfg = &g_lis2dh12_descr.cfg;

    if (LIS2DH12_STATE_PROCESSING != g_lis2dh12_descr.lib_state) {
        return ERR_PERMISSION;
    }

    M_CHECK_NULL_POINTER(p_data);
    M_CHECK_NULL_POINTER(p_samples);

    if (FALSE == p_cfg->fifo_en) {
        err = __lis2dh12_data_read(p_data, p_samples);
    } else {
        err = __lis2dh12_fifo_read(p_data, p_samples);
    }

    return err;
}

err_code_t lis2dh12_shutdown()
{
    lis2dh12_stop();
    memset(&g_lis2dh12_descr, 0, sizeof(g_lis2dh12_descr));
    return ERR_SUCCESS;
}
