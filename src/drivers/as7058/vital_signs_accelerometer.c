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

#include <stdint.h>
#include <string.h>

#include "error_codes.h"
#include "lis2dh12.h"
#include "std_inc.h"
#include "vital_signs_acc_osal.h"
#include "vital_signs_accelerometer.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

#define MULT_MS 1000
#ifndef ACC_I2C_ADDR
#define ACC_I2C_ADDR 0x19
#endif
#define NORMALIZED_MARKER 0x0001

/*! States of the module. */
typedef enum {
    ACC_STATE_UNINITIALIZED = 0, /*!< Module is in uninitialized state. */
    ACC_STATE_UNCONFIGURED,      /*!< Module is not configured yet. */
    ACC_STATE_CONFIGURED,        /*!< Module is configured. */
    ACC_STATE_PROCESSING         /*!< Module is in processing state. */
} acc_state_t;

/*! Checks whether the module is in the expected state and returns ::ERR_PERMISSION otherwise. */
#define M_CHECK_STATE(expected)                                                                                        \
    do {                                                                                                               \
        if (g_state != (expected)) {                                                                                   \
            return ERR_PERMISSION;                                                                                     \
        }                                                                                                              \
    } while (0)

/******************************************************************************
 *                                  GLOBALS                                   *
 ******************************************************************************/

/*! The current state of the module. */
static volatile acc_state_t g_state = ACC_STATE_UNINITIALIZED;

static const char *gp_osal_config;

static uint8_t g_simulate_acc = FALSE;
static uint32_t g_last_ms_tick = 0;
static uint32_t g_start_ms_tick = 0;
static uint32_t g_sim_update_time_ms = 0;

/******************************************************************************
 *                               LOCAL FUNCTIONS                              *
 ******************************************************************************/
/* The accelerometer returns values left aligned in a signed 16-bit representation (actually it is 2x 8-bit
   registers). The mg/LSB in the datasheet means that the LSB bit is the last of the 12 bits and not the real
   LSB of a 16-bit value.

   The LIS2DH12 has 12 bits and 12 mg/LSB. So in a 16-bit representation it has 12/16 = 0.75 mg/LSB.

   The output accelerometer data is expected to be scaled to 0.5 mg/LSB (approximately).
*/
static err_code_t normalize_samples(lis2dh12_data_t *p_acc_data, uint8_t num_acc_data)
{
    uint8_t i, j;
    int32_t sample;

    M_CHECK_NULL_POINTER(p_acc_data);
    if (0 == num_acc_data) {
        return ERR_ARGUMENT;
    }

    for (i = 0; i < num_acc_data; i++) {
        for (j = 0; j < sizeof(lis2dh12_data_t) / sizeof(p_acc_data[0].i16bit[0]); j++) {

            /* convert from 0.75 mg to 0.5 mg (=multiply by 1.5) */
            sample = ((p_acc_data[i].i16bit[j] * 3) / 2) | NORMALIZED_MARKER;

            /* check saturation */
            if (sample < INT16_MIN) {
                p_acc_data[i].i16bit[j] = INT16_MIN;
            } else if (sample > INT16_MAX) {
                p_acc_data[i].i16bit[j] = INT16_MAX;
            } else {
                p_acc_data[i].i16bit[j] = (int16_t)sample;
            }
        }
    }

    return ERR_SUCCESS;
}

static err_code_t i2c_transfer(void *p_param, uint8_t dev_addr, uint8_t *p_send_data, uint16_t send_len,
                               uint8_t *p_recv_data, uint16_t recv_len)
{
    return vs_acc_osal_transfer_i2c((char *)p_param, dev_addr, p_send_data, send_len, p_recv_data, recv_len);
}

/******************************************************************************
 *                             GLOBAL FUNCTIONS                               *
 ******************************************************************************/

err_code_t vs_acc_initialize(const char *p_config)
{
    err_code_t err;

    (void)vs_acc_shutdown();

    err = lis2dh12_initialize(ACC_I2C_ADDR, i2c_transfer, (void *)p_config);

    /* use accelerometer simulation driver if identification failed */
    g_simulate_acc = (ERR_SUCCESS != err) ? TRUE : FALSE;
    g_sim_update_time_ms = 0;
    gp_osal_config = p_config;
    g_state = ACC_STATE_UNCONFIGURED;

    return ERR_SUCCESS;
}

err_code_t vs_acc_set_sample_period(uint32_t sample_period_us)
{
    err_code_t err = ERR_SUCCESS;
    lis2dh12_config_t lis_cfg = {LIS2DH12_ODR_10Hz, LIS2DH12_16g, LIS2DH12_HR_12bit, LIS2DH12_FIFO_MODE};

    if (ACC_STATE_UNINITIALIZED == g_state || ACC_STATE_PROCESSING == g_state) {
        return ERR_PERMISSION;
    }

    switch (sample_period_us) {
    case 1000000:
        lis_cfg.odr = LIS2DH12_ODR_1Hz;
        break;
    case 100000:
        lis_cfg.odr = LIS2DH12_ODR_10Hz;
        break;
    case 40000:
        lis_cfg.odr = LIS2DH12_ODR_25Hz;
        break;
    case 20000:
        lis_cfg.odr = LIS2DH12_ODR_50Hz;
        break;
    case 10000:
        lis_cfg.odr = LIS2DH12_ODR_100Hz;
        break;
    case 5000:
        lis_cfg.odr = LIS2DH12_ODR_200Hz;
        break;
    case 0:
        lis_cfg.odr = LIS2DH12_POWER_DOWN;
        break;
    default:
        return ERR_ARGUMENT;
        break;
    }

    if (!g_simulate_acc) {
        err = lis2dh12_configure(&lis_cfg);
    }

    g_sim_update_time_ms = sample_period_us / MULT_MS;
    g_state = ACC_STATE_CONFIGURED;

    return err;
}

err_code_t vs_acc_shutdown(void)
{
    err_code_t err;

    if (g_state != ACC_STATE_UNINITIALIZED && !g_simulate_acc) {
        err = lis2dh12_shutdown();
    } else {
        err = ERR_SUCCESS;
    }

    g_state = ACC_STATE_UNINITIALIZED;
    gp_osal_config = NULL;
    return err;
}

err_code_t vs_acc_start(void)
{
    err_code_t err;

    M_CHECK_STATE(ACC_STATE_CONFIGURED);

    if (!g_simulate_acc) {
        err = lis2dh12_start();
    } else {
        err = vs_acc_osal_get_tick(gp_osal_config, &g_last_ms_tick);
        g_start_ms_tick = g_last_ms_tick;
    }

    g_state = ACC_STATE_PROCESSING;

    return err;
}

err_code_t vs_acc_stop(void)
{
    err_code_t err;

    if (ACC_STATE_UNINITIALIZED == g_state) {
        return ERR_PERMISSION;
    } else if (ACC_STATE_PROCESSING != g_state) {
        return ERR_SUCCESS;
    } else if (!g_simulate_acc) {
        err = lis2dh12_stop();
    } else {
        err = ERR_SUCCESS;
    }

    g_state = ACC_STATE_CONFIGURED;
    return err;
}

err_code_t vs_acc_get_data(vs_acc_data_t *p_acc_data, uint8_t *p_num_acc_data)
{
    err_code_t err = ERR_SUCCESS;
    uint32_t tick_ms;
    uint32_t delta;
    uint8_t num_acc_data;

    M_CHECK_STATE(ACC_STATE_PROCESSING);

    M_CHECK_NULL_POINTER(p_acc_data);
    M_CHECK_NULL_POINTER(p_num_acc_data);
    M_CHECK_ARGUMENT_LOWER(0, *p_num_acc_data);

    if (0 == g_sim_update_time_ms) {
        /* Return function directly if sample period is zero */
        *p_num_acc_data = 0;
        return ERR_SUCCESS;
    }

    if (!g_simulate_acc) {
        err = lis2dh12_read((lis2dh12_data_t *)p_acc_data, p_num_acc_data);
        if ((ERR_SUCCESS == err) && (0 < *p_num_acc_data)) {
            err = normalize_samples((lis2dh12_data_t *)p_acc_data, *p_num_acc_data);
        }
    } else {
        err = vs_acc_osal_get_tick(gp_osal_config, &tick_ms);
        if (ERR_SUCCESS == err) {
            /* overflow handling. Here we will miss some data but that is not critical. */
            if (tick_ms < g_start_ms_tick) {
                g_start_ms_tick = 0;
                g_last_ms_tick = 0;
            }
            delta = (tick_ms - g_start_ms_tick) - (g_last_ms_tick - g_start_ms_tick);

            num_acc_data = delta / g_sim_update_time_ms;
            if (*p_num_acc_data > num_acc_data) {
                *p_num_acc_data = num_acc_data;
            }
            if (0 < num_acc_data) {
                g_last_ms_tick =
                    g_start_ms_tick + (((tick_ms - g_start_ms_tick) / g_sim_update_time_ms) * g_sim_update_time_ms);
            }
            memset(p_acc_data, 0, sizeof(p_acc_data[0]) * (*p_num_acc_data));
        } else {
            *p_num_acc_data = 0;
        }
    }
    return err;
}
