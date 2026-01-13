/*
 * Copyright (c) 2022-2023 Nordic Semiconductor ASA
 *
 * SPDX-License-Identifier: LicenseRef-Nordic-5-Clause
 */

#include <zephyr/random/random.h>
#include <zephyr/sys_clock.h>
#include <zephyr/sys/__assert.h>

#include <zephyr/bluetooth/bluetooth.h>
#include <zephyr/bluetooth/conn.h>
#include <bluetooth/adv_prov.h>

#include <zephyr/logging/log.h>
LOG_MODULE_REGISTER(BLE2, LOG_LEVEL_DBG);

#include "bt_adv_helper.h"

/* According to Fast Pair specification RPA rotation must be synchronized with generating new salt
 * for Acount Key Filter advertising data. The RPA rotation must occur at least every 15 minutes
 * while the device is actively advertising in Fast Pair not discoverable mode. The value of this
 * timeout must be lower than CONFIG_BT_RPA_TIMEOUT to ensure that RPA rotation will always trigger
 * update of Account Key Filter advertising data.
 */
#define RPA_TIMEOUT_NOT_DISC 		(13 * SEC_PER_MIN)
#define RPA_TIMEOUT_OFFSET_MAX 		(2 * SEC_PER_MIN)
#define RPA_TIMEOUT_FAST_PAIR_MAX 	(15 * SEC_PER_MIN)

BUILD_ASSERT(RPA_TIMEOUT_FAST_PAIR_MAX < CONFIG_BT_RPA_TIMEOUT);

static bool adv_helper_pairing_mode;
static bool adv_helper_new_adv_session;

static void rpa_rotate_fn(struct k_work *w);
static K_WORK_DELAYABLE_DEFINE(rpa_rotate, rpa_rotate_fn);

/* --- MODIFIED --- Moved adv_param to file scope and made it non-const */
static struct bt_le_adv_param adv_param = {
	.id = BT_ID_DEFAULT,
	.options = BT_LE_ADV_OPT_CONN,
	.interval_min = BT_GAP_ADV_FAST_INT_MIN_1,
	.interval_max = BT_GAP_ADV_FAST_INT_MAX_1,
	.peer = NULL,
};


static void connected(struct bt_conn *conn, uint8_t err)
{
	if (!err) {
		int ret = k_work_cancel_delayable(&rpa_rotate);

		__ASSERT_NO_MSG(ret == 0);
		ARG_UNUSED(ret);
	}
}

BT_CONN_CB_DEFINE(conn_callbacks) = {
	.connected 		= connected,
};

static int adv_start_internal(void)
{
	struct bt_le_oob oob;
	int err = bt_le_adv_stop();

	if (err) {
		LOG_ERR("Cannot stop advertising (err: %d)", err);
		return err;
	}

	/* Generate new Resolvable Private Address (RPA). */
	err = bt_le_oob_get_local(BT_ID_DEFAULT, &oob);
	if (err) {
		LOG_ERR("Cannot trigger RPA rotation (err: %d)", err);
		return err;
	}

	size_t ad_len = bt_le_adv_prov_get_ad_prov_cnt();
	size_t sd_len = bt_le_adv_prov_get_sd_prov_cnt();
	struct bt_data ad[ad_len];
	struct bt_data sd[sd_len];

	struct bt_le_adv_prov_adv_state state;
	struct bt_le_adv_prov_feedback fb;

	state.pairing_mode = adv_helper_pairing_mode;
	state.in_grace_period = false;
	state.rpa_rotated = true;
	state.new_adv_session = adv_helper_new_adv_session;
	state.adv_handle = 0;

	adv_helper_new_adv_session = false;

	err = bt_le_adv_prov_get_ad(ad, &ad_len, &state, &fb);
	if (err) {
		LOG_ERR("Cannot get advertising data (err: %d)", err);
		return err;
	}

	err = bt_le_adv_prov_get_sd(sd, &sd_len, &state, &fb);
	if (err) {
		LOG_ERR("Cannot get scan response data (err: %d)", err);
		return err;
	}

	/*
	 * According to Fast Pair specification, the advertising interval should be no longer than
	 * 100 ms when discoverable and no longer than 250 ms when not discoverable.
	 * The local adv_param struct is removed and now uses the file-scope one which can be modified.
	 */
	err = bt_le_adv_start(&adv_param, ad, ad_len, sd, sd_len);

	if ((!err) && (!adv_helper_pairing_mode)) {
		unsigned int rpa_timeout_ms = RPA_TIMEOUT_NOT_DISC * MSEC_PER_SEC;
		int8_t rand;

		err = sys_csrand_get(&rand, sizeof(rand));
		if (!err) {
			rpa_timeout_ms += ((int)(RPA_TIMEOUT_OFFSET_MAX * MSEC_PER_SEC)) *
					rand / INT8_MAX;
		} else {
			LOG_WRN("Cannot get random RPA timeout (err: %d). Used fixed value", err);
		}

		__ASSERT_NO_MSG(rpa_timeout_ms <= RPA_TIMEOUT_FAST_PAIR_MAX * MSEC_PER_SEC);
		int ret = k_work_schedule(&rpa_rotate, K_MSEC(rpa_timeout_ms));

		__ASSERT_NO_MSG(ret == 1);
		ARG_UNUSED(ret);
	}

	return err;

}

static void rpa_rotate_fn(struct k_work *w)
{
	(void)adv_start_internal();
}

int bt_adv_helper_adv_start(bool pairing_mode, bool new_adv_session)
{
	int ret = k_work_cancel_delayable(&rpa_rotate);

	__ASSERT_NO_MSG(ret == 0);
	ARG_UNUSED(ret);

	adv_helper_pairing_mode = pairing_mode;
	adv_helper_new_adv_session = new_adv_session;

	/* --- ADDED --- Reset interval on a new session (e.g. after disconnect) */
	if (new_adv_session) {
		adv_param.interval_min = BT_GAP_ADV_FAST_INT_MIN_1;
		adv_param.interval_max = BT_GAP_ADV_FAST_INT_MAX_1;
		LOG_DBG("Advertising interval reset to default.");
	}
	/* --- END ADDED --- */


	LOG_INF("Looking for a new peer: %s", pairing_mode ? "yes" : "no");

	return adv_start_internal();
}

int bt_adv_helper_adv_stop(void)
{
	int ret = k_work_cancel_delayable(&rpa_rotate);

	__ASSERT_NO_MSG(ret == 0);
	ARG_UNUSED(ret);

	return bt_le_adv_stop();
}

/* --- ADDED --- New function to increase the advertising interval */
void bt_adv_helper_increase_interval(void)
{
	/* Increase interval by 30 ms. 30ms / 0.625ms/unit = 48 units. */
	const uint16_t increase_units = 48;
	/* Set max interval to ~1 second (1600 units * 0.625ms) */
	const uint16_t max_interval_units = 1600;

	if (adv_param.interval_max < max_interval_units) {
		adv_param.interval_min += increase_units;
		adv_param.interval_max += increase_units;
	} else {
		/* If max is reached, wrap around to default for the next cycle */
		adv_param.interval_min = BT_GAP_ADV_FAST_INT_MIN_1;
		adv_param.interval_max = BT_GAP_ADV_FAST_INT_MAX_1;
	}
	LOG_INF("Next advertising interval set to %u units (~%u ms)",
		adv_param.interval_max, (uint32_t)(adv_param.interval_max * 625 / 1000));
}
/* --- END ADDED --- */