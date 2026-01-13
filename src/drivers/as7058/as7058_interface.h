/******************************************************************************
 * Copyright © 2022 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

#ifndef __AS7058_INTERFACE_H__
#define __AS7058_INTERFACE_H__

/*!
 * \file        as7058_interface.h
 * \authors     ARIT
 * \copyright   ams OSRAM
 * \addtogroup  chiplib_ifce_group
 *
 * \brief This is the chip library interface module for ams vital signs chip AS7058.
 *
 * @{
 */

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include "as7058_typedefs.h"
#include "error_codes.h"
#include "std_inc.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

/*! Bit fields of the interrupts. */
typedef struct {
    uint8_t sequencer : 1;      /*!< Interrupt for sequencer. */
    uint8_t fifo_threshold : 1; /*!< FIFO threshold reached. */
    uint8_t fifo_overflow : 1;  /*!< FIFO overflow. */
    uint8_t led_lowvds : 1;     /*!< LED current does not reach the expected value. */
    uint8_t asat : 1;           /*!< Analog saturation. */
    uint8_t vcsel : 1;          /*!< VCSEL interrupt. */
    uint8_t leadoff : 1;        /*!< Lead-Off interrupt. */
    uint8_t iir_overflow : 1;   /*!< IIR overflow interrupt. */
} as7058_interrupt_t;

/*! LED ID defintion. */
typedef enum {
    AS7058_LED1 = 0, /*!< LED 1. */
    AS7058_LED2 = 1, /*!< LED 2. */
    AS7058_LED3 = 2, /*!< LED 3. */
    AS7058_LED4 = 3, /*!< LED 4. */
    AS7058_LED5 = 4, /*!< LED 5. */
    AS7058_LED6 = 5, /*!< LED 6. */
    AS7058_LED7 = 6, /*!< LED 7. */
    AS7058_LED8 = 7, /*!< LED 8. */

    AS7058_LED_NUM_MAX = 8 /*!< Maximum supported LED IDs. */
} as7058_led_ids_t;

/*! ECG multiplexer signals. */
enum as7058_ecg_mux_signals {
    AS7058_ECG_MUX_UNDEFINED = 0, /*!< Undefined multiplexer configuration. */
    AS7058_ECG_MUX_ECG_AMP = 1,   /*!< ECG amplifier output. */
    AS7058_ECG_MUX_ECG_LEAD = 2,  /*!< ECG lead detection output. */
    AS7058_ECG_MUX_I = 3,         /*!< BioZ I channel. */
    AS7058_ECG_MUX_Q = 4,         /*!< BioZ Q channel. */
    AS7058_ECG_MUX_EDA = 5,       /*!< EDA channel. */
    AS7058_ECG_MUX_TEMP = 6,      /*!< Temperature channel */

    AS7058_ECG_MUX_NUM = 7 /*!< Maximum supported ECG multiplexer configurations. */
};

/*! Type of ::as7058_ecg_mux_signals. */
typedef uint8_t as7058_ecg_mux_signals_t;

/*! Sub-sample post-processing modes. */
enum as7058_pp_modes {
    AS7058_PP_MODE_NORMAL = 0, /*!< Normal post-processing mode. */
    AS7058_PP_MODE_INVERT = 1,
    AS7058_PP_MODE_SUBTRACT_OFFSET = 2,
    AS7058_PP_MODE_WRITE_TO_OFFSET = 3,

    AS7058_PP_MODE_NUM = 4 /*!< Number of post-processing modes. */
};

/*! Type of ::as7058_pp_modes. */
typedef uint8_t as7058_pp_modes_t;

/*! Number of available ECG sub-samples. */
#define AS7058_NUM_ECG_SUBS 3

/******************************************************************************
 *                                 FUNCTIONS                                  *
 ******************************************************************************/

/*!
 * \brief Writes a value to a 8-bit register.
 *
 * \param[in] reg_addr              Register address. See ::as7058_reg_addresses.
 * \param[in] reg_val               New register value.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 */
err_code_t as7058_ifce_write_register(as7058_reg_addresses_t reg_addr, uint8_t reg_val);

/*!
 * \brief Reads a value from a 8-bit register.
 *
 * \param[in] reg_addr              Register address. See ::as7058_reg_addresses.
 * \param[out] p_reg_val            Pointer where new register value can be saved.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 */
err_code_t as7058_ifce_read_register(as7058_reg_addresses_t reg_addr, uint8_t *p_reg_val);

/*!
 * \brief Resets the chip to default register configuration.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 * \retval ::ERR_POINTER            Detected NULL pointer for data.
 */
err_code_t as7058_ifce_reset_chip(void);

/*!
 * \brief Reads the silicon ID of the chip.
 *
 * \note Default silicon ID should be ::AS7058_SILICON_ID.
 *
 * \param[out] p_silicon_id         Pointer to memory, where silicon ID can be saved.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 * \retval ::ERR_POINTER            Detected NULL pointer for data.
 */
err_code_t as7058_ifce_get_silicon_id(uint8_t *p_silicon_id);

/*!
 * \brief Reads the product ID of the chip.
 *
 * \param[out] p_product_id         Pointer to memory, where product ID can be saved.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 * \retval ::ERR_POINTER            Detected NULL pointer for data.
 */
err_code_t as7058_ifce_get_product_id(uint8_t *p_product_id);

/*!
 * \brief Reads the revision of the chip.
 *
 * \param[out] p_revision           Pointer to memory, where revision can be saved.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 * \retval ::ERR_POINTER            Detected NULL pointer for data.
 */
err_code_t as7058_ifce_get_revision(uint8_t *p_revision);

/*!
 * \brief Reads the error of the 2k ohm resistor.
 *
 * \param[out] p_2k_error           2k ohm resistor error in thousandths of a
 *                                  percent, i.e. an error of 5% is represented
 *                                  using value 5000.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 * \retval ::ERR_POINTER            Detected NULL pointer for data.
 */
err_code_t as7058_ifce_get_2k_error(int16_t *p_2k_error);

/*!
 * \brief Reads the error of the 1M ohm resistor.
 *
 * \param[out] p_1meg_error         1M ohm resistor error in thousandths of a
 *                                  percent, i.e. an error of 5% is represented
 *                                  using value 5000.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 * \retval ::ERR_POINTER            Detected NULL pointer for data.
 */
err_code_t as7058_ifce_get_1meg_error(int16_t *p_1meg_error);

/*!
 * \brief Reads the temperature ADC value that was recorded during production.
 *
 * \param[out] p_temp_adc           Temperature value in ADC counts (20 bits).
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 * \retval ::ERR_POINTER            Detected NULL pointer for data.
 */
err_code_t as7058_ifce_get_temp_adc_production(uint32_t *p_temp_adc);

/*!
 * \brief Clears the FIFO.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 */
err_code_t as7058_ifce_clear_fifo(void);

/*!
 * \brief Reads the FIFO level.
 *
 * \param[out] p_fifo_level         Pointer to memory, where revision can be saved.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 * \retval ::ERR_POINTER            Detected NULL pointer for data.
 */
err_code_t as7058_ifce_get_fifo_level(uint16_t *p_fifo_level);

/*!
 * \brief Reads the FIFO threshold.
 *
 * \param[out] p_fifo_threshold     Pointer to memory, where current FIFO threshold can be saved.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 * \retval ::ERR_POINTER            Detected NULL pointer for data.
 */
err_code_t as7058_ifce_get_fifo_threshold(uint16_t *p_fifo_threshold);

/*!
 * \brief Reads common interrupt status register.
 *
 * \param[out] p_status     Pointer to memory, where interrupt status can be saved.
 *                          Flags are described here: ::as7058_interrupt_status_t.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 * \retval ::ERR_POINTER            Detected NULL pointer for data.
 */
err_code_t as7058_ifce_get_interrupt_status(as7058_interrupt_t *p_status);

/*!
 * \brief Reads the selected sub interrupt status registers.
 *
 * \note FIFO overflow and FIFO threshold interrupts are ignored by this function.
 *
 * \note There is no sub status register for IIR. Therefore, the state of irqs.iir_overflow will be used for that.
 *
 * \param[in] irqs                  Selection of interrupt status register which shall be read.
 * \param[out] p_status_registers   Pointer to memory, where the activated status registers can be saved.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 * \retval ::ERR_POINTER            Detected NULL pointer for data.
 */
err_code_t as7058_ifce_get_sub_status_registers(as7058_interrupt_t irqs, as7058_status_events_t *p_status_registers);

/*!
 * \brief Reads the activated interrupt sources.
 *
 * \param[out] p_enable     Pointer to memory, where the state can be saved.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 * \retval ::ERR_POINTER            Detected NULL pointer for data.
 */
err_code_t as7058_ifce_get_interrupt_enable(as7058_interrupt_t *p_enable);

/*!
 * \brief Sets a group of registers with one function call.
 *
 * \param[in] id            Id of the register group. See ::as7058_reg_group_ids.
 * \param[in] p_data        Pointer to the register data, like ::as7058_reg_group_led_t.
 * \param[in] size          Sets the size of register data in bytes.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_ARGUMENT           Register group id is not supported.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 * \retval ::ERR_POINTER            Detected NULL pointer for data.
 * \retval ::ERR_SIZE               Size of the data buffer is wrong.
 */
err_code_t as7058_ifce_set_reg_group(as7058_reg_group_ids_t id, const uint8_t *p_data, uint8_t size);

/*!
 * \brief Gets a group of registers with one function call.
 *
 * \param[in] id                Id of the register group. See ::as7058_reg_group_ids.
 * \param[out] p_data           Pointer to the register data, like ::as7058_reg_group_led_t.
 * \param[inout] p_size         IN: Maximum buffer size, OUT: Size in byte of the register group data.
 *                              The maximum size is defined in ::AS7058_MAX_GROUP_SIZE.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_ARGUMENT           Register group id is not supported.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 * \retval ::ERR_POINTER            Detected NULL pointer for data.
 * \retval ::ERR_SIZE               Size of the data buffer is wrong.
 */
err_code_t as7058_ifce_get_reg_group(as7058_reg_group_ids_t id, uint8_t *p_data, uint8_t *p_size);

/*!
 * \brief Reads the current sample periods for PPG and the two ECG sequencers.
 *
 * \param[out] p_ppg_sample_period_us       Pointer to memory, where PPG period [us] will be saved.
 * \param[out] p_ecg_seq1_sample_period_us  Pointer to memory, where ECG sequencer 1 period [us] will be saved.
 * \param[out] p_ecg_seq2_sample_period_us  Pointer to memory, where ECG sequencer 2 period [us] will be saved.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 * \retval ::ERR_POINTER            Detected NULL pointer for data.
 */
err_code_t as7058_ifce_get_sample_periods(uint32_t *p_ppg_sample_period_us, uint32_t *p_ecg_seq1_sample_period_us,
                                          uint32_t *p_ecg_seq2_sample_period_us);

/*!
 * \brief Starts a measurement.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 */
err_code_t as7058_ifce_start_measurement(void);

/*!
 * \brief Stops a measurement.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 */
err_code_t as7058_ifce_stop_measurement(void);

/*!
 * \brief Reads FIFO data.
 *
 * \param[out] p_data               Pointer to memory, where FIFO data can be saved.
 * \param[in] data_num              Size in bytes how many data shall be read.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 * \retval ::ERR_POINTER            Detected NULL pointer for data.
 */
err_code_t as7058_ifce_get_fifo_data(uint8_t *p_data, uint16_t data_num);

/*!
 * \brief Gets the current activated sub-samples inside the FIFO.
 *
 * \param[out] p_fifo_map           Pointer to memory, where the state of the activated sub-samples can be saved.
 *                                  See ::as7058_sub_sample_flags.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 * \retval ::ERR_POINTER            Detected NULL pointer for data.
 */
err_code_t as7058_ifce_get_fifo_mapping(uint32_t *p_fifo_map);

/*!
 * \brief Gets the current activated sub-samples where SAR is activated.
 *
 * \param[out] p_active_sar         Pointer to memory, where a bit field of the sub-samples with enabled SAR can be
 *                                  saved. See ::as7058_sub_sample_flags.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 * \retval ::ERR_POINTER            Detected NULL pointer for data.
 */
err_code_t as7058_ifce_get_active_sar_sub_samples(uint32_t *p_active_sar);

/*!
 * \brief Gets the configured SAR data transfer mode (Register bit sar_data_en).
 *
 * \param[out] p_sar_transfer_mode  Pointer to memory, where the current SAR data transfer mode can be saved. See
 *                                  ::as7058_sar_transfer_mode.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 * \retval ::ERR_POINTER            Detected NULL pointer for data.
 */
err_code_t as7058_ifce_get_sar_transfer_mode(as7058_sar_transfer_mode_t *p_sar_transfer_mode);

/*!
 * \brief Sets the LED current.
 *
 * \param[in] led_id         ID of the LED. See ::as7058_led_ids_t.
 * \param[in] current        New current. See register definition for SEQ1_LED1_CURR.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_ARGUMENT           Parameter led_id is not supported.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 */
err_code_t as7058_ifce_set_led_current(as7058_led_ids_t led_id, uint8_t current);

/*!
 * \brief Gets the LED current.
 *
 * \param[in] led_id         ID of the LED. See ::as7058_led_ids_t.
 * \param[out] p_current     Pointer to memory where the current can be saved.
 *                           See register definition for SEQ1_LED1_CURR.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_ARGUMENT           Parameter led_id is not supported.
 * \retval ::ERR_POINTER            Detected NULL pointer for data.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 */
err_code_t as7058_ifce_get_led_current(as7058_led_ids_t led_id, uint8_t *p_current);

/*!
 * \brief Sets the PD offset currents (IOS).
 *
 * \note PD offset can't be set for ECG channels.
 *
 * \param[in] sub_sample_id         Sub-sample ID. Only PPG1 and PPG2 sub-samples are supported. See
 *                                  ::as7058_sub_sample_ids.
 * \param[in] ios                   PD offset current.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 * \retval ::ERR_ARGUMENT           Sub-sample ID is wrong.
 */
err_code_t as7058_ifce_set_pd_offset(as7058_sub_sample_ids_t sub_sample_id, uint8_t ios);

/*!
 * \brief Gets the PD offset current (IOS) of a given sub-sample ID.
 *
 * \param[in] sub_sample_id         Sub-sample ID. Only PPG1 and PPG2 sub-samples are supported. See
 *                                  ::as7058_sub_sample_ids.
 * \param[in] p_ios                 Pointer to memory where the PD offset current can be saved.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 * \retval ::ERR_POINTER            Detected NULL pointer.
 * \retval ::ERR_ARGUMENT           Sub-sample ID is wrong.
 */
err_code_t as7058_ifce_get_pd_offset(as7058_sub_sample_ids_t sub_sample_id, uint8_t *p_ios);

/*!
 * \brief Gets the LED configuration for a given sub-sample ID.
 *
 * \param[in] sub_sample_id         Sub-sample description. Only PPG1 and PPG2 sub-samples are supported. See
 *                                  ::as7058_sub_sample_ids.
 * \param[out] p_led_config         Pointer to memory where the LED configuration can be saved.
 *                                  This is a bit array. More than one LED can be enabled for the sub sample.
 *                                  The bit position corresponds to ::as7058_led_ids_t.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 * \retval ::ERR_POINTER            Detected NULL pointer.
 * \retval ::ERR_ARGUMENT           Argument is invalid.
 */
err_code_t as7058_ifce_get_sub_sample_led_config(as7058_sub_sample_ids_t sub_sample_id, uint8_t *p_led_config);

/*!
 * \brief Sets the photodiode configuration for a given sub-sample ID.
 *
 * \param[in] sub_sample_id         Sub-sample ID. Only PPG1 and PPG2 sub-samples are supported. See
 *                                  ::as7058_sub_sample_ids.
 * \param[in] pd_config             Photodiode configuration to set. This is a bit array containing the photodiodes
 *                                  mapped to the given sub-sample ID. Multiple photodiodes can be mapped to a single
 *                                  sub-sample ID. Bit 0 corresponds to PD1, bit 7 corresponds to PD8.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 * \retval ::ERR_ARGUMENT           Argument is invalid.
 */
err_code_t as7058_ifce_set_sub_sample_pd_config(as7058_sub_sample_ids_t sub_sample_id, uint8_t pd_config);

/*!
 * \brief Gets the photodiode configuration for a given sub-sample ID.
 *
 * \param[in] sub_sample_id         Sub-sample ID. Only PPG1 and PPG2 sub-samples are supported. See
 *                                  ::as7058_sub_sample_ids.
 * \param[out] p_pd_config          Pointer to memory where the photodiode configuration can be saved. This is a bit
 *                                  array containing the photodiodes mapped to the given sub-sample ID. Multiple
 *                                  photodiodes can be mapped to a single sub-sample ID. Bit 0 corresponds to PD1, bit 7
 *                                  corresponds to PD8.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 * \retval ::ERR_POINTER            Detected NULL pointer.
 * \retval ::ERR_ARGUMENT           Argument is invalid.
 */
err_code_t as7058_ifce_get_sub_sample_pd_config(as7058_sub_sample_ids_t sub_sample_id, uint8_t *p_pd_config);

/*!
 * \brief Sets the post-processing mode for a given sub-sample ID.
 *
 * Note that this function does not perform a single atomic register write. To set the pre-processing mode, the function
 * reads a register value, modifies it in software, and writes the modified value back to the register.
 *
 * \param[in] sub_sample_id         Sub-sample ID. Only PPG1 and PPG2 sub-samples are supported. See
 *                                  ::as7058_sub_sample_ids.
 * \param[in] pp_mode               Post-processing mode to set. See ::as7058_pp_modes_t.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 * \retval ::ERR_POINTER            Detected NULL pointer.
 * \retval ::ERR_ARGUMENT           Argument is invalid.
 */
err_code_t as7058_ifce_set_sub_sample_pp_mode(as7058_sub_sample_ids_t sub_sample_id, as7058_pp_modes_t pp_mode);

/*!
 * \brief Gets the post-processing mode for a given sub-sample ID.
 *
 * \param[in] sub_sample_id         Sub-sample ID. Only PPG1 and PPG2 sub-samples are supported. See
 *                                  ::as7058_sub_sample_ids.
 * \param[out] p_pp_mode            Pointer to memory where the post-processing mode can be saved. See
 *                                  ::as7058_pp_modes_t.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 * \retval ::ERR_POINTER            Detected NULL pointer.
 * \retval ::ERR_ARGUMENT           Argument is invalid.
 */
err_code_t as7058_ifce_get_sub_sample_pp_mode(as7058_sub_sample_ids_t sub_sample_id, as7058_pp_modes_t *p_pp_mode);

/*!
 * \brief Gets the ECG multiplexer configuration.
 *
 * \param[out] p_mux_signals        Multiplexer signal configuration. Needs to be an array of 3.
 *                                  See ::as7058_ecg_mux_signals_t.
 * \param[in] num_mux_signals       Number of elements of 'p_mux_signals'
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 * \retval ::ERR_POINTER            Detected NULL pointer for data.
 * \retval ::ERR_ARGUMENT           Argument 'num_mux_signals' is not 3.
 */
err_code_t as7058_ifce_get_ecg_mux_config(as7058_ecg_mux_signals_t *p_mux_signals, uint8_t num_mux_signals);

/*!
 * \brief Sets the PPG sample period multiplier. This sets the sample period for all PPG sub-samples.
 *
 * \param[in] multiplier            Base sample period multiplier. The base sample period is 31.25 microseconds. The
 *                                  resulting sample period is obtained by incrementing the multiplier by one and by
 *                                  multiplying the base sample period by the incremented multiplier. For example, a
 *                                  multiplier value of 9 results in sample period of (9 + 1) * 31.25 microseconds =
 *                                  312.5 microseconds.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 */
err_code_t as7058_ifce_set_ppg_sample_period_multiplier(uint16_t multiplier);

/*!
 * \brief Gets the PPG sample period multiplier.
 *
 * \param[out] p_multiplier         Points to the location where the base sample period multiplier will be written to.
 *                                  The base sample period is 31.25 microseconds. The resulting sample period is
 *                                  obtained by incrementing the multiplier by one and by multiplying the base sample
 *                                  period by the incremented multiplier. For example, a multiplier value of 9 results
 *                                  in sample period of (9 + 1) * 31.25 microseconds = 312.5 microseconds.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_DATA_TRANSFER      Error during communication with sensor.
 * \retval ::ERR_POINTER            Detected NULL pointer.
 */
err_code_t as7058_ifce_get_ppg_sample_period_multiplier(uint16_t *p_multiplier);

/*! @} */

#endif /* __AS7058_INTERFACE_H__ */
