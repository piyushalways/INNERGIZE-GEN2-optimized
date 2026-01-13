/******************************************************************************
 * Copyright © 2022 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include "as7058_pd_offset_calibration.h"

#include "as7058_chiplib.h"
#include "as7058_extract.h"
#include "as7058_interface.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

/*! Bitmask for field ppgmod*X*_en of register PPGMOD*X*_CFG1. */
#define REG_MASK__PPGMODX_CFG1__PPGMODX_EN 0x80

/*! Bitmask for field ppgmod*X*_ios_mux of register PPGMOD*X*_CFG1. */
#define REG_MASK__PPGMODX_CFG1__PPGMODX_IOS_MUX 0x40

/*! Bitmask for field ppgmod*X*_ios_dir of register PPGMOD*X*_CFG2. */
#define REG_MASK__PPGMODX_CFG2__PPGMODX_IOS_DIR 0x80

/*! Bitmask for field ppgmod*X*_ios_fs of register PPGMOD*X*_CFG2. */
#define REG_MASK__PPGMODX_CFG2__PPGMODX_IOS_FS 0x70

/*! Bitmask for the lower two bits of field ppg_mode_sub*X* of register PPG_MODE*X* (measurement mode). */
#define REG_MASK__PPG_MODEX__PPG_MODE_SUBX_MODE 0x03

/*! Bitmask for the upper three bits of field ppg_mode_sub*X* of register PPG_MODE*X* (number of measurements). */
#define REG_MASK__PPG_MODEX__PPG_MODE_SUBX_NUM 0x1C

/*! Bitmask for field sample_num of register SAMPLE_NUM. */
#define REG_MASK__SAMPLE_NUM__SAMPLE_NUM 0xFF

/*! Bitmask for field sar_ppg*X*_en of register AOC_SAR_PPG*X*. */
#define REG_MASK__AOC_SAR_PPGX__SAR_PPGX_EN 0xFF

/*! Bitmask for register PWR_ON where the bit representing PPG1 in field pwr_on is set. */
#define REG_VAL__PWR_ON__PWR_ON__PPG1 0x04

/*! Bitmask for register PWR_ON where the bit representing PPG2 in field pwr_on is set. */
#define REG_VAL__PWR_ON__PWR_ON__PPG2 0x08

/*! Bitmask for register PWR_ISO where the bit representing PPG1 in field pwr_iso is set. */
#define REG_VAL__PWR_ISO__PWR_ISO__PPG1 0x04

/*! Bitmask for register PWR_ISO where the bit representing PPG2 in field pwr_iso is set. */
#define REG_VAL__PWR_ISO__PWR_ISO__PPG2 0x08

/*! Bitmask for register PPG_MODE*X* where the bits representing number of measurements = 1 in field ppg_mode_sub*X* are
 *  set. */
#define REG_VAL__PPG_MODEX__PPG_MODE_SUBX_NUM__ONE 0x00

/*! Bitmask for register PPG_MODE*X* where the bits representing measurement mode = single in field ppg_mode_sub*X* are
 *  set. */
#define REG_VAL__PPG_MODEX__PPG_MODE_SUBX_MODE__SINGLE 0x00

/*! Bitmask for register SAMPLE_NUM where the bits representing continuous operation in field sample_num are set. */
#define REG_VAL__SAMPLE_NUM__SAMPLE_NUM__CONTINUOUS 0x00

/*! Bitmask for register AOC_SAR_PPG*X* where no bits are set in field sar_ppg*X*_en. */
#define REG_VAL__AOC_SAR_PPGX__SAR_PPGX_EN__NONE 0x00

/*! Size of a single SAR photodiode offset current step. SAR controls the upper 4 bits of the 8-bit current value,
 *  resulting in a step size of 16. */
#define AS7058_PD_OFFSET_CALIBRATION_PD_OFFSET_SAR_STEP_SIZE 16

/*! Bitmask for the photodiode offset current bits that are not controlled by SAR. */
#define AS7058_PD_OFFSET_CALIBRATION_PD_OFFSET_PROGRAMMABLE_MASK 0x0F

/*! Clears the bits set in the `clear` bitmask and then sets the bits set in the `set` bitmask. */
#define M_CLEAR_AND_SET_BITS(value, clear, set) ((uint8_t)(((value) & (~(clear))) | (set)))

/*! States of the module. */
enum as7058_pd_offset_calibration_state {
    AS7058_PD_OFFSET_CALIBRATION_STATE_UNINITIALIZED = 0, /*!< Module is uninitialized. */
    AS7058_PD_OFFSET_CALIBRATION_STATE_UNCONFIGURED,      /*!< Module is initialized, but unconfigured. */
    AS7058_PD_OFFSET_CALIBRATION_STATE_CONFIGURED,        /*!< Module is initialized and configured. */
    AS7058_PD_OFFSET_CALIBRATION_STATE_MEASUREMENT, /*!< Module is initialized, configured, and currently measuring. */
};

/*! Type definition for ::as7058_pd_offset_calibration_state. */
typedef uint8_t as7058_pd_offset_calibration_state_t;

/*! Type of a calibration point measurement. */
enum as7058_pd_offset_calibration_point_type {
    AS7058_PD_OFFSET_CALIBRATION_POINT_TYPE_ZERO = 0, /*!< Zero calibration point. Both DACs are set to the same
                                                           current. */
    AS7058_PD_OFFSET_CALIBRATION_POINT_TYPE_STEP,     /*!< Step calibration point. Current of secondary DAC is one SAR
                                                           step higher than current of primary DAC. */
};

/*! Type definition for ::as7058_pd_offset_calibration_point_type. */
typedef uint8_t as7058_pd_offset_calibration_point_type_t;

/*! Chip configuration values modified for calibration. */
struct as7058_pd_offset_calibration_config_backup {
    uint8_t ppg1_pd_offset; /*!< Photodiode offset current of the selected sub-sample in PPG modulator 1. */
    uint8_t ppg2_pd_offset; /*!< Photodiode offset current of the selected sub-sample in PPG modulator 2. */
    uint16_t ppg_sample_period_multiplier; /*!< Base sample period multiplier for PPG sub-samples. */
    uint8_t pd_config;                     /*!< Photodiode mapping for the selected sub-sample. */
    as7058_pp_modes_t pp_mode;             /*!< Post-processing mode of the selected sub-sample. */
    uint8_t reg_val_pwr_on;                /*!< Value of register ::AS7058_REGADDR_PWR_ON. */
    uint8_t reg_val_pwr_iso;               /*!< Value of register ::AS7058_REGADDR_PWR_ISO. */
    uint8_t reg_val_ppgmod1_cfg1;          /*!< Value of register ::AS7058_REGADDR_PPGMOD1_CFG1. */
    uint8_t reg_val_ppgmod1_cfg2;          /*!< Value of register ::AS7058_REGADDR_PPGMOD1_CFG2. */
    uint8_t reg_val_ppgmod2_cfg1;          /*!< Value of register ::AS7058_REGADDR_PPGMOD2_CFG1. */
    uint8_t reg_val_ppgmod2_cfg2;          /*!< Value of register ::AS7058_REGADDR_PPGMOD2_CFG2. */
    uint8_t reg_val_ppg_modex;    /*!< Value of the PPG_MODE*X* register corresponding to the selected sub-sample. */
    uint8_t reg_val_sample_num;   /*!< Value of register ::AS7058_REGADDR_SAMPLE_NUM. */
    uint8_t reg_val_aoc_sar_ppg1; /*!< Value of register ::AS7058_REGADDR_AOC_SAR_PPG1. */
    uint8_t reg_val_aoc_sar_ppg2; /*!< Value of register ::AS7058_REGADDR_AOC_SAR_PPG2. */
};

/******************************************************************************
 *                                  GLOBALS                                   *
 ******************************************************************************/

/*! Current state of the module. */
static as7058_pd_offset_calibration_state_t g_state = AS7058_PD_OFFSET_CALIBRATION_STATE_UNINITIALIZED;

/*! Sub-sample used for calibration. */
static as7058_sub_sample_ids_t g_sub_sample_id;

/*! Number of samples that are averaged per calibration point measurement. */
static uint16_t g_target_num_averages;

/*! Base sample period multiplier for PPG sub-samples to use during calibration. */
static uint16_t g_ppg_sample_period_multiplier;

/*! The photodiode offset current as present in the configuration before start of calibration. Note that the module
 *  checks that the SAR-controlled bits are set to zero before calibration is started. */
static uint8_t g_programmable_pd_offset;

/*! Chip configuration backed up before the configuration was patched for calibration. */
static struct as7058_pd_offset_calibration_config_backup g_config_backup;

/*! Number of the current photodiode offset SAR step. A total of
 *  ::AS7058_PD_OFFSET_CALIBRATION_COMPENSATION_TABLE_ELEMENTS_NUM steps are performed. All measurements have been
 *  performed when this variable is set to a value greater than
 *  ::AS7058_PD_OFFSET_CALIBRATION_COMPENSATION_TABLE_ELEMENTS_NUM.*/
static uint8_t g_current_pd_offset_sar_step;

/*! Type of the current calibration point measurement. */
static as7058_pd_offset_calibration_point_type_t g_current_calibration_point;

/*! Number of samples of the current calibration point measurement that are accumulated in ::g_current_sample_accu.*/
static uint16_t g_current_sample_cnt;

/*! Accumulator of samples of the current calibration point measurement. */
static uint32_t g_current_sample_accu;

/*! Output structure, contains the resulting calibration table. */
static as7058_pd_offset_calibration_result_t g_result;

/*! Averaged result of the last ::AS7058_PD_OFFSET_CALIBRATION_POINT_TYPE_STEP measurement. */
static uint32_t g_calibration_point_zero_result;

/*! State required to extract samples from FIFO data. */
static as7058_extract_metadata_t g_extract_metadata;

/******************************************************************************
 *                               LOCAL FUNCTIONS                              *
 ******************************************************************************/

/*! Gets an ::as7058_modulator value and an ::as7058_sub_sample value from a
 *  ::as7058_sub_sample_ids value. ::as7058_sub_sample_ids values that do not correspond to a sub-sample of PPG
 *  modulators 1 or 2 generate an error. */
static err_code_t get_modulator_and_sub_sample_from_sub_sample_id(as7058_sub_sample_ids_t sub_sample_id,
                                                                  as7058_modulator_t *p_modulator,
                                                                  as7058_modulator_sub_sample_t *p_sub_sample)
{
    if (sub_sample_id >= AS7058_SUB_SAMPLE_ID_PPG1_SUB1 && sub_sample_id <= AS7058_SUB_SAMPLE_ID_PPG1_SUB8) {
        *p_modulator = AS7058_MODULATOR_PPG1;
        *p_sub_sample = sub_sample_id - AS7058_SUB_SAMPLE_ID_PPG1_SUB1;
    } else if (sub_sample_id >= AS7058_SUB_SAMPLE_ID_PPG2_SUB1 && sub_sample_id <= AS7058_SUB_SAMPLE_ID_PPG2_SUB8) {
        *p_modulator = AS7058_MODULATOR_PPG2;
        *p_sub_sample = sub_sample_id - AS7058_SUB_SAMPLE_ID_PPG2_SUB1;
    } else {
        /* Only PPG sub-sample IDs are supported */
        return ERR_ARGUMENT;
    }

    return ERR_SUCCESS;
}

/*! Backups the chip configuration and updates it for the calibration of the given modulator. */
static err_code_t patch_chip_configuration(as7058_sub_sample_ids_t sub_sample_id, uint32_t fifo_map,
                                           uint16_t ppg_sample_period_multiplier,
                                           struct as7058_pd_offset_calibration_config_backup *p_config_backup,
                                           uint8_t *p_configured_primary_programmable_pd_offset)
{
    as7058_modulator_t modulator;
    as7058_modulator_sub_sample_t sub_sample;
    M_CHECK_SUCCESS(get_modulator_and_sub_sample_from_sub_sample_id(sub_sample_id, &modulator, &sub_sample));

    /* Check that the provided sub-sample is enabled. */
    if (!(fifo_map & M_AS7058_SUB_SAMPLE_ID_TO_FLAG(sub_sample_id))) {
        return ERR_SENSOR_CONFIG;
    }

    /* Backup configurations that are about to be modified. Registers which cannot be accessed using higher-level
     * functions are accessed directly. */
    M_CHECK_SUCCESS(
        as7058_ifce_get_pd_offset(AS7058_SUB_SAMPLE_ID_PPG1_SUB1 + sub_sample, &p_config_backup->ppg1_pd_offset));
    M_CHECK_SUCCESS(
        as7058_ifce_get_pd_offset(AS7058_SUB_SAMPLE_ID_PPG2_SUB1 + sub_sample, &p_config_backup->ppg2_pd_offset));
    M_CHECK_SUCCESS(as7058_ifce_get_ppg_sample_period_multiplier(&p_config_backup->ppg_sample_period_multiplier));
    M_CHECK_SUCCESS(as7058_ifce_get_sub_sample_pd_config(sub_sample_id, &p_config_backup->pd_config));
    M_CHECK_SUCCESS(as7058_ifce_get_sub_sample_pp_mode(sub_sample_id, &p_config_backup->pp_mode));
    M_CHECK_SUCCESS(as7058_ifce_read_register(AS7058_REGADDR_PWR_ON, &p_config_backup->reg_val_pwr_on));
    M_CHECK_SUCCESS(as7058_ifce_read_register(AS7058_REGADDR_PWR_ISO, &p_config_backup->reg_val_pwr_iso));
    M_CHECK_SUCCESS(as7058_ifce_read_register(AS7058_REGADDR_PPGMOD1_CFG1, &p_config_backup->reg_val_ppgmod1_cfg1));
    M_CHECK_SUCCESS(as7058_ifce_read_register(AS7058_REGADDR_PPGMOD1_CFG2, &p_config_backup->reg_val_ppgmod1_cfg2));
    M_CHECK_SUCCESS(as7058_ifce_read_register(AS7058_REGADDR_PPGMOD2_CFG1, &p_config_backup->reg_val_ppgmod2_cfg1));
    M_CHECK_SUCCESS(as7058_ifce_read_register(AS7058_REGADDR_PPGMOD2_CFG2, &p_config_backup->reg_val_ppgmod2_cfg2));
    M_CHECK_SUCCESS(
        as7058_ifce_read_register(AS7058_REGADDR_PPG_MODE1 + sub_sample, &p_config_backup->reg_val_ppg_modex));
    M_CHECK_SUCCESS(as7058_ifce_read_register(AS7058_REGADDR_SAMPLE_NUM, &p_config_backup->reg_val_sample_num));
    M_CHECK_SUCCESS(as7058_ifce_read_register(AS7058_REGADDR_AOC_SAR_PPG1, &p_config_backup->reg_val_aoc_sar_ppg1));
    M_CHECK_SUCCESS(as7058_ifce_read_register(AS7058_REGADDR_AOC_SAR_PPG2, &p_config_backup->reg_val_aoc_sar_ppg2));

    /* Update PPG sample period multiplier. */
    M_CHECK_SUCCESS(as7058_ifce_set_ppg_sample_period_multiplier(ppg_sample_period_multiplier));

    /* Clear photodiode mapping for the provided sub-sample. */
    M_CHECK_SUCCESS(as7058_ifce_set_sub_sample_pd_config(sub_sample_id, 0));

    /* Set post-processing mode of the provided sub-sample to normal. */
    M_CHECK_SUCCESS(as7058_ifce_set_sub_sample_pp_mode(sub_sample_id, AS7058_PP_MODE_NORMAL));

    /* Power-on both PPG modulators. */
    M_CHECK_SUCCESS(as7058_ifce_write_register(
        AS7058_REGADDR_PWR_ON, M_CLEAR_AND_SET_BITS(p_config_backup->reg_val_pwr_on, 0,
                                                    (REG_VAL__PWR_ON__PWR_ON__PPG1 | REG_VAL__PWR_ON__PWR_ON__PPG2))));
    M_CHECK_SUCCESS(as7058_ifce_write_register(
        AS7058_REGADDR_PWR_ISO,
        M_CLEAR_AND_SET_BITS(p_config_backup->reg_val_pwr_iso,
                             (REG_VAL__PWR_ISO__PWR_ISO__PPG1 | REG_VAL__PWR_ISO__PWR_ISO__PPG2), 0)));

    if (AS7058_MODULATOR_PPG1 == modulator) {
        /* Enable PPG1 modulator, disable PPG2 modulator, and connect PPG2 DAC (secondary DAC) to PPG1 modulator in
         * special mode. */
        M_CHECK_SUCCESS(as7058_ifce_write_register(AS7058_REGADDR_PPGMOD1_CFG1,
                                                   M_CLEAR_AND_SET_BITS(p_config_backup->reg_val_ppgmod1_cfg1,
                                                                        REG_MASK__PPGMODX_CFG1__PPGMODX_IOS_MUX,
                                                                        REG_MASK__PPGMODX_CFG1__PPGMODX_EN)));
        M_CHECK_SUCCESS(as7058_ifce_write_register(
            AS7058_REGADDR_PPGMOD1_CFG2,
            M_CLEAR_AND_SET_BITS(p_config_backup->reg_val_ppgmod1_cfg2, REG_MASK__PPGMODX_CFG2__PPGMODX_IOS_DIR, 0)));
        M_CHECK_SUCCESS(as7058_ifce_write_register(AS7058_REGADDR_PPGMOD2_CFG1,
                                                   M_CLEAR_AND_SET_BITS(p_config_backup->reg_val_ppgmod2_cfg1,
                                                                        REG_MASK__PPGMODX_CFG1__PPGMODX_EN,
                                                                        REG_MASK__PPGMODX_CFG1__PPGMODX_IOS_MUX)));
        M_CHECK_SUCCESS(as7058_ifce_write_register(
            AS7058_REGADDR_PPGMOD2_CFG2,
            M_CLEAR_AND_SET_BITS(p_config_backup->reg_val_ppgmod2_cfg2, REG_MASK__PPGMODX_CFG2__PPGMODX_IOS_FS,
                                 (REG_MASK__PPGMODX_CFG2__PPGMODX_IOS_DIR |
                                  (p_config_backup->reg_val_ppgmod1_cfg2 & REG_MASK__PPGMODX_CFG2__PPGMODX_IOS_FS)))));
    } else if (AS7058_MODULATOR_PPG2 == modulator) {
        /* Disable PPG1 modulator, enable PPG2 modulator, connect PPG1 DAC (secondary DAC) to PPG2 modulator in
         * special mode, set full-scale range of secondary DAC to range of PPG2 DAC (primary DAC). */
        M_CHECK_SUCCESS(as7058_ifce_write_register(AS7058_REGADDR_PPGMOD1_CFG1,
                                                   M_CLEAR_AND_SET_BITS(p_config_backup->reg_val_ppgmod1_cfg1,
                                                                        REG_MASK__PPGMODX_CFG1__PPGMODX_EN,
                                                                        REG_MASK__PPGMODX_CFG1__PPGMODX_IOS_MUX)));
        M_CHECK_SUCCESS(as7058_ifce_write_register(
            AS7058_REGADDR_PPGMOD1_CFG2,
            M_CLEAR_AND_SET_BITS(p_config_backup->reg_val_ppgmod1_cfg2, REG_MASK__PPGMODX_CFG2__PPGMODX_IOS_FS,
                                 (REG_MASK__PPGMODX_CFG2__PPGMODX_IOS_DIR |
                                  (p_config_backup->reg_val_ppgmod2_cfg2 & REG_MASK__PPGMODX_CFG2__PPGMODX_IOS_FS)))));
        M_CHECK_SUCCESS(as7058_ifce_write_register(AS7058_REGADDR_PPGMOD2_CFG1,
                                                   M_CLEAR_AND_SET_BITS(p_config_backup->reg_val_ppgmod2_cfg1,
                                                                        REG_MASK__PPGMODX_CFG1__PPGMODX_IOS_MUX,
                                                                        REG_MASK__PPGMODX_CFG1__PPGMODX_EN)));
        M_CHECK_SUCCESS(as7058_ifce_write_register(
            AS7058_REGADDR_PPGMOD2_CFG2,
            M_CLEAR_AND_SET_BITS(p_config_backup->reg_val_ppgmod2_cfg2, REG_MASK__PPGMODX_CFG2__PPGMODX_IOS_DIR, 0)));

    } else {
        return ERR_ARGUMENT;
    }

    /* Configure the provided sub-sample to number of measurements = 1 and measurement mode = single. */
    M_CHECK_SUCCESS(as7058_ifce_write_register(
        AS7058_REGADDR_PPG_MODE1 + sub_sample,
        M_CLEAR_AND_SET_BITS(
            p_config_backup->reg_val_ppg_modex,
            (REG_MASK__PPG_MODEX__PPG_MODE_SUBX_NUM | REG_MASK__PPG_MODEX__PPG_MODE_SUBX_MODE),
            (REG_VAL__PPG_MODEX__PPG_MODE_SUBX_NUM__ONE | REG_VAL__PPG_MODEX__PPG_MODE_SUBX_MODE__SINGLE))));

    /* Configure the sequencer to measure continuously. */
    M_CHECK_SUCCESS(as7058_ifce_write_register(AS7058_REGADDR_SAMPLE_NUM,
                                               M_CLEAR_AND_SET_BITS(p_config_backup->reg_val_sample_num,
                                                                    REG_MASK__SAMPLE_NUM__SAMPLE_NUM,
                                                                    REG_VAL__SAMPLE_NUM__SAMPLE_NUM__CONTINUOUS)));

    /* Disable use last SAR value for both PPG modulators. */
    M_CHECK_SUCCESS(as7058_ifce_write_register(AS7058_REGADDR_AOC_SAR_PPG1,
                                               M_CLEAR_AND_SET_BITS(p_config_backup->reg_val_aoc_sar_ppg1,
                                                                    REG_MASK__AOC_SAR_PPGX__SAR_PPGX_EN,
                                                                    REG_VAL__AOC_SAR_PPGX__SAR_PPGX_EN__NONE)));
    M_CHECK_SUCCESS(as7058_ifce_write_register(AS7058_REGADDR_AOC_SAR_PPG2,
                                               M_CLEAR_AND_SET_BITS(p_config_backup->reg_val_aoc_sar_ppg2,
                                                                    REG_MASK__AOC_SAR_PPGX__SAR_PPGX_EN,
                                                                    REG_VAL__AOC_SAR_PPGX__SAR_PPGX_EN__NONE)));

    /* Export the programmable photodiode offset current bits of the primary DAC. */
    if (AS7058_MODULATOR_PPG1 == modulator) {
        *p_configured_primary_programmable_pd_offset =
            p_config_backup->ppg1_pd_offset & AS7058_PD_OFFSET_CALIBRATION_PD_OFFSET_PROGRAMMABLE_MASK;
    } else if (AS7058_MODULATOR_PPG2 == modulator) {
        *p_configured_primary_programmable_pd_offset =
            p_config_backup->ppg2_pd_offset & AS7058_PD_OFFSET_CALIBRATION_PD_OFFSET_PROGRAMMABLE_MASK;
    } else {
        return ERR_ARGUMENT;
    }

    return ERR_SUCCESS;
}

/*! Restores the original chip configuration. */
static err_code_t restore_chip_configuration(as7058_sub_sample_ids_t sub_sample_id,
                                             struct as7058_pd_offset_calibration_config_backup *p_config_backup)
{
    as7058_modulator_t modulator;
    as7058_modulator_sub_sample_t sub_sample;
    M_CHECK_SUCCESS(get_modulator_and_sub_sample_from_sub_sample_id(sub_sample_id, &modulator, &sub_sample));

    /* Restore values from backup. */
    M_CHECK_SUCCESS(
        as7058_ifce_set_pd_offset(AS7058_SUB_SAMPLE_ID_PPG1_SUB1 + sub_sample, p_config_backup->ppg1_pd_offset));
    M_CHECK_SUCCESS(
        as7058_ifce_set_pd_offset(AS7058_SUB_SAMPLE_ID_PPG2_SUB1 + sub_sample, p_config_backup->ppg2_pd_offset));
    M_CHECK_SUCCESS(as7058_ifce_set_ppg_sample_period_multiplier(p_config_backup->ppg_sample_period_multiplier));
    M_CHECK_SUCCESS(as7058_ifce_set_sub_sample_pd_config(sub_sample_id, p_config_backup->pd_config));
    M_CHECK_SUCCESS(as7058_ifce_set_sub_sample_pp_mode(sub_sample_id, p_config_backup->pp_mode));
    M_CHECK_SUCCESS(as7058_ifce_write_register(AS7058_REGADDR_PWR_ON, p_config_backup->reg_val_pwr_on));
    M_CHECK_SUCCESS(as7058_ifce_write_register(AS7058_REGADDR_PWR_ISO, p_config_backup->reg_val_pwr_iso));
    M_CHECK_SUCCESS(as7058_ifce_write_register(AS7058_REGADDR_PPGMOD1_CFG1, p_config_backup->reg_val_ppgmod1_cfg1));
    M_CHECK_SUCCESS(as7058_ifce_write_register(AS7058_REGADDR_PPGMOD1_CFG2, p_config_backup->reg_val_ppgmod1_cfg2));
    M_CHECK_SUCCESS(as7058_ifce_write_register(AS7058_REGADDR_PPGMOD2_CFG1, p_config_backup->reg_val_ppgmod2_cfg1));
    M_CHECK_SUCCESS(as7058_ifce_write_register(AS7058_REGADDR_PPGMOD2_CFG2, p_config_backup->reg_val_ppgmod2_cfg2));
    M_CHECK_SUCCESS(
        as7058_ifce_write_register(AS7058_REGADDR_PPG_MODE1 + sub_sample, p_config_backup->reg_val_ppg_modex));
    M_CHECK_SUCCESS(as7058_ifce_write_register(AS7058_REGADDR_SAMPLE_NUM, p_config_backup->reg_val_sample_num));
    M_CHECK_SUCCESS(as7058_ifce_write_register(AS7058_REGADDR_AOC_SAR_PPG1, p_config_backup->reg_val_aoc_sar_ppg1));
    M_CHECK_SUCCESS(as7058_ifce_write_register(AS7058_REGADDR_AOC_SAR_PPG2, p_config_backup->reg_val_aoc_sar_ppg2));

    return ERR_SUCCESS;
}

/*! Sets the photodiode offset current of the primary DAC for the calibration of the given modulator. */
static err_code_t set_pd_offset_primary_dac(as7058_modulator_t modulator, as7058_modulator_sub_sample_t sub_sample,
                                            uint8_t pd_offset)
{
    as7058_sub_sample_ids_t sub_sample_id;
    if (AS7058_MODULATOR_PPG1 == modulator) {
        sub_sample_id = AS7058_SUB_SAMPLE_ID_PPG1_SUB1 + sub_sample;
    } else if (AS7058_MODULATOR_PPG2 == modulator) {
        sub_sample_id = AS7058_SUB_SAMPLE_ID_PPG2_SUB1 + sub_sample;
    } else {
        /* Only PPG modulators are supported */
        return ERR_ARGUMENT;
    }

    return as7058_ifce_set_pd_offset(sub_sample_id, pd_offset);
}

/*! Sets the photodiode offset current of the secondary DAC for the calibration of the given modulator. */
static err_code_t set_pd_offset_secondary_dac(as7058_modulator_t modulator, as7058_modulator_sub_sample_t sub_sample,
                                              uint8_t pd_offset)
{
    as7058_sub_sample_ids_t sub_sample_id;
    if (AS7058_MODULATOR_PPG1 == modulator) {
        sub_sample_id = AS7058_SUB_SAMPLE_ID_PPG2_SUB1 + sub_sample;
    } else if (AS7058_MODULATOR_PPG2 == modulator) {
        sub_sample_id = AS7058_SUB_SAMPLE_ID_PPG1_SUB1 + sub_sample;
    } else {
        /* Only PPG modulators are supported */
        return ERR_ARGUMENT;
    }

    return as7058_ifce_set_pd_offset(sub_sample_id, pd_offset);
}

/*! Extracts the calibration measurement samples from the provided FIFO data and accumulates them until the target
 *  sample count is reached. */
static err_code_t extract_and_accumulate_samples(as7058_sub_sample_ids_t sub_sample_id, const uint8_t *p_fifo_data,
                                                 uint16_t fifo_data_size, as7058_extract_metadata_t *p_extract_metadata,
                                                 uint32_t *p_sample_accu, uint16_t *p_sample_cnt,
                                                 uint16_t target_sample_cnt)
{
    /* Extract the samples from the FIFO data. */
    static uint32_t samples[AS7058_FIFO_DATA_BUFFER_SIZE / AS7058_FIFO_SAMPLE_SIZE];
    uint16_t samples_num = AS7058_FIFO_DATA_BUFFER_SIZE / AS7058_FIFO_SAMPLE_SIZE;
    p_extract_metadata->copy_recent_to_current = TRUE;
    M_CHECK_SUCCESS(
        as7058_extract_samples(sub_sample_id, p_fifo_data, fifo_data_size, samples, &samples_num, p_extract_metadata));

    /* Accumulate the samples until the target sample count is reached. Discard all remaining samples. */
    for (uint16_t i = 0; i < samples_num; i++) {
        if (*p_sample_cnt >= target_sample_cnt) {
            break;
        }

        *p_sample_accu += samples[i];
        (*p_sample_cnt)++;
    }

    return ERR_SUCCESS;
}

/******************************************************************************
 *                             GLOBAL FUNCTIONS                               *
 ******************************************************************************/

err_code_t as7058_pd_offset_calibration_initialize(void)
{
    g_state = AS7058_PD_OFFSET_CALIBRATION_STATE_UNCONFIGURED;

    return ERR_SUCCESS;
}

err_code_t as7058_pd_offset_calibration_configure(const as7058_pd_offset_calibration_config_t *p_config)
{
    /* Check whether module is initialized and not currently measuring. */
    if (g_state != AS7058_PD_OFFSET_CALIBRATION_STATE_UNCONFIGURED &&
        g_state != AS7058_PD_OFFSET_CALIBRATION_STATE_CONFIGURED) {
        return ERR_PERMISSION;
    }

    M_CHECK_NULL_POINTER(p_config);

    /* Check validity of configuration. num_averages must no exceed UINT32_MAX / AS7058_SAMPLE_MAX_VALUE to ensure that
     * the accumulator variable used for averaging never overflows. */
    as7058_modulator_t modulator;
    as7058_modulator_sub_sample_t sub_sample;
    M_CHECK_SUCCESS(get_modulator_and_sub_sample_from_sub_sample_id(p_config->sub_sample_id, &modulator, &sub_sample));
    if (p_config->reserved) {
        return ERR_ARGUMENT;
    }
    if (0 == p_config->num_averages || p_config->num_averages > (UINT32_MAX / AS7058_SAMPLE_MAX_VALUE)) {
        return ERR_ARGUMENT;
    }

    /* Save configuration. */
    g_sub_sample_id = p_config->sub_sample_id;
    g_target_num_averages = p_config->num_averages;
    g_ppg_sample_period_multiplier = p_config->ppg_sample_period_multiplier;
    g_state = AS7058_PD_OFFSET_CALIBRATION_STATE_CONFIGURED;

    return ERR_SUCCESS;
}

err_code_t as7058_pd_offset_calibration_start(as7058_meas_config_t meas_config)
{
    /* Check whether module is initialized, configured, and not currently measuring. */
    if (g_state != AS7058_PD_OFFSET_CALIBRATION_STATE_CONFIGURED) {
        return ERR_PERMISSION;
    }

    /* Backup and update current chip configuration is suitable for calibration of the given modulator. */
    M_CHECK_SUCCESS(patch_chip_configuration(g_sub_sample_id, meas_config.fifo_map, g_ppg_sample_period_multiplier,
                                             &g_config_backup, &g_programmable_pd_offset));

    /* Prepare metadata from extraction of samples from FIFO data. */
    g_extract_metadata.fifo_map = meas_config.fifo_map;
    g_extract_metadata.current.ppg1_sub = AS7058_SUB_SAMPLE_FLAG_NONE;
    g_extract_metadata.current.ppg2_sub = AS7058_SUB_SAMPLE_FLAG_NONE;
    g_extract_metadata.recent.ppg1_sub = AS7058_SUB_SAMPLE_FLAG_NONE;
    g_extract_metadata.recent.ppg2_sub = AS7058_SUB_SAMPLE_FLAG_NONE;
    g_extract_metadata.copy_recent_to_current = TRUE;

    /* The module will now perform a total of AS7058_PD_OFFSET_CALIBRATION_COMPENSATION_TABLE_ELEMENTS_NUM * 2
     * measurements. For the first measurement, the SAR-controlled bits of the photodiode offset currents of both DACs
     * are cleared, i.e. only the programmable bits remain set.
     *
     * For each subsequent measurement, function as7058_pd_offset_calibration_process alternatingly increments the
     * photodiode offset current of the primary DAC and the secondary DAC by one SAR step, starting with the primary
     * DAC. For example, for the second measurement the current of the primary DAC is incremented by one SAR step, while
     * for the third measurement the current of the secondary DAC is incremented by one SAR step. */
    g_current_calibration_point = AS7058_PD_OFFSET_CALIBRATION_POINT_TYPE_ZERO;
    g_current_pd_offset_sar_step = 0;
    g_current_sample_cnt = 0;
    g_current_sample_accu = 0;
    as7058_modulator_t modulator;
    as7058_modulator_sub_sample_t sub_sample;
    M_CHECK_SUCCESS(get_modulator_and_sub_sample_from_sub_sample_id(g_sub_sample_id, &modulator, &sub_sample));
    M_CHECK_SUCCESS(set_pd_offset_primary_dac(modulator, sub_sample, g_programmable_pd_offset));
    M_CHECK_SUCCESS(set_pd_offset_secondary_dac(modulator, sub_sample, g_programmable_pd_offset));

    g_state = AS7058_PD_OFFSET_CALIBRATION_STATE_MEASUREMENT;

    return ERR_SUCCESS;
}

err_code_t as7058_pd_offset_calibration_stop(void)
{
    if (AS7058_PD_OFFSET_CALIBRATION_STATE_UNINITIALIZED == g_state) {
        return ERR_PERMISSION;
    } else if (AS7058_PD_OFFSET_CALIBRATION_STATE_MEASUREMENT == g_state) {
        /* Restore original chip configuration. */
        M_CHECK_SUCCESS(restore_chip_configuration(g_sub_sample_id, &g_config_backup));

        g_state = AS7058_PD_OFFSET_CALIBRATION_STATE_CONFIGURED;
        return ERR_SUCCESS;
    } else { /* AS7058_PD_OFFSET_CALIBRATION_STATE_UNCONFIGURED, AS7058_PD_OFFSET_CALIBRATION_STATE_CONFIGURED */
        /* State is not modified by this function in all other states. */
        return ERR_SUCCESS;
    }
}

err_code_t as7058_pd_offset_calibration_process(uint8_t *p_fifo_data, uint16_t fifo_data_size,
                                                const as7058_pd_offset_calibration_result_t **const pp_result)
{
    M_CHECK_NULL_POINTER(p_fifo_data);
    M_CHECK_NULL_POINTER(pp_result);
    *pp_result = NULL;

    if (g_state != AS7058_PD_OFFSET_CALIBRATION_STATE_MEASUREMENT) {
        /* Module is not in measurement state. */
        return ERR_PERMISSION;
    }

    if (g_current_pd_offset_sar_step > AS7058_PD_OFFSET_CALIBRATION_COMPENSATION_TABLE_ELEMENTS_NUM) {
        /* Measurements are finished and results have already been provided */
        return ERR_NO_DATA;
    }

    M_CHECK_SUCCESS(extract_and_accumulate_samples(g_sub_sample_id, p_fifo_data, fifo_data_size, &g_extract_metadata,
                                                   &g_current_sample_accu, &g_current_sample_cnt,
                                                   g_target_num_averages));

    if (g_current_sample_cnt < g_target_num_averages) {
        /* Measurement needs to continue with current settings until enough samples have been acquired. */
        return ERR_NO_DATA;
    }

    /* Enough samples have been received, stop current measurement. */
    M_CHECK_SUCCESS(as7058_ifce_stop_measurement());

    as7058_modulator_t modulator;
    as7058_modulator_sub_sample_t sub_sample;
    M_CHECK_SUCCESS(get_modulator_and_sub_sample_from_sub_sample_id(g_sub_sample_id, &modulator, &sub_sample));

    uint32_t current_measurement_avg = g_current_sample_accu / g_current_sample_cnt;
    if (AS7058_PD_OFFSET_CALIBRATION_POINT_TYPE_ZERO == g_current_calibration_point) {
        /* Save averaged result and use it after the AS7058_PD_OFFSET_CALIBRATION_POINT_TYPE_STEP measurement has been
         * performed for the current photodiode offset current. */
        g_calibration_point_zero_result = current_measurement_avg;

        /* Increase photodiode offset current of the primary DAC by one SAR step and start
         * AS7058_PD_OFFSET_CALIBRATION_POINT_TYPE_STEP measurement. */
        g_current_calibration_point = AS7058_PD_OFFSET_CALIBRATION_POINT_TYPE_STEP;
        g_current_pd_offset_sar_step++;
        g_current_sample_cnt = 0;
        g_current_sample_accu = 0;
        M_CHECK_SUCCESS(set_pd_offset_primary_dac(modulator, sub_sample,
                                                  g_programmable_pd_offset +
                                                      g_current_pd_offset_sar_step *
                                                          AS7058_PD_OFFSET_CALIBRATION_PD_OFFSET_SAR_STEP_SIZE));
        M_CHECK_SUCCESS(as7058_ifce_start_measurement());

        /* No final measurement results is yet available. */
        return ERR_NO_DATA;
    } else { /* AS7058_PD_OFFSET_CALIBRATION_POINT_TYPE_STEP */
        uint32_t last_calibration_table_value;
        /* For calculating the index, subtract 1 from g_current_pd_offset_sar_step since no calibration is performed for
         * g_current_pd_offset_sar_step = 0. */
        uint8_t current_calibration_table_index = g_current_pd_offset_sar_step - 1;
        if (current_calibration_table_index > 0) {
            last_calibration_table_value = g_result.compensation_table[current_calibration_table_index - 1];
        } else {
            /* First entry in calibration table, no previous entry available. */
            last_calibration_table_value = 0;
        }
        /* Calculate difference of the previous AS7058_PD_OFFSET_CALIBRATION_POINT_TYPE_STEP measurement result and the
         * current AS7058_PD_OFFSET_CALIBRATION_POINT_TYPE_ZERO measurement result. Prevent integer overflow during
         * subtraction. */
        uint32_t calibration_point_result_delta =
            g_calibration_point_zero_result - M_MIN(current_measurement_avg, g_calibration_point_zero_result);
        /* Add last entry of the calibration table to the difference, store resulting value in calibration table. */
        g_result.compensation_table[current_calibration_table_index] =
            last_calibration_table_value + calibration_point_result_delta;

        if (g_current_pd_offset_sar_step < AS7058_PD_OFFSET_CALIBRATION_COMPENSATION_TABLE_ELEMENTS_NUM) {
            /* Another photodiode offset current step needs to be performed. First, perform a
             * AS7058_PD_OFFSET_CALIBRATION_POINT_TYPE_ZERO measurement where the photodiode offset current of the
             * secondary DAC is increased by one SAR step, so that both DACs are set to the same current value. */
            g_current_calibration_point = AS7058_PD_OFFSET_CALIBRATION_POINT_TYPE_ZERO;
            g_current_sample_cnt = 0;
            g_current_sample_accu = 0;
            M_CHECK_SUCCESS(set_pd_offset_secondary_dac(modulator, sub_sample,
                                                        g_programmable_pd_offset +
                                                            g_current_pd_offset_sar_step *
                                                                AS7058_PD_OFFSET_CALIBRATION_PD_OFFSET_SAR_STEP_SIZE));
            M_CHECK_SUCCESS(as7058_ifce_start_measurement());

            /* No final measurement results is yet available. */
            return ERR_NO_DATA;
        } else {
            /* All measurements have been performed, provide final measurement results to caller. Setting
             * g_current_pd_offset_sar_step to a value greater than
             * AS7058_PD_OFFSET_CALIBRATION_COMPENSATION_TABLE_ELEMENTS_NUM marks that all measurements have been
             * performed. */
            g_current_pd_offset_sar_step = AS7058_PD_OFFSET_CALIBRATION_COMPENSATION_TABLE_ELEMENTS_NUM + 1;
            *pp_result = &g_result;
            return ERR_SUCCESS;
        }
    }
}

err_code_t as7058_pd_offset_calibration_shutdown(void)
{
    g_state = AS7058_PD_OFFSET_CALIBRATION_STATE_UNINITIALIZED;

    return ERR_SUCCESS;
}
