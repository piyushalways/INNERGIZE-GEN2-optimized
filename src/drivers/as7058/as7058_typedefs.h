/******************************************************************************
 * Copyright © 2022 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

#ifndef __AS7058_TYPEDEFS_H__
#define __AS7058_TYPEDEFS_H__

/*!
 * \file      as7058_typedefs.h
 * \authors   ARIT
 * \copyright ams OSRAM
 * \addtogroup definition_group ChipLib Definitions
 *
 * \brief Description of the used data types.
 *
 * These are the type definitions used by AS7058 chip library.
 *
 *  @{
 */

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include "agc_typedefs.h"
#include "error_codes.h"
#include "std_inc.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

#define AS7058_SILICON_ID 0x92 /*!< Silicon ID of AS7058. */
#define AS7058_MAX_GROUP_SIZE                                                                                          \
    sizeof(as7058_reg_group_iir_t) /*!< Maximum combined size of the register values of a single register group. */
#define AS7058_FIFO_SAMPLE_SIZE 3  /*!< Size of one sample inside the FIFO. */

#ifndef AS7058_FIFO_DATA_BUFFER_SIZE
#define AS7058_FIFO_DATA_BUFFER_SIZE 1536 /*!< Size of the buffer which holds the FIFO data. */
#endif

/*! Maximum value of a sample acquired by AS7058. */
#define AS7058_SAMPLE_MAX_VALUE 0xFFFFF

/*! Number of elements in a PD offset calibration compensation table. During PD offset calibration, the SAR-controlled
 *  photodiode offset current bits (upper four bits) are manipulated. The remaining bits are left unmodified. A table
 *  element is generated for each value of the SAR-controlled bits, except for when the SAR-controlled bits are zero. */
#define AS7058_PD_OFFSET_CALIBRATION_COMPENSATION_TABLE_ELEMENTS_NUM 15

/*! Calculate the sub-sample flag from the ID. */
#define M_AS7058_SUB_SAMPLE_ID_TO_FLAG(sub_sample_id) (as7058_sub_sample_flags_t)(1 << ((sub_sample_id)-1))

/*! Definition of the register group IDs. */
enum as7058_reg_group_ids {
    AS7058_REG_GROUP_ID_PWR = 0,   /*!< ID of the `power` register group. See ::as7058_reg_group_power_t for the
                                        contents of the group. */
    AS7058_REG_GROUP_ID_CTRL = 1,  /*!< ID of the `control` register group. See ::as7058_reg_group_control_t for the
                                        contents of the group. */
    AS7058_REG_GROUP_ID_LED = 2,   /*!< ID of the `led` register group. See ::as7058_reg_group_led_t for the contents of
                                        the group. */
    AS7058_REG_GROUP_ID_PD = 3,    /*!< ID of the `pd` register group. See ::as7058_reg_group_pd_t for the contents of
                                        the group. */
    AS7058_REG_GROUP_ID_IOS = 4,   /*!< ID of the `ios` register group. See ::as7058_reg_group_ios_t for the contents of
                                        the group. */
    AS7058_REG_GROUP_ID_PPG = 5,   /*!< ID of the `ppg` register group. See ::as7058_reg_group_ppg_t for the contents of
                                        the group. */
    AS7058_REG_GROUP_ID_ECG = 6,   /*!< ID of the `ecg` register group. See ::as7058_reg_group_ecg_t for the contents of
                                        the group. */
    AS7058_REG_GROUP_ID_SINC = 7,  /*!< ID of the `sinc` register group. See ::as7058_reg_group_sinc_t for the contents
                                        of the group. */
    AS7058_REG_GROUP_ID_IIR = 8,   /*!< ID of the `iir` register group. See ::as7058_reg_group_iir_t for the contents of
                                        the group. */
    AS7058_REG_GROUP_ID_SEQ = 9,   /*!< ID of the `seq` register group. See ::as7058_reg_group_seq_t for the contents of
                                        the group. */
    AS7058_REG_GROUP_ID_PP = 10,   /*!< ID of the `post` register group. See ::as7058_reg_group_pp_t for the contents of
                                        the group. */
    AS7058_REG_GROUP_ID_FIFO = 11, /*!< ID of the `fifo` register group. See ::as7058_reg_group_fifo_t for the contents
                                        of the group. */

    AS7058_REG_GROUP_ID_NUM = 12, /*!< Number of supported register groups. */
};

/*! Type of ::as7058_reg_group_ids. */
typedef uint8_t as7058_reg_group_ids_t;

/*! Sub-sample flags. */
enum as7058_sub_sample_flags {
    AS7058_SUB_SAMPLE_FLAG_NONE = 0x00000000, /*!< No sub-sample is selected. */

    AS7058_SUB_SAMPLE_FLAG_PPG1_SUB1 = 0x00000001, /*!< Flag for sub-sample 1 of PPG modulator 1. */
    AS7058_SUB_SAMPLE_FLAG_PPG1_SUB2 = 0x00000002, /*!< Flag for sub-sample 2 of PPG modulator 1. */
    AS7058_SUB_SAMPLE_FLAG_PPG1_SUB3 = 0x00000004, /*!< Flag for sub-sample 3 of PPG modulator 1. */
    AS7058_SUB_SAMPLE_FLAG_PPG1_SUB4 = 0x00000008, /*!< Flag for sub-sample 4 of PPG modulator 1. */
    AS7058_SUB_SAMPLE_FLAG_PPG1_SUB5 = 0x00000010, /*!< Flag for sub-sample 5 of PPG modulator 1. */
    AS7058_SUB_SAMPLE_FLAG_PPG1_SUB6 = 0x00000020, /*!< Flag for sub-sample 6 of PPG modulator 1. */
    AS7058_SUB_SAMPLE_FLAG_PPG1_SUB7 = 0x00000040, /*!< Flag for sub-sample 7 of PPG modulator 1. */
    AS7058_SUB_SAMPLE_FLAG_PPG1_SUB8 = 0x00000080, /*!< Flag for sub-sample 8 of PPG modulator 1. */

    AS7058_SUB_SAMPLE_FLAG_PPG2_SUB1 = 0x00000100, /*!< Flag for sub-sample 1 of PPG modulator 2. */
    AS7058_SUB_SAMPLE_FLAG_PPG2_SUB2 = 0x00000200, /*!< Flag for sub-sample 2 of PPG modulator 2. */
    AS7058_SUB_SAMPLE_FLAG_PPG2_SUB3 = 0x00000400, /*!< Flag for sub-sample 3 of PPG modulator 2. */
    AS7058_SUB_SAMPLE_FLAG_PPG2_SUB4 = 0x00000800, /*!< Flag for sub-sample 4 of PPG modulator 2. */
    AS7058_SUB_SAMPLE_FLAG_PPG2_SUB5 = 0x00001000, /*!< Flag for sub-sample 5 of PPG modulator 2. */
    AS7058_SUB_SAMPLE_FLAG_PPG2_SUB6 = 0x00002000, /*!< Flag for sub-sample 6 of PPG modulator 2. */
    AS7058_SUB_SAMPLE_FLAG_PPG2_SUB7 = 0x00004000, /*!< Flag for sub-sample 7 of PPG modulator 2. */
    AS7058_SUB_SAMPLE_FLAG_PPG2_SUB8 = 0x00008000, /*!< Flag for sub-sample 8 of PPG modulator 2. */

    AS7058_SUB_SAMPLE_FLAG_ECG_SEQ1_SUB1 = 0x00010000, /*!< Flag for sub-sample 1 of sequence 1 of the ECG modulator. */
    AS7058_SUB_SAMPLE_FLAG_ECG_SEQ1_SUB2 = 0x00020000, /*!< Flag for sub-sample 2 of sequence 1 of the ECG modulator. */

    AS7058_SUB_SAMPLE_FLAG_ECG_SEQ2_SUB1 = 0x00040000, /*!< Flag for sub-sample 1 of sequence 2 of the ECG modulator. */
};

/*! Type of ::as7058_sub_sample_flags. */
typedef uint32_t as7058_sub_sample_flags_t;

/*! Sub-sample ID. */
enum as7058_sub_sample_ids {
    AS7058_SUB_SAMPLE_ID_DISABLED = 0, /*!< Sub-sample is disabled. */

    AS7058_SUB_SAMPLE_ID_PPG1_SUB1 = 1, /*!< Sub-sample ID of sub-sample 1 of PPG modulator 1. */
    AS7058_SUB_SAMPLE_ID_PPG1_SUB2 = 2, /*!< Sub-sample ID of sub-sample 2 of PPG modulator 1. */
    AS7058_SUB_SAMPLE_ID_PPG1_SUB3 = 3, /*!< Sub-sample ID of sub-sample 3 of PPG modulator 1. */
    AS7058_SUB_SAMPLE_ID_PPG1_SUB4 = 4, /*!< Sub-sample ID of sub-sample 4 of PPG modulator 1. */
    AS7058_SUB_SAMPLE_ID_PPG1_SUB5 = 5, /*!< Sub-sample ID of sub-sample 5 of PPG modulator 1. */
    AS7058_SUB_SAMPLE_ID_PPG1_SUB6 = 6, /*!< Sub-sample ID of sub-sample 6 of PPG modulator 1. */
    AS7058_SUB_SAMPLE_ID_PPG1_SUB7 = 7, /*!< Sub-sample ID of sub-sample 7 of PPG modulator 1. */
    AS7058_SUB_SAMPLE_ID_PPG1_SUB8 = 8, /*!< Sub-sample ID of sub-sample 8 of PPG modulator 1. */

    AS7058_SUB_SAMPLE_ID_PPG2_SUB1 = 9,  /*!< Sub-sample ID of sub-sample 1 of PPG modulator 2. */
    AS7058_SUB_SAMPLE_ID_PPG2_SUB2 = 10, /*!< Sub-sample ID of sub-sample 2 of PPG modulator 2. */
    AS7058_SUB_SAMPLE_ID_PPG2_SUB3 = 11, /*!< Sub-sample ID of sub-sample 3 of PPG modulator 2. */
    AS7058_SUB_SAMPLE_ID_PPG2_SUB4 = 12, /*!< Sub-sample ID of sub-sample 4 of PPG modulator 2. */
    AS7058_SUB_SAMPLE_ID_PPG2_SUB5 = 13, /*!< Sub-sample ID of sub-sample 5 of PPG modulator 2. */
    AS7058_SUB_SAMPLE_ID_PPG2_SUB6 = 14, /*!< Sub-sample ID of sub-sample 6 of PPG modulator 2. */
    AS7058_SUB_SAMPLE_ID_PPG2_SUB7 = 15, /*!< Sub-sample ID of sub-sample 7 of PPG modulator 2. */
    AS7058_SUB_SAMPLE_ID_PPG2_SUB8 = 16, /*!< Sub-sample ID of sub-sample 8 of PPG modulator 2. */

    AS7058_SUB_SAMPLE_ID_ECG_SEQ1_SUB1 = 17, /*!< Sub-sample ID of sub-sample 1 of sequence 1 of the ECG modulator. */
    AS7058_SUB_SAMPLE_ID_ECG_SEQ1_SUB2 = 18, /*!< Sub-sample ID of sub-sample 2 of sequence 1 of the ECG modulator. */

    AS7058_SUB_SAMPLE_ID_ECG_SEQ2_SUB1 = 19, /*!< Sub-sample ID of sub-sample 1 of sequence 2 of the ECG modulator. */

    AS7058_SUB_SAMPLE_ID_NUM =
        20, /*!< Number of supported sub-sample IDs. The last valid ID is ::AS7058_SUB_SAMPLE_ID_ECG_SEQ2_SUB1. */
};

/*! Type of ::as7058_sub_sample_ids. */
typedef uint8_t as7058_sub_sample_ids_t;

/*! Identifies the modulators of the AS7058 AFE. Note that if a modulator supports multiple sequences, this enumeration
 *  contains separate enumeration constants for each sequence. */
enum as7058_modulator {
    AS7058_MODULATOR_PPG1 = 0,     /*!< PPG modulator 1. */
    AS7058_MODULATOR_PPG2 = 1,     /*!< PPG modulator 2. */
    AS7058_MODULATOR_ECG_SEQ1 = 2, /*!< ECG modulator, sequence 1. */
    AS7058_MODULATOR_ECG_SEQ2 = 3, /*!< ECG modulator, sequence 2. */

    AS7058_MODULATOR_NUM_PPG = 2, /*!< Number of PPG modulators. */
    AS7058_MODULATOR_NUM = 4,     /*!< Total number of modulators. */
};

/*! Type for ::as7058_modulator. */
typedef uint8_t as7058_modulator_t;

/*! Identifies the sub-samples of an ::as7058_modulator. Note that not all modulators support the same number of
 *  sub-samples. */
enum as7058_sub_sample {
    AS7058_MODULATOR_SUB_SAMPLE_1 = 0, /*!< Sub-sample 1. */
    AS7058_MODULATOR_SUB_SAMPLE_2 = 1, /*!< Sub-sample 2. */
    AS7058_MODULATOR_SUB_SAMPLE_3 = 2, /*!< Sub-sample 3. */
    AS7058_MODULATOR_SUB_SAMPLE_4 = 3, /*!< Sub-sample 4. */
    AS7058_MODULATOR_SUB_SAMPLE_5 = 4, /*!< Sub-sample 5. */
    AS7058_MODULATOR_SUB_SAMPLE_6 = 5, /*!< Sub-sample 6. */
    AS7058_MODULATOR_SUB_SAMPLE_7 = 6, /*!< Sub-sample 7. */
    AS7058_MODULATOR_SUB_SAMPLE_8 = 7, /*!< Sub-sample 8. */

    AS7058_MODULATOR_SUB_SAMPLE_NUM_PPG = 8, /*!< Number of sub-samples supported by PPG modulators
                                                  (::AS7058_MODULATOR_PPG1 and ::AS7058_MODULATOR_PPG2). */

    AS7058_MODULATOR_SUB_SAMPLE_INVALID = 0xFF, /*!< Represents an invalid value. */
};

/*! Type for ::as7058_sub_sample. */
typedef uint8_t as7058_modulator_sub_sample_t;

/*! First three bits of the FIFO data, which describes the type of the sample. */
enum as7058_fifo_data_marker {
    AS7058_FIFO_DATA_MARKER_PPG1_FIRST = 0,    /*!< Defines first sub-sample of modulator 1. */
    AS7058_FIFO_DATA_MARKER_PPG1_OTHER = 1,    /*!< Other sub-samples of modulator 1. */
    AS7058_FIFO_DATA_MARKER_PPG2_FIRST = 2,    /*!< Defines first sub-sample of modulator 2. */
    AS7058_FIFO_DATA_MARKER_PPG2_OTHER = 3,    /*!< Other sub-samples of modulator 2. */
    AS7058_FIFO_DATA_MARKER_ECG_SEQ1_SUB1 = 4, /*!< Sub-sample 1 of modulator 3 and sequence 1. */
    AS7058_FIFO_DATA_MARKER_ECG_SEQ1_SUB2 = 5, /*!< Sub-sample 2 of modulator 3 and sequence 1. */
    AS7058_FIFO_DATA_MARKER_ECG_SEQ2_SUB1 = 6, /*!< Sub-sample 1 of modulator 3 and sequence 2. */
    AS7058_FIFO_DATA_MARKER_STATUS = 7,        /*!< Status marker of SAR information. */
};

/*! Type of ::as7058_fifo_data_marker. */
typedef uint8_t as7058_fifo_data_marker_t;

/*! Measurement modes. */
enum as7058_meas_mode {
    AS7058_MEAS_MODE_NORMAL = 0,                        /*!< Default measurement mode for regular FIFO data acquisition.
                                                         */
    AS7058_MEAS_MODE_SPECIAL_BIOZ = 1,                  /*!< Special measurement mode for BioZ. */
    AS7058_MEAS_MODE_SPECIAL_SCALING_EDA = 2,           /*!< Special measurement mode to obtain impedance
                                                             reference values for EDA. */
    AS7058_MEAS_MODE_SPECIAL_PD_OFFSET_CALIBRATION = 3, /*!< Special measurement mode to perform PD offset
                                                             calibration. */

    AS7058_MEAS_MODE_NUM = 4, /*!< Number of supported measurement modes. */
};

/*! Type of ::as7058_meas_mode. */
typedef uint8_t as7058_meas_mode_t;

/*! Register definition of AS7058. */
enum as7058_reg_addresses {
    AS7058_REGADDR_OTP_BIOZ_REF_L = 0x0E,   /*!< Address of register OTP14. */
    AS7058_REGADDR_OTP_BIOZ_REF_H = 0x0F,   /*!< Address of register OTP15. */
    AS7058_REGADDR_OTP_GSR_REF_L = 0x13,    /*!< Address of register OTP19. */
    AS7058_REGADDR_OTP_GSR_REF_H = 0x14,    /*!< Address of register OTP20. */
    AS7058_REGADDR_OTP_TEMP_REF_L = 0x15,   /*!< Address of register OTP21. */
    AS7058_REGADDR_OTP_TEMP_REF_H = 0x16,   /*!< Address of register OTP22. */
    AS7058_REGADDR_CLK_CFG = 0x18,          /*!< Address of register CLK_CFG. */
    AS7058_REGADDR_REF_CFG1 = 0x19,         /*!< Address of register REF_CFG1. */
    AS7058_REGADDR_REF_CFG2 = 0x1A,         /*!< Address of register REF_CFG2. */
    AS7058_REGADDR_REF_CFG3 = 0x1B,         /*!< Address of register REF_CFG3. */
    AS7058_REGADDR_STANDBY_ON1 = 0x1C,      /*!< Address of register STANDBY_ON1. */
    AS7058_REGADDR_STANDBY_ON2 = 0x1D,      /*!< Address of register STANDBY_ON2. */
    AS7058_REGADDR_STANDBY_EN1 = 0x1E,      /*!< Address of register STANDBY_EN1. */
    AS7058_REGADDR_STANDBY_EN2 = 0x1F,      /*!< Address of register STANDBY_EN2. */
    AS7058_REGADDR_STANDBY_EN3 = 0x20,      /*!< Address of register STANDBY_EN3. */
    AS7058_REGADDR_STANDBY_EN4 = 0x21,      /*!< Address of register STANDBY_EN4. */
    AS7058_REGADDR_STANDBY_EN5 = 0x22,      /*!< Address of register STANDBY_EN5. */
    AS7058_REGADDR_STANDBY_EN6 = 0x23,      /*!< Address of register STANDBY_EN6. */
    AS7058_REGADDR_STANDBY_EN7 = 0x24,      /*!< Address of register STANDBY_EN7. */
    AS7058_REGADDR_STANDBY_EN8 = 0x25,      /*!< Address of register STANDBY_EN8. */
    AS7058_REGADDR_STANDBY_EN9 = 0x26,      /*!< Address of register STANDBY_EN9. */
    AS7058_REGADDR_STANDBY_EN10 = 0x27,     /*!< Address of register STANDBY_EN10. */
    AS7058_REGADDR_STANDBY_EN11 = 0x28,     /*!< Address of register STANDBY_EN11. */
    AS7058_REGADDR_STANDBY_EN12 = 0x29,     /*!< Address of register STANDBY_EN12. */
    AS7058_REGADDR_STANDBY_EN13 = 0x2A,     /*!< Address of register STANDBY_EN13. */
    AS7058_REGADDR_STANDBY_EN14 = 0x2B,     /*!< Address of register STANDBY_EN14. */
    AS7058_REGADDR_PWR_ON = 0x2D,           /*!< Address of register PWR_ON. */
    AS7058_REGADDR_PWR_ISO = 0x2E,          /*!< Address of register PWR_ISO. */
    AS7058_REGADDR_PWR_STAT = 0x2F,         /*!< Address of register PWR_STAT. */
    AS7058_REGADDR_I2C_MODE = 0x31,         /*!< Address of register I2C_MODE. */
    AS7058_REGADDR_INT_CFG = 0x32,          /*!< Address of register INT_CFG. */
    AS7058_REGADDR_IF_CFG = 0x33,           /*!< Address of register IF_CFG. */
    AS7058_REGADDR_GPIO_CFG1 = 0x34,        /*!< Address of register GPIO_CFG1. */
    AS7058_REGADDR_GPIO_CFG2 = 0x35,        /*!< Address of register GPIO_CFG2. */
    AS7058_REGADDR_IO_CFG = 0x36,           /*!< Address of register IO_CFG. */
    AS7058_REGADDR_PPGMOD_CFG1 = 0x37,      /*!< Address of register PPGMOD_CFG1. */
    AS7058_REGADDR_PPGMOD_CFG2 = 0x38,      /*!< Address of register PPGMOD_CFG2. */
    AS7058_REGADDR_PPGMOD_CFG3 = 0x39,      /*!< Address of register PPGMOD_CFG3. */
    AS7058_REGADDR_PPGMOD1_CFG1 = 0x3A,     /*!< Address of register PPGMOD1_CFG1. */
    AS7058_REGADDR_PPGMOD1_CFG2 = 0x3B,     /*!< Address of register PPGMOD1_CFG2. */
    AS7058_REGADDR_PPGMOD1_CFG3 = 0x3C,     /*!< Address of register PPGMOD1_CFG3. */
    AS7058_REGADDR_PPGMOD2_CFG1 = 0x3D,     /*!< Address of register PPGMOD2_CFG1. */
    AS7058_REGADDR_PPGMOD2_CFG2 = 0x3E,     /*!< Address of register PPGMOD2_CFG2. */
    AS7058_REGADDR_PPGMOD2_CFG3 = 0x3F,     /*!< Address of register PPGMOD2_CFG3. */
    AS7058_REGADDR_VCSEL_PASSWORD = 0x40,   /*!< Address of register VCSEL_PASSWORD. */
    AS7058_REGADDR_VCSEL_CFG = 0x41,        /*!< Address of register VCSEL_CFG. */
    AS7058_REGADDR_VCSEL_MODE = 0x42,       /*!< Address of register VCSEL_MODE. */
    AS7058_REGADDR_LED_CFG = 0x43,          /*!< Address of register LED_CFG. */
    AS7058_REGADDR_LED_DRV1 = 0x44,         /*!< Address of register LED_DRV1. */
    AS7058_REGADDR_LED_DRV2 = 0x45,         /*!< Address of register LED_DRV2. */
    AS7058_REGADDR_LED1_ICTRL = 0x46,       /*!< Address of register LED1_ICTRL. */
    AS7058_REGADDR_LED2_ICTRL = 0x47,       /*!< Address of register LED2_ICTRL. */
    AS7058_REGADDR_LED3_ICTRL = 0x48,       /*!< Address of register LED3_ICTRL. */
    AS7058_REGADDR_LED4_ICTRL = 0x49,       /*!< Address of register LED4_ICTRL. */
    AS7058_REGADDR_LED5_ICTRL = 0x4A,       /*!< Address of register LED5_ICTRL. */
    AS7058_REGADDR_LED6_ICTRL = 0x4B,       /*!< Address of register LED6_ICTRL. */
    AS7058_REGADDR_LED7_ICTRL = 0x4C,       /*!< Address of register LED7_ICTRL. */
    AS7058_REGADDR_LED8_ICTRL = 0x4D,       /*!< Address of register LED8_ICTRL. */
    AS7058_REGADDR_LED_IRNG1 = 0x4E,        /*!< Address of register LED_IRNG1. */
    AS7058_REGADDR_LED_IRNG2 = 0x4F,        /*!< Address of register LED_IRNG2. */
    AS7058_REGADDR_LED_SUB1 = 0x50,         /*!< Address of register LED_SUB1. */
    AS7058_REGADDR_LED_SUB2 = 0x51,         /*!< Address of register LED_SUB2. */
    AS7058_REGADDR_LED_SUB3 = 0x52,         /*!< Address of register LED_SUB3. */
    AS7058_REGADDR_LED_SUB4 = 0x53,         /*!< Address of register LED_SUB4. */
    AS7058_REGADDR_LED_SUB5 = 0x54,         /*!< Address of register LED_SUB5. */
    AS7058_REGADDR_LED_SUB6 = 0x55,         /*!< Address of register LED_SUB6. */
    AS7058_REGADDR_LED_SUB7 = 0x56,         /*!< Address of register LED_SUB7. */
    AS7058_REGADDR_LED_SUB8 = 0x57,         /*!< Address of register LED_SUB8. */
    AS7058_REGADDR_LOWVDS_WAIT = 0x58,      /*!< Address of register LOWVDS_WAIT. */
    AS7058_REGADDR_PDSEL_CFG = 0x59,        /*!< Address of register PDSEL_CFG. */
    AS7058_REGADDR_PPG1_PDSEL1 = 0x5A,      /*!< Address of register PPG1_PDSEL1. */
    AS7058_REGADDR_PPG1_PDSEL2 = 0x5B,      /*!< Address of register PPG1_PDSEL2. */
    AS7058_REGADDR_PPG1_PDSEL3 = 0x5C,      /*!< Address of register PPG1_PDSEL3. */
    AS7058_REGADDR_PPG1_PDSEL4 = 0x5D,      /*!< Address of register PPG1_PDSEL4. */
    AS7058_REGADDR_PPG1_PDSEL5 = 0x5E,      /*!< Address of register PPG1_PDSEL5. */
    AS7058_REGADDR_PPG1_PDSEL6 = 0x5F,      /*!< Address of register PPG1_PDSEL6. */
    AS7058_REGADDR_PPG1_PDSEL7 = 0x60,      /*!< Address of register PPG1_PDSEL7. */
    AS7058_REGADDR_PPG1_PDSEL8 = 0x61,      /*!< Address of register PPG1_PDSEL8. */
    AS7058_REGADDR_PPG2_PDSEL1 = 0x62,      /*!< Address of register PPG2_PDSEL1. */
    AS7058_REGADDR_PPG2_PDSEL2 = 0x63,      /*!< Address of register PPG2_PDSEL2. */
    AS7058_REGADDR_PPG2_PDSEL3 = 0x64,      /*!< Address of register PPG2_PDSEL3. */
    AS7058_REGADDR_PPG2_PDSEL4 = 0x65,      /*!< Address of register PPG2_PDSEL4. */
    AS7058_REGADDR_PPG2_PDSEL5 = 0x66,      /*!< Address of register PPG2_PDSEL2. */
    AS7058_REGADDR_PPG2_PDSEL6 = 0x67,      /*!< Address of register PPG2_PDSEL5. */
    AS7058_REGADDR_PPG2_PDSEL7 = 0x68,      /*!< Address of register PPG2_PDSEL6. */
    AS7058_REGADDR_PPG2_PDSEL8 = 0x69,      /*!< Address of register PPG2_PDSEL7. */
    AS7058_REGADDR_PPG2_AFESEL1 = 0x6A,     /*!< Address of register PPG2_AFESEL1. */
    AS7058_REGADDR_PPG2_AFESEL2 = 0x6B,     /*!< Address of register PPG2_AFESEL2. */
    AS7058_REGADDR_PPG2_AFESEL3 = 0x6C,     /*!< Address of register PPG2_AFESEL3. */
    AS7058_REGADDR_PPG2_AFESEL4 = 0x6D,     /*!< Address of register PPG2_AFESEL4. */
    AS7058_REGADDR_PPG2_AFEEN = 0x6E,       /*!< Address of register PPG2_AFEEN. */
    AS7058_REGADDR_PPG_SINC_CFGA = 0x6F,    /*!< Address of register PPG_SINC_CFGA. */
    AS7058_REGADDR_PPG_SINC_CFGB = 0x70,    /*!< Address of register PPG_SINC_CFGB. */
    AS7058_REGADDR_PPG_SINC_CFGC = 0x71,    /*!< Address of register PPG_SINC_CFGC. */
    AS7058_REGADDR_PPG_SINC_CFGD = 0x72,    /*!< Address of register PPG_SINC_CFGD. */
    AS7058_REGADDR_ECG1_SINC_CFGA = 0x73,   /*!< Address of register ECG1_SINC_CFGA. */
    AS7058_REGADDR_ECG1_SINC_CFGB = 0x74,   /*!< Address of register ECG1_SINC_CFGB. */
    AS7058_REGADDR_ECG1_SINC_CFGC = 0x75,   /*!< Address of register ECG1_SINC_CFGC. */
    AS7058_REGADDR_ECG2_SINC_CFGA = 0x76,   /*!< Address of register ECG2_SINC_CFGA. */
    AS7058_REGADDR_ECG2_SINC_CFGB = 0x77,   /*!< Address of register ECG2_SINC_CFGB. */
    AS7058_REGADDR_ECG2_SINC_CFGC = 0x78,   /*!< Address of register ECG2_SINC_CFGC. */
    AS7058_REGADDR_ECG_SINC_CFG = 0x79,     /*!< Address of register ECG_SINC_CFG. */
    AS7058_REGADDR_IOS_PPG1_SUB1 = 0x7A,    /*!< Address of register IOS_PPG1_SUB1. */
    AS7058_REGADDR_IOS_PPG1_SUB2 = 0x7B,    /*!< Address of register IOS_PPG1_SUB2. */
    AS7058_REGADDR_IOS_PPG1_SUB3 = 0x7C,    /*!< Address of register IOS_PPG1_SUB3. */
    AS7058_REGADDR_IOS_PPG1_SUB4 = 0x7D,    /*!< Address of register IOS_PPG1_SUB4. */
    AS7058_REGADDR_IOS_PPG1_SUB5 = 0x7E,    /*!< Address of register IOS_PPG1_SUB5. */
    AS7058_REGADDR_IOS_PPG1_SUB6 = 0x7F,    /*!< Address of register IOS_PPG1_SUB6. */
    AS7058_REGADDR_IOS_PPG1_SUB7 = 0x80,    /*!< Address of register IOS_PPG1_SUB7. */
    AS7058_REGADDR_IOS_PPG1_SUB8 = 0x81,    /*!< Address of register IOS_PPG1_SUB8. */
    AS7058_REGADDR_IOS_PPG2_SUB1 = 0x82,    /*!< Address of register IOS_PPG2_SUB1. */
    AS7058_REGADDR_IOS_PPG2_SUB2 = 0x83,    /*!< Address of register IOS_PPG2_SUB2. */
    AS7058_REGADDR_IOS_PPG2_SUB3 = 0x84,    /*!< Address of register IOS_PPG2_SUB3. */
    AS7058_REGADDR_IOS_PPG2_SUB4 = 0x85,    /*!< Address of register IOS_PPG2_SUB4. */
    AS7058_REGADDR_IOS_PPG2_SUB5 = 0x86,    /*!< Address of register IOS_PPG2_SUB5. */
    AS7058_REGADDR_IOS_PPG2_SUB6 = 0x87,    /*!< Address of register IOS_PPG2_SUB6. */
    AS7058_REGADDR_IOS_PPG2_SUB7 = 0x88,    /*!< Address of register IOS_PPG2_SUB7. */
    AS7058_REGADDR_IOS_PPG2_SUB8 = 0x89,    /*!< Address of register IOS_PPG2_SUB8. */
    AS7058_REGADDR_IOS_LEDOFF = 0x8A,       /*!< Address of register IOS_LEDOFF. */
    AS7058_REGADDR_IOS_CFG = 0x8B,          /*!< Address of register IOS_CFG. */
    AS7058_REGADDR_AOC_SAR_THRES = 0x8C,    /*!< Address of register AOC_SAR_THRES. */
    AS7058_REGADDR_AOC_SAR_RANGE = 0x8D,    /*!< Address of register AOC_SAR_RANGE. */
    AS7058_REGADDR_AOC_SAR_PPG1 = 0x8E,     /*!< Address of register AOC_SAR_PPG1. */
    AS7058_REGADDR_AOC_SAR_PPG2 = 0x8F,     /*!< Address of register AOC_SAR_PPG2. */
    AS7058_REGADDR_PP_CFG = 0x90,           /*!< Address of register PP_CFG. */
    AS7058_REGADDR_PPG1_PP1 = 0x91,         /*!< Address of register PPG1_PP1. */
    AS7058_REGADDR_PPG1_PP2 = 0x92,         /*!< Address of register PPG1_PP2. */
    AS7058_REGADDR_PPG2_PP1 = 0x93,         /*!< Address of register PPG2_PP1. */
    AS7058_REGADDR_PPG2_PP2 = 0x94,         /*!< Address of register PPG2_PP2. */
    AS7058_REGADDR_IRQ_ENABLE = 0x95,       /*!< Address of register IRQ_ENABLE. */
    AS7058_REGADDR_PPG_SUB_WAIT = 0x96,     /*!< Address of register PPG_SUB_WAIT. */
    AS7058_REGADDR_PPG_SAR_WAIT = 0x97,     /*!< Address of register AOC_SAR_PPG2. */
    AS7058_REGADDR_PPG_LED_INIT = 0x98,     /*!< Address of register PPG_LED_INIT. */
    AS7058_REGADDR_PPG_FREQL = 0x99,        /*!< Address of register PPG_FREQL. */
    AS7058_REGADDR_PPG_FREQH = 0x9A,        /*!< Address of register PPG_FREQH. */
    AS7058_REGADDR_PPG1_SUB_EN = 0x9B,      /*!< Address of register PPG1_SUB_EN. */
    AS7058_REGADDR_PPG2_SUB_EN = 0x9C,      /*!< Address of register PPG2_SUB_EN. */
    AS7058_REGADDR_PPG_MODE1 = 0x9D,        /*!< Address of register PPG_MODE1. */
    AS7058_REGADDR_PPG_MODE2 = 0x9E,        /*!< Address of register PPG_MODE2. */
    AS7058_REGADDR_PPG_MODE3 = 0x9F,        /*!< Address of register PPG_MODE3. */
    AS7058_REGADDR_PPG_MODE4 = 0xA0,        /*!< Address of register PPG_MODE4. */
    AS7058_REGADDR_PPG_MODE5 = 0xA1,        /*!< Address of register PPG_MODE5. */
    AS7058_REGADDR_PPG_MODE6 = 0xA2,        /*!< Address of register PPG_MODE6. */
    AS7058_REGADDR_PPG_MODE7 = 0xA3,        /*!< Address of register PPG_MODE7. */
    AS7058_REGADDR_PPG_MODE8 = 0xA4,        /*!< Address of register PPG_MODE8. */
    AS7058_REGADDR_PPG_CFG = 0xA5,          /*!< Address of register PPG_CFG. */
    AS7058_REGADDR_ECG_FREQL = 0xA6,        /*!< Address of register ECG_FREQL. */
    AS7058_REGADDR_ECG_FREQH = 0xA7,        /*!< Address of register ECG_FREQH. */
    AS7058_REGADDR_ECG1_FREQDIVL = 0xA8,    /*!< Address of register ECG1_FREQDIVL. */
    AS7058_REGADDR_ECG1_FREQDIVH = 0xA9,    /*!< Address of register ECG1_FREQDIVH. */
    AS7058_REGADDR_ECG2_FREQDIVL = 0xAA,    /*!< Address of register ECG2_FREQDIVL. */
    AS7058_REGADDR_ECG2_FREQDIVH = 0xAB,    /*!< Address of register ECG2_FREQDIVH. */
    AS7058_REGADDR_ECG_SUBS = 0xAC,         /*!< Address of register ECG_SUBS. */
    AS7058_REGADDR_LEADOFF_INITL = 0xAD,    /*!< Address of register LEADOFF_INITL. */
    AS7058_REGADDR_LEADOFF_INITH = 0xAE,    /*!< Address of register LEADOFF_INITH. */
    AS7058_REGADDR_ECG_INITL = 0xAF,        /*!< Address of register ECG_INITL. */
    AS7058_REGADDR_ECG_INITH = 0xB0,        /*!< Address of register ECG_INITH. */
    AS7058_REGADDR_SAMPLE_NUM = 0xB1,       /*!< Address of register SAMPLE_NUM. */
    AS7058_REGADDR_BIOZ_CFG = 0xB2,         /*!< Address of register BIOZ_CFG. */
    AS7058_REGADDR_BIOZ_EXCIT = 0xB3,       /*!< Address of register BIOZ_EXCIT. */
    AS7058_REGADDR_BIOZ_MIXER = 0xB4,       /*!< Address of register BIOZ_MIXER. */
    AS7058_REGADDR_BIOZ_SELECT = 0xB5,      /*!< Address of register BIOZ_SELECT. */
    AS7058_REGADDR_BIOZ_GAIN = 0xB6,        /*!< Address of register BIOZ_GAIN. */
    AS7058_REGADDR_ECGMOD_CFG1 = 0xB7,      /*!< Address of register ECGMOD_CFG1. */
    AS7058_REGADDR_ECGMOD_CFG2 = 0xB8,      /*!< Address of register ECGMOD_CFG2. */
    AS7058_REGADDR_ECGIMUX_CFG1 = 0xB9,     /*!< Address of register ECGIMUX_CFG1. */
    AS7058_REGADDR_ECGIMUX_CFG2 = 0xBA,     /*!< Address of register ECGIMUX_CFG2. */
    AS7058_REGADDR_ECGIMUX_CFG3 = 0xBB,     /*!< Address of register ECGIMUX_CFG3. */
    AS7058_REGADDR_ECGAMP_CFG1 = 0xBC,      /*!< Address of register ECGAMP_CFG1. */
    AS7058_REGADDR_ECGAMP_CFG2 = 0xBD,      /*!< Address of register ECGAMP_CFG2. */
    AS7058_REGADDR_ECGAMP_CFG3 = 0xBE,      /*!< Address of register ECGAMP_CFG3. */
    AS7058_REGADDR_ECGAMP_CFG4 = 0xBF,      /*!< Address of register ECGAMP_CFG4. */
    AS7058_REGADDR_ECGAMP_CFG5 = 0xC0,      /*!< Address of register ECGAMP_CFG5. */
    AS7058_REGADDR_ECGAMP_CFG6 = 0xC1,      /*!< Address of register ECGAMP_CFG6. */
    AS7058_REGADDR_ECGAMP_CFG7 = 0xC2,      /*!< Address of register ECGAMP_CFG7. */
    AS7058_REGADDR_ECG_BIOZ = 0xC3,         /*!< Address of register ECG_BIOZ. */
    AS7058_REGADDR_LEADOFF_CFG = 0xC4,      /*!< Address of register LEADOFF_CFG. */
    AS7058_REGADDR_LEADOFF_THRESL = 0xC5,   /*!< Address of register LEADOFF_THRESL. */
    AS7058_REGADDR_LEADOFF_THRESH = 0xC6,   /*!< Address of register LEADOFF_THRESH. */
    AS7058_REGADDR_IIR_CFG = 0xC7,          /*!< Address of register IIR_CFG. */
    AS7058_REGADDR_IIR_COEFF_ADDR = 0xC8,   /*!< Address of register IIR_COEFF_ADDR. */
    AS7058_REGADDR_IIR_COEFF_DATA = 0xC9,   /*!< Address of register IIR_COEFF_DATA. */
    AS7058_REGADDR_FIFO_THRESHOLD = 0xCA,   /*!< Address of register FIFO_THRESHOLD. */
    AS7058_REGADDR_FIFO_CTRL = 0xCB,        /*!< Address of register FIFO_CTRL. */
    AS7058_REGADDR_PRODUCT_ID = 0xEB,       /*!< Address of register PRODUCT_ID. */
    AS7058_REGADDR_SILICON_ID = 0xEC,       /*!< Address of register SILICON_ID. */
    AS7058_REGADDR_REVISION = 0xED,         /*!< Address of register REVISION. */
    AS7058_REGADDR_GPIO_CTRL = 0xEE,        /*!< Address of register GPIO_CTRL. */
    AS7058_REGADDR_CHIP_CTRL = 0xEF,        /*!< Address of register CHIP_CTRL. */
    AS7058_REGADDR_SEQ_START = 0xF0,        /*!< Address of register SEQ_START. */
    AS7058_REGADDR_STATUS_CGB = 0xF1,       /*!< Address of register STATUS_CGBA. */
    AS7058_REGADDR_STATUS_SEQ = 0xF2,       /*!< Address of register STATUS_SEQ. */
    AS7058_REGADDR_STATUS_LED = 0xF3,       /*!< Address of register STATUS_LED. */
    AS7058_REGADDR_STATUS_ASATA = 0xF4,     /*!< Address of register STATUS_ASATA. */
    AS7058_REGADDR_STATUS_ASATB = 0xF5,     /*!< Address of register STATUS_ASATB. */
    AS7058_REGADDR_STATUS_VCSEL = 0xF6,     /*!< Address of register STATUS_VCSEL. */
    AS7058_REGADDR_STATUS_VCSEL_VSS = 0xF7, /*!< Address of register STATUS_VCSEL_VSS. */
    AS7058_REGADDR_STATUS_VCSEL_VDD = 0xF8, /*!< Address of register STATUS_VCSEL_VDD. */
    AS7058_REGADDR_STATUS_LEADOFF = 0xF9,   /*!< Address of register STATUS_LEADOFF. */
    AS7058_REGADDR_STATUS = 0xFA,           /*!< Address of register STATUS. */
    AS7058_REGADDR_FIFO_LEVEL0 = 0xFB,      /*!< Address of register FIFO_LEVEL0. */
    AS7058_REGADDR_FIFO_LEVEL1 = 0xFC,      /*!< Address of register FIFO_LEVEL1. */
    AS7058_REGADDR_FIFOL = 0xFD,            /*!< Address of register FIFOL. */
    AS7058_REGADDR_FIFOM = 0xFE,            /*!< Address of register FIFOM. */
    AS7058_REGADDR_FIFOH = 0xFF,            /*!< Address of register FIFOH. */
};

/*! Type of ::as7058_reg_addresses. */
typedef uint8_t as7058_reg_addresses_t;

/*! BioZ measurement types */
enum as7058_bioz_measurement_types {
    AS7058_BIOZ_MEASUREMENT_TYPE_SHORT = 0,    /*!< Measurement of a short circuit. */
    AS7058_BIOZ_MEASUREMENT_TYPE_RESISTOR = 1, /*!< Measurement of the internal 2k reference resistor. */
    AS7058_BIOZ_MEASUREMENT_TYPE_BODY = 2,     /*!< Measurement of the body impedance. */
    AS7058_BIOZ_MEASUREMENT_TYPE_WRIST = 3,    /*!< Measurement of the wrist impedance. */
    AS7058_BIOZ_MEASUREMENT_TYPE_FINGER = 4,   /*!< Measurement of the finger impedance. */
    AS7058_BIOZ_MEASUREMENT_TYPE_TOTAL = 5,    /*!< Measurement of the total impedance. */

    AS7058_BIOZ_MEASUREMENT_TYPE_NUM = 6, /*!< Number of measurement types. */
};

/*! Register group for sensor status events. */
typedef struct status_regs {
    uint8_t status_seq;       /*!< Content of register STATUS_SEQ. */
    uint8_t status_led;       /*!< Content of register STATUS_LED. */
    uint8_t status_asata;     /*!< Content of register STATUS_ASATA. */
    uint8_t status_asatb;     /*!< Content of register STATUS_ASATB. */
    uint8_t status_vcsel;     /*!< Content of register STATUS_VCSEL. */
    uint8_t status_vcsel_vss; /*!< Content of register STATUS_VCSEL_VSS. */
    uint8_t status_vcsel_vdd; /*!< Content of register STATUS_VCSEL_VDD. */
    uint8_t status_leadoff;   /*!< Content of register STATUS_LEADOFF. */
    uint8_t status_iir;       /*!< ::TRUE when IIR interrupt set, otherwise ::FALSE. */
} as7058_status_events_t;

/*! Register group for power configuration.
 *
 * \note Registers PWR_ON and PWR_ISO were moved to the beginning because those registers need to be set first to access
 *       the other one. Furthermore, those registers are not in the same address range.
 */
typedef union {
    /*! Contents of the Power register group. */
    struct power_regs {
        uint8_t pwr_on;       /*!< Content of register PWR_ON. */
        uint8_t pwr_iso;      /*!< Content of register PWR_ISO. */
        uint8_t clk_cfg;      /*!< Content of register CLK_CFG. */
        uint8_t ref_cfg1;     /*!< Content of register REF_CFG1. */
        uint8_t ref_cfg2;     /*!< Content of register REF_CFG2. */
        uint8_t ref_cfg3;     /*!< Content of register REF_CFG3. */
        uint8_t standby_on1;  /*!< Content of register STANDBY_ON1. */
        uint8_t standby_on2;  /*!< Content of register STANDBY_ON2. */
        uint8_t standby_en1;  /*!< Content of register STANDBY_EN1. */
        uint8_t standby_en2;  /*!< Content of register STANDBY_EN2. */
        uint8_t standby_en3;  /*!< Content of register STANDBY_EN3. */
        uint8_t standby_en4;  /*!< Content of register STANDBY_EN4. */
        uint8_t standby_en5;  /*!< Content of register STANDBY_EN5. */
        uint8_t standby_en6;  /*!< Content of register STANDBY_EN6. */
        uint8_t standby_en7;  /*!< Content of register STANDBY_EN7. */
        uint8_t standby_en8;  /*!< Content of register STANDBY_EN8. */
        uint8_t standby_en9;  /*!< Content of register STANDBY_EN9. */
        uint8_t standby_en10; /*!< Content of register STANDBY_EN10. */
        uint8_t standby_en11; /*!< Content of register STANDBY_EN11. */
        uint8_t standby_en12; /*!< Content of register STANDBY_EN12. */
        uint8_t standby_en13; /*!< Content of register STANDBY_EN13. */
        uint8_t standby_en14; /*!< Content of register STANDBY_EN14. */
    } reg_vals;               /*!< Register values for power group. */
    /*! Register buffer for power configuration. */
    uint8_t reg_buffer[sizeof(struct power_regs)];
} as7058_reg_group_power_t;

/*! Register group for control configuration. */
typedef union {
    /*! Contents of the Control register group. */
    struct control_regs {
        uint8_t i2c_mode;  /*!< Content of register I2C_MODE. */
        uint8_t int_cfg;   /*!< Content of register INT_CFG. */
        uint8_t if_cfg;    /*!< Content of register IF_CFG. */
        uint8_t gpio_cfg1; /*!< Content of register GPIO_CFG1. */
        uint8_t gpio_cfg2; /*!< Content of register GPIO_CFG2. */
        uint8_t io_cfg;    /*!< Content of register IO_CFG. */
    } reg_vals;            /*!< Register values for control group. */
    /*! Register buffer for control configuration. */
    uint8_t reg_buffer[sizeof(struct control_regs)];
} as7058_reg_group_control_t;

/*! Register group for configuration of the LEDs. */
typedef union {
    /*! Contents of the LED register group. */
    struct led_regs {
        uint8_t vcsel_password; /*!< Content of register VCSEL_PASSWORD. */
        uint8_t vcsel_cfg;      /*!< Content of register VCSEL_CFG. */
        uint8_t vcsel_mode;     /*!< Content of register VCSEL_MODE. */
        uint8_t led_cfg;        /*!< Content of register LED_CFG. */
        uint8_t led_drv1;       /*!< Content of register LED_DRV1. */
        uint8_t led_drv2;       /*!< Content of register LED_DRV2. */
        uint8_t led1_ictrl;     /*!< Content of register LED1_ICTRL. */
        uint8_t led2_ictrl;     /*!< Content of register LED2_ICTRL. */
        uint8_t led3_ictrl;     /*!< Content of register LED3_ICTRL. */
        uint8_t led4_ictrl;     /*!< Content of register LED4_ICTRL. */
        uint8_t led5_ictrl;     /*!< Content of register LED5_ICTRL. */
        uint8_t led6_ictrl;     /*!< Content of register LED6_ICTRL. */
        uint8_t led7_ictrl;     /*!< Content of register LED7_ICTRL. */
        uint8_t led8_ictrl;     /*!< Content of register LED8_ICTRL. */
        uint8_t led_irng1;      /*!< Content of register LED_IRNG1. */
        uint8_t led_irng2;      /*!< Content of register LED_IRNG2. */
        uint8_t led_sub1;       /*!< Content of register LED_SUB1. */
        uint8_t led_sub2;       /*!< Content of register LED_SUB2. */
        uint8_t led_sub3;       /*!< Content of register LED_SUB3. */
        uint8_t led_sub4;       /*!< Content of register LED_SUB4. */
        uint8_t led_sub5;       /*!< Content of register LED_SUB5. */
        uint8_t led_sub6;       /*!< Content of register LED_SUB6. */
        uint8_t led_sub7;       /*!< Content of register LED_SUB7. */
        uint8_t led_sub8;       /*!< Content of register LED_SUB8. */
        uint8_t lowvds_wait;    /*!< Content of register LOWVDS_WAIT. */

    } reg_vals; /*!< Register values for LED group. */
    /*! Register buffer for LED configuration. */
    uint8_t reg_buffer[sizeof(struct led_regs)];
} as7058_reg_group_led_t;

/*! Register group for configuration of the photodiodes. */
typedef union {
    /*! Contents of the Photodiodes register group. */
    struct pd_regs {
        uint8_t pdsel_cfg;    /*!< Content of register PDSEL_CFG. */
        uint8_t ppg1_pdsel1;  /*!< Content of register PPG1_PDSEL1. */
        uint8_t ppg1_pdsel2;  /*!< Content of register PPG1_PDSEL2. */
        uint8_t ppg1_pdsel3;  /*!< Content of register PPG1_PDSEL3. */
        uint8_t ppg1_pdsel4;  /*!< Content of register PPG1_PDSEL4. */
        uint8_t ppg1_pdsel5;  /*!< Content of register PPG1_PDSEL5. */
        uint8_t ppg1_pdsel6;  /*!< Content of register PPG1_PDSEL6. */
        uint8_t ppg1_pdsel7;  /*!< Content of register PPG1_PDSEL7. */
        uint8_t ppg1_pdsel8;  /*!< Content of register PPG1_PDSEL8. */
        uint8_t ppg2_pdsel1;  /*!< Content of register PPG2_PDSEL1. */
        uint8_t ppg2_pdsel2;  /*!< Content of register PPG2_PDSEL2. */
        uint8_t ppg2_pdsel3;  /*!< Content of register PPG2_PDSEL3. */
        uint8_t ppg2_pdsel4;  /*!< Content of register PPG2_PDSEL4. */
        uint8_t ppg2_pdsel5;  /*!< Content of register PPG2_PDSEL5. */
        uint8_t ppg2_pdsel6;  /*!< Content of register PPG2_PDSEL6. */
        uint8_t ppg2_pdsel7;  /*!< Content of register PPG2_PDSEL7. */
        uint8_t ppg2_pdsel8;  /*!< Content of register PPG2_PDSEL8. */
        uint8_t ppg2_afesel1; /*!< Content of register PPG2_AFESEL1. */
        uint8_t ppg2_afesel2; /*!< Content of register PPG2_AFESEL2. */
        uint8_t ppg2_afesel3; /*!< Content of register PPG2_AFESEL3. */
        uint8_t ppg2_afesel4; /*!< Content of register PPG2_AFESEL4. */
        uint8_t ppg2_afeen;   /*!< Content of register PPG2_AFEEN. */
    } reg_vals;               /*!< Register values for PD group. */
    /*! Register buffer for photodiodes configuration. */
    uint8_t reg_buffer[sizeof(struct pd_regs)];
} as7058_reg_group_pd_t;

/*! Register group for configuration of the PD offset currents. */
typedef union {
    /*! Contents of the PD Offset Control register group. */
    struct ios_regs {
        uint8_t ios_ppg1_sub1; /*!< Content of register IOS_PPG1_SUB1. */
        uint8_t ios_ppg1_sub2; /*!< Content of register IOS_PPG1_SUB2. */
        uint8_t ios_ppg1_sub3; /*!< Content of register IOS_PPG1_SUB3. */
        uint8_t ios_ppg1_sub4; /*!< Content of register IOS_PPG1_SUB4. */
        uint8_t ios_ppg1_sub5; /*!< Content of register IOS_PPG1_SUB5. */
        uint8_t ios_ppg1_sub6; /*!< Content of register IOS_PPG1_SUB6. */
        uint8_t ios_ppg1_sub7; /*!< Content of register IOS_PPG1_SUB7. */
        uint8_t ios_ppg1_sub8; /*!< Content of register IOS_PPG1_SUB8. */
        uint8_t ios_ppg2_sub1; /*!< Content of register IOS_PPG2_SUB1. */
        uint8_t ios_ppg2_sub2; /*!< Content of register IOS_PPG2_SUB2. */
        uint8_t ios_ppg2_sub3; /*!< Content of register IOS_PPG2_SUB3. */
        uint8_t ios_ppg2_sub4; /*!< Content of register IOS_PPG2_SUB4. */
        uint8_t ios_ppg2_sub5; /*!< Content of register IOS_PPG2_SUB5. */
        uint8_t ios_ppg2_sub6; /*!< Content of register IOS_PPG2_SUB6. */
        uint8_t ios_ppg2_sub7; /*!< Content of register IOS_PPG2_SUB7. */
        uint8_t ios_ppg2_sub8; /*!< Content of register IOS_PPG2_SUB8. */
        uint8_t ios_ledoff;    /*!< Content of register IOS_LEDOFF. */
        uint8_t ios_cfg;       /*!< Content of register IOS_CFG. */
        uint8_t aoc_sar_thres; /*!< Content of register AOC_SAR_THRES. */
        uint8_t aoc_sar_range; /*!< Content of register AOC_SAR_RANGE. */
        uint8_t aoc_sar_ppg1;  /*!< Content of register AOC_SAR_PPG1. */
        uint8_t aoc_sar_ppg2;  /*!< Content of register AOC_SAR_PPG2. */
    } reg_vals;                /*!< Register values for IOS group. */
    /*! Register buffer for PD offset current configuration. */
    uint8_t reg_buffer[sizeof(struct ios_regs)];
} as7058_reg_group_ios_t;

/*! Register group for configuration of PPG. */
typedef union {
    /*! Contents of the PPG register group. */
    struct ppg_regs {
        uint8_t ppgmod_cfg1;  /*!< Content of register PPGMOD_CFG1. */
        uint8_t ppgmod_cfg2;  /*!< Content of register PPGMOD_CFG2. */
        uint8_t ppgmod_cfg3;  /*!< Content of register PPGMOD_CFG3. */
        uint8_t ppgmod1_cfg1; /*!< Content of register PPGMOD1_CFG1. */
        uint8_t ppgmod1_cfg2; /*!< Content of register PPGMOD1_CFG2. */
        uint8_t ppgmod1_cfg3; /*!< Content of register PPGMOD1_CFG3. */
        uint8_t ppgmod2_cfg1; /*!< Content of register PPGMOD2_CFG1. */
        uint8_t ppgmod2_cfg2; /*!< Content of register PPGMOD2_CFG2. */
        uint8_t ppgmod2_cfg3; /*!< Content of register PPGMOD2_CFG3. */
    } reg_vals;               /*!< Register values for PPG group. */
    /*! Register buffer for PPG configuration. */
    uint8_t reg_buffer[sizeof(struct ppg_regs)];
} as7058_reg_group_ppg_t;

/*! Register group for configuration of ECG. */
typedef union {
    /*! Contents of the ECG register group. */
    struct ecg_regs {
        uint8_t bioz_cfg;       /*!< Content of register BIOZ_CFG. */
        uint8_t bioz_excit;     /*!< Content of register BIOZ_EXCIT. */
        uint8_t bioz_mixer;     /*!< Content of register BIOZ_MIXER. */
        uint8_t bioz_select;    /*!< Content of register BIOZ_SELECT. */
        uint8_t bioz_gain;      /*!< Content of register BIOZ_GAIN. */
        uint8_t ecgmod_cfg1;    /*!< Content of register ECGMOD_CFG1. */
        uint8_t ecgmod_cfg2;    /*!< Content of register ECGMOD_CFG2. */
        uint8_t ecgimux_cfg1;   /*!< Content of register ECGIMUX_CFG1. */
        uint8_t ecgimux_cfg2;   /*!< Content of register ECGIMUX_CFG2. */
        uint8_t ecgimux_cfg3;   /*!< Content of register ECGIMUX_CFG3. */
        uint8_t ecgamp_cfg1;    /*!< Content of register ECGAMP_CFG1. */
        uint8_t ecgamp_cfg2;    /*!< Content of register ECGAMP_CFG2. */
        uint8_t ecgamp_cfg3;    /*!< Content of register ECGAMP_CFG3. */
        uint8_t ecgamp_cfg4;    /*!< Content of register ECGAMP_CFG4. */
        uint8_t ecgamp_cfg5;    /*!< Content of register ECGAMP_CFG5. */
        uint8_t ecgamp_cfg6;    /*!< Content of register ECGAMP_CFG6. */
        uint8_t ecgamp_cfg7;    /*!< Content of register ECGAMP_CFG7. */
        uint8_t ecg_bioz;       /*!< Content of register ECG_BIOZ. */
        uint8_t leadoff_cfg;    /*!< Content of register LEADOFF_CFG*/
        uint8_t leadoff_thresl; /*!< Content of register LEADOFF_THRESL. */
        uint8_t leadoff_thresh; /*!< Content of register LEADOFF_THRESH. */
    } reg_vals;                 /*!< Register values for ECG group. */
    /*! Register buffer for ECG configuration. */
    uint8_t reg_buffer[sizeof(struct ecg_regs)];
} as7058_reg_group_ecg_t;

/*! Register group for configuration of the sinc filter. */
typedef union {
    /*! Contents of the Sinc Filter register group. */
    struct sinc_regs {
        uint8_t ppg_sinc_cfga;  /*!< Content of register PPG_SINC_CFGA. */
        uint8_t ppg_sinc_cfgb;  /*!< Content of register PPG_SINC_CFGB. */
        uint8_t ppg_sinc_cfgc;  /*!< Content of register PPG_SINC_CFGC. */
        uint8_t ppg_sinc_cfgd;  /*!< Content of register PPG_SINC_CFGD. */
        uint8_t ecg1_sinc_cfga; /*!< Content of register ECG1_SINC_CFGA. */
        uint8_t ecg1_sinc_cfgb; /*!< Content of register ECG1_SINC_CFGB. */
        uint8_t ecg1_sinc_cfgc; /*!< Content of register ECG1_SINC_CFGC. */
        uint8_t ecg2_sinc_cfga; /*!< Content of register ECG2_SINC_CFGA. */
        uint8_t ecg2_sinc_cfgb; /*!< Content of register ECG2_SINC_CFGB. */
        uint8_t ecg2_sinc_cfgc; /*!< Content of register ECG2_SINC_CFGC. */
        uint8_t ecg_sinc_cfg;   /*!< Content of register ECG_SINC_CFG. */
    } reg_vals;                 /*!< Register values for SINC group. */
    /*! Register buffer for SINC filter configuration. */
    uint8_t reg_buffer[sizeof(struct sinc_regs)];
} as7058_reg_group_sinc_t;

/*! Register group for configuration of the Infinite Impulse Response filter (IIR filter). */
typedef union {
    /*! Contents of the IIR Filter register group. */
    struct iir_regs {
        uint8_t iir_cfg;                   /*!< Content of register IIR_CFG. */
        uint8_t reserved;                  /*!< Unused padding byte. */
        int16_t iir_coeff_data_sos[12][5]; /*!< Coefficients of the cascaded IIR second-order sections. Up to 12
                                                sections are supported. Each section has five coefficients. */
    } reg_vals;                            /*!< Register values for IIR group. */
    /*! Register buffer for IIR filter configuration. */
    uint8_t reg_buffer[sizeof(struct iir_regs)];
} as7058_reg_group_iir_t;

/*! Register group for configuration of the sequencer. */
typedef union {
    /*! Contents of the Sequencer register group. */
    struct seq_regs {
        uint8_t irq_enable;    /*!< Content of register IRQ_ENABLE. */
        uint8_t ppg_sub_wait;  /*!< Content of register PPG_SUB_WAIT. */
        uint8_t ppg_sar_wait;  /*!< Content of register PPG_SAR_WAIT. */
        uint8_t ppg_led_init;  /*!< Content of register PPG_LED_INIT. */
        uint8_t ppg_freql;     /*!< Content of register PPG_FREQL. */
        uint8_t ppg_freqh;     /*!< Content of register PPG_FREQH. */
        uint8_t ppg1_sub_en;   /*!< Content of register PPG1_SUB_EN. */
        uint8_t ppg2_sub_en;   /*!< Content of register PPG2_SUB_EN. */
        uint8_t ppg_mode_1;    /*!< Content of register PPG_MODE1. */
        uint8_t ppg_mode_2;    /*!< Content of register PPG_MODE2. */
        uint8_t ppg_mode_3;    /*!< Content of register PPG_MODE3. */
        uint8_t ppg_mode_4;    /*!< Content of register PPG_MODE4. */
        uint8_t ppg_mode_5;    /*!< Content of register PPG_MODE5. */
        uint8_t ppg_mode_6;    /*!< Content of register PPG_MODE6. */
        uint8_t ppg_mode_7;    /*!< Content of register PPG_MODE7. */
        uint8_t ppg_mode_8;    /*!< Content of register PPG_MODE8. */
        uint8_t ppg_cfg;       /*!< Content of register PPG_CFG. */
        uint8_t ecg_freql;     /*!< Content of register ECG_FREQL. */
        uint8_t ecg_freqh;     /*!< Content of register ECG_FREQH. */
        uint8_t ecg1_freqdivl; /*!< Content of register ECG1_FREQDIVL. */
        uint8_t ecg1_freqdivh; /*!< Content of register ECG1_FREQDIVH. */
        uint8_t ecg2_freqdivl; /*!< Content of register ECG2_FREQDIVL. */
        uint8_t ecg2_freqdivh; /*!< Content of register ECG2_FREQDIVH. */
        uint8_t ecg_subs;      /*!< Content of register ECG_SUBS. */
        uint8_t leadoff_initl; /*!< Content of register LEADOFF_INITL. */
        uint8_t leadoff_inith; /*!< Content of register LEADOFF_INITH. */
        uint8_t ecg_initl;     /*!< Content of register ECG_INITL. */
        uint8_t ecg_inith;     /*!< Content of register ECG_INITH. */
        uint8_t sample_num;    /*!< Content of register SAMPLE_NUM. */
    } reg_vals;                /*!< Register values for sequencer group. */
    /*! Register buffer for sequencer configuration. */
    uint8_t reg_buffer[sizeof(struct seq_regs)];
} as7058_reg_group_seq_t;

/*! Register group for configuration of post-processing engine. */
typedef union {
    /*! Contents of the Post-Processing register group. */
    struct pp_regs {
        uint8_t pp_cfg;   /*!< Content of register PP_CFG. */
        uint8_t ppg1_pp1; /*!< Content of register PPG1_PP1. */
        uint8_t ppg1_pp2; /*!< Content of register PPG1_PP2. */
        uint8_t ppg2_pp1; /*!< Content of register PPG2_PP1. */
        uint8_t ppg2_pp2; /*!< Content of register PPG2_PP2. */
    } reg_vals;           /*!< Register values for post-processing group. */
    /*! Register buffer for post-processing configuration. */
    uint8_t reg_buffer[sizeof(struct pp_regs)];
} as7058_reg_group_pp_t;

/*! Register group for configuration of the FIFO handling. */
typedef union {
    /*! Contents of the FIFO register group. */
    struct fifo_regs {
        uint8_t fifo_threshold; /*!< Content of register FIFO_THRESHOLD. */
        uint8_t fifo_ctrl;      /*!< Content of register FIFO_CTRL. */
    } reg_vals;                 /*!< Register values for FIFO group. */
    /*! Register buffer for FIFO configuration. */
    uint8_t reg_buffer[sizeof(struct fifo_regs)];
} as7058_reg_group_fifo_t;

/*! Represents how the AS7058 AFE provides the SAR status. */
enum as7058_sar_transfer_mode {
    AS7058_SAR_TRANSFER_MODE_SEPARATE = 0, /*!< PD offset is provided in a separate FIFO item. */
    AS7058_SAR_TRANSFER_MODE_INLINE,       /*!< ADC data and upper four bits of the PD offset are contained in a single
                                                FIFO item. The AS7058 AFE truncates the ADC data to make room for the
                                                upper four bits of the PD offset. The lower four bits of the PD offset
                                                (which are not controlled by SAR) must be known from configuration or
                                                must be read from the corresponding register. */
};

/*! Type for ::as7058_sar_transfer_mode. */
typedef uint8_t as7058_sar_transfer_mode_t;

/*! Measurement settings which can be read out after finished register configuration. */
typedef struct {
    uint32_t ppg_sample_period_us;      /*!< Sample period for PPG in microseconds. */
    uint32_t ecg_seq1_sample_period_us; /*!< Sample period for ECG sequence 1 in microseconds. */
    uint32_t ecg_seq2_sample_period_us; /*!< Sample period for ECG sequence 2 in microseconds. */
    uint32_t fifo_map; /*!< Definition which sub-samples are mapped inside FIFO. More than one flag can be set. See
                          ::as7058_sub_sample_flags. */
    as7058_sub_sample_ids_t
        agc_channels[AGC_MAX_CHANNEL_CNT]; /*!< Activated AGC channels. ::AS7058_SUB_SAMPLE_ID_DISABLED is set on unused
                                              channels. */
    uint32_t sar_map; /*!< Defines which sub-samples have SAR enabled. More than one flag can be set. See
                           ::as7058_sub_sample_flags. */
    as7058_sar_transfer_mode_t sar_transfer_mode; /*!< Defines how the SAR status is provided by the AS7058 AFE. */
    uint8_t reserved[3];                          /*!< Padding bytes, reserved for future use. */
} as7058_meas_config_t;

/*! Configuration for the EDA impedance scaling measurement mode. */
typedef struct {
    uint16_t num_averages; /*!< Number of samples to average. */
} as7058_eda_scaling_config_t;

/*! Configuration for the BioZ measurement mode. */
typedef struct {
    uint16_t num_averages;              /*!< Number of samples to average. */
    uint16_t num_dropped_first_samples; /*!< Number of samples to drop before averaging. Because of settling time, BioZ
                                             results can be optimized by dropping the first samples. */
} as7058_bioz_meas_config_t;

/*! Result of the EDA impedance scaling measurement mode. */
typedef struct {
    uint32_t ref_resistor;        /*!< Resistance of the reference resistor in ohm. This value is calculated from OTP
                                       data. */
    uint32_t ref_temperature_adc; /*!< ADC counts of the temperature when the resistance of the reference resistor was
                                       measured. This value is calculated from OTP data. */
    uint32_t temperature_adc;     /*!< ADC counts of the temperature during the EDA scaling measurements. It is set to
                                       UINT32_MAX if temperature measurement is disabled. */
    int32_t slope;                /*!< Slope of the temperature scaled by 1000000. */
    uint32_t short_p;             /*!< Measured EDA+ while electrical circuit has a short. */
    uint32_t short_n;             /*!< Measured EDA- while electrical circuit has a short. */
    uint32_t resistor_p;          /*!< Measured EDA+ while electrical circuit is connected with the reference resistor.
                                   */
    uint32_t resistor_n;          /*!< Measured EDA- while electrical circuit is connected with the reference resistor.
                                   */
} as7058_eda_scaling_result_t;

/*! Result of a single BioZ measurement. */
struct as7058_bioz_measurement {
    uint32_t in_phase;   /*!< In-phase component of the measured BioZ signal. */
    uint32_t quadrature; /*!< Quadrature component of the measured BioZ signal. */
};

/*! Result of the BioZ measurement mode. */
typedef struct {
    uint32_t ref_resistor;        /*!< Resistance of the reference resistor in ohm. This value is calculated from OTP
                                       data. */
    uint32_t ref_temperature_adc; /*!< ADC counts of the temperature when the resistance of the reference resistor was
                                       measured. This value is calculated from OTP data. */
    uint32_t temperature_adc;     /*!< ADC counts of the temperature during the BioZ measurements. It is set to
                                       UINT32_MAX if temperature measurement is disabled. */
    int32_t slope;                /*!< Slope of the temperature scaled by 1000000. */
    struct as7058_bioz_measurement
        measurements[AS7058_BIOZ_MEASUREMENT_TYPE_NUM]; /*!< BioZ measurement results acquired with different
                                                             measurement setups. See ::as7058_bioz_measurement_types. */
} as7058_bioz_meas_result_t;

/*! Measurement configuration for PD offset calibration. */
typedef struct {
    as7058_sub_sample_ids_t sub_sample_id; /*!< Sub-sample to use for calibration, see ::as7058_sub_sample_ids.
                                                Depending on the selected sub-sample, either PPG modulator 1 or PPG
                                                modulator 2 is calibrated. ECG sub-samples must not be selected. */
    uint8_t reserved;                      /*!< Padding byte, reserved for future use. Must be set to zero. */
    uint16_t num_averages;                 /*!< Number of samples to acquire and average per calibration point
                                                measurement. */
    uint16_t ppg_sample_period_multiplier; /*!< Base sample period multiplier to use during calibration. The base sample
                                                period is 31.25 microseconds. The resulting sample period is obtained by
                                                incrementing the multiplier by one and by multiplying the base sample
                                                period by the incremented multiplier. For example, a multiplier value of
                                                9 results in sample period of (9 + 1) * 31.25 microseconds = 312.5
                                                microseconds. The contents of registers ::AS7058_REGADDR_PPG_FREQL and
                                                ::AS7058_REGADDR_PPG_FREQH are temporarily replaced by the provided
                                                value during calibration. */
} as7058_pd_offset_calibration_config_t;

/*! Result structure for PD offset calibration. */
typedef struct {
    uint32_t compensation_table[AS7058_PD_OFFSET_CALIBRATION_COMPENSATION_TABLE_ELEMENTS_NUM]; /*!< Contains the
                                                                                                    measured ADC count
                                                                                                    offsets for
                                                                                                    different photodiode
                                                                                                    offset current
                                                                                                    values. PD offset
                                                                                                    calibration takes
                                                                                                    the lower 4 bits of
                                                                                                    the photodiode
                                                                                                    offset current of
                                                                                                    the selected PPG1 or
                                                                                                    PPG2 sub-sample from
                                                                                                    the chip
                                                                                                    configuration and
                                                                                                    modifies the upper 4
                                                                                                    bits during
                                                                                                    calibration. The
                                                                                                    first item in the
                                                                                                    array contains the
                                                                                                    ADC count offset
                                                                                                    when the upper 4
                                                                                                    bits are set to
                                                                                                    value 1. The last
                                                                                                    item contains the
                                                                                                    offset when the
                                                                                                    upper 4 bits are set
                                                                                                    to value 15. */
} as7058_pd_offset_calibration_result_t;

/*! Special measurement results. */
typedef union {
    as7058_bioz_meas_result_t bioz;                              /*!< Result for mode ::AS7058_MEAS_MODE_SPECIAL_BIOZ.
                                                                  */
    as7058_eda_scaling_result_t eda_scaling;                     /*!< Result for mode
                                                                      ::AS7058_MEAS_MODE_SPECIAL_SCALING_EDA. */
    as7058_pd_offset_calibration_result_t pd_offset_calibration; /*!< Result for mode
                                                                      ::AS7058_MEAS_MODE_SPECIAL_PD_OFFSET_CALIBRATION.
                                                                  */
} as7058_special_measurement_result_t;

/*!
 * \brief Callback function used to provide regular measurement results to the application.
 *
 * A callback of this type is registered via the function ::as7058_initialize.
 * During measurements of mode ::AS7058_MEAS_MODE_NORMAL, this function is called whenever data is received from AS7058.
 *
 * \param[in] error             Default ::ERR_SUCCESS, otherwise an error occurred during measurement and the
 *                              measurement is stopped. See ::error_codes.
 * \param[in] p_fifo_data       Pointer to the measurement data, the content depends on configuration.
 * \param[in] fifo_data_size    Size of the FIFO data buffer in bytes.
 * \param[in] p_agc_statuses    Pointer to AGC status structure.
 * \param[in] agc_statuses_num  Number of AGC status elements.
 * \param[in] sensor_events     Combination of all possible sensor status events but FIFO status.
 *                              See ::as7058_status_events_t. When an interrupt is disabled, the corresponding
 *                              status field is always set to zero.
 * \param[in] p_cb_param        Application parameter which was set when ::as7058_initialize was called.
 */
typedef void (*as7058_callback_t)(err_code_t error, const uint8_t *p_fifo_data, uint16_t fifo_data_size,
                                  const agc_status_t *p_agc_statuses, uint8_t agc_statuses_num,
                                  as7058_status_events_t sensor_events, const void *p_cb_param);

/*!
 * \brief Callback function used to provide special measurement results to the application.
 *
 * A callback of this type is registered via the function ::as7058_initialize.
 * During measurements of modes ::AS7058_MEAS_MODE_SPECIAL_BIOZ and ::AS7058_MEAS_MODE_SPECIAL_SCALING_EDA, this
 * function is called whenever measurement results are available.
 *
 * \param[in] mode                  Current measurement mode.
 * \param[in] p_result              Result of the special measurement.
 *                                  See ::as7058_special_measurement_result_t.
 * \param[in] result_size           Size of the special measurement result.
 * \param[in] p_cb_param            Application parameter which was set when ::as7058_initialize was called.
 */
typedef void (*as7058_callback_special_measurement_t)(as7058_meas_mode_t mode,
                                                      const as7058_special_measurement_result_t *p_result,
                                                      uint16_t result_size, const void *p_cb_param);

/******************************************************************************
 *                            TYPE SIZE VALIDATION                            *
 ******************************************************************************/

M_STATIC_ASSERT_TYPE_SIZE(as7058_reg_group_power_t, 22);  /*!< Size check of register group power. */
M_STATIC_ASSERT_TYPE_SIZE(as7058_reg_group_control_t, 6); /*!< Size check of register group control. */
M_STATIC_ASSERT_TYPE_SIZE(as7058_reg_group_led_t, 25);    /*!< Size check of register group LED. */
M_STATIC_ASSERT_TYPE_SIZE(as7058_reg_group_pd_t, 22);     /*!< Size check of register group photodiodes. */
M_STATIC_ASSERT_TYPE_SIZE(as7058_reg_group_ios_t, 22);    /*!< Size check of register group IOS. */
M_STATIC_ASSERT_TYPE_SIZE(as7058_reg_group_ppg_t, 9);     /*!< Size check of register group PPG. */
M_STATIC_ASSERT_TYPE_SIZE(as7058_reg_group_ecg_t, 21);    /*!< Size check of register group ECG. */
M_STATIC_ASSERT_TYPE_SIZE(as7058_reg_group_sinc_t, 11);   /*!< Size check of register group SINC. */
M_STATIC_ASSERT_TYPE_SIZE(as7058_reg_group_iir_t, 122);   /*!< Size check of register group IIR. */
M_STATIC_ASSERT_TYPE_SIZE(as7058_reg_group_seq_t, 29);    /*!< Size check of register group SEQ. */
M_STATIC_ASSERT_TYPE_SIZE(as7058_reg_group_pp_t, 5);      /*!< Size check of register group post processing. */
M_STATIC_ASSERT_TYPE_SIZE(as7058_reg_group_fifo_t, 2);    /*!< Size check of register group FIFO. */
M_STATIC_ASSERT_TYPE_SIZE(as7058_meas_config_t, 24 + AGC_MAX_CHANNEL_CNT); /*!< Size check of measurement configuration
                                                                                structure. */
M_STATIC_ASSERT_TYPE_SIZE(as7058_status_events_t, 9);        /*!< Size check of status events structure. */
M_STATIC_ASSERT_TYPE_SIZE(as7058_modulator_t, 1);            /*!< Size check of modulator IDs. */
M_STATIC_ASSERT_TYPE_SIZE(as7058_modulator_sub_sample_t, 1); /*!< Size check of modulator sub-sample IDs. */
M_STATIC_ASSERT_TYPE_SIZE(as7058_fifo_data_marker_t, 1);     /*!< Size check of FIFO data marker. */
M_STATIC_ASSERT_TYPE_SIZE(as7058_sar_transfer_mode_t, 1);    /*!< Size check of SAR transfer mode. */
M_STATIC_ASSERT_TYPE_SIZE(as7058_meas_mode_t, 1);            /*!< Size check of measurement mode. */
M_STATIC_ASSERT_TYPE_SIZE(as7058_eda_scaling_config_t, 2);  /*!< Size check of EDA scaling measurement configuration. */
M_STATIC_ASSERT_TYPE_SIZE(as7058_eda_scaling_result_t, 32); /*!< Size check of EDA scaling measurement result. */
M_STATIC_ASSERT_TYPE_SIZE(as7058_bioz_meas_config_t, 4);    /*!< Size check of BioZ measurement configuration. */
M_STATIC_ASSERT_TYPE_SIZE(as7058_bioz_meas_result_t, 64);   /*!< Size check of BioZ measurement result. */
M_STATIC_ASSERT_TYPE_SIZE(as7058_special_measurement_result_t, 64);   /*!< Size check of special measurement result. */
M_STATIC_ASSERT_TYPE_SIZE(as7058_pd_offset_calibration_config_t, 6);  /*!< Size check of PD offset calibration
                                                                           configuration. */
M_STATIC_ASSERT_TYPE_SIZE(as7058_pd_offset_calibration_result_t, 60); /*!< Size check of PD offset calibration results.
                                                                       */

/*! @} */

#endif /* __AS7058_TYPEDEFS_H__ */
