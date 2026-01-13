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

#include "as7058_raw_app.h"
#include "fifo.h"
#include "std_inc.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

#ifndef AS7058_RAW_APP_MAX_PACKET_SIZE
/*! The maximum size of a packet. */
#define AS7058_RAW_APP_MAX_PACKET_SIZE 149
#endif

/*!
 * \brief The size of the header of a packet.
 *
 * It consists of the packet counter field, the FIFO data count field, the accelerometer data count field, and the flags
 * field.
 */
#define AS7058_RAW_APP_HEADER_SIZE 4

/*! Offset of the packet counter field, relative to the begin of the packet. */
#define AS7058_RAW_APP_FIELD_OFFSET_PACKET_CNT 0

/*! Offset of the FIFO data count field, relative to the begin of the packet. */
#define AS7058_RAW_APP_FIELD_OFFSET_FIFO_DATA_CNT 1

/*! Offset of the accelerometer data count field, relative to the begin of the packet. */
#define AS7058_RAW_APP_FIELD_OFFSET_ACC_DATA_CNT 2

/*! Offset of the flags field, relative to the begin of the packet. */
#define AS7058_RAW_APP_FIELD_OFFSET_FLAGS 3

/*! The maximum number of accelerometer samples in a packet. */
#define AS7058_RAW_APP_MAX_ACC_SAMPLES_PER_PACKET 20

#ifndef AS7058_RAW_APP_OUTPUT_QUEUE_SIZE
/*! The size of the output queue. */
#define AS7058_RAW_APP_OUTPUT_QUEUE_SIZE 2999
#endif

/*! Magic number used in ::g_agc_statuses_num when the number of AGC statuses is not yet known. */
#define AS7058_RAW_APP_AGC_STATUSES_NUM_UNKNOWN 0xFF

/*! @defgroup AS7058_RAW_APP_FLAGS Packet Header Flags
 * @{ */

/*! Defines the bits that are used to store the number of AGC statuses in the packets. */
#define AS7058_FLAGS_AGC_STATUSES_NUM_MASK 0x0F

/*! Indicates the presence of the status event data in the packet. */
#define AS7058_FLAGS_STATUS_EVENTS_PRESENT (1 << 4)

/*! Indicates the presence of the external event occurrence counter in the packet. */
#define AS7058_FLAGS_EXT_EVENT_CNT_PRESENT (1 << 5)

/*! Indicates that accelerometer data has been copied to the packet. */
#define AS7058_FLAGS_INTERNAL_ACC_DATA_COPIED (1 << 6)

/*! Indicates that the packet is not finalized yet. */
#define AS7058_FLAGS_INTERNAL_NOT_READY_FOR_OUTPUT (1 << 7)

/*! Bitmask where the flags of all PPG sub-samples are set. */
#define AS7058_SUB_SAMPLE_FLAG_ALL_PPG                                                                                 \
    (AS7058_SUB_SAMPLE_FLAG_PPG1_SUB1 | AS7058_SUB_SAMPLE_FLAG_PPG1_SUB2 | AS7058_SUB_SAMPLE_FLAG_PPG1_SUB3 |          \
     AS7058_SUB_SAMPLE_FLAG_PPG1_SUB4 | AS7058_SUB_SAMPLE_FLAG_PPG1_SUB5 | AS7058_SUB_SAMPLE_FLAG_PPG1_SUB6 |          \
     AS7058_SUB_SAMPLE_FLAG_PPG1_SUB7 | AS7058_SUB_SAMPLE_FLAG_PPG1_SUB8 | AS7058_SUB_SAMPLE_FLAG_PPG2_SUB1 |          \
     AS7058_SUB_SAMPLE_FLAG_PPG2_SUB2 | AS7058_SUB_SAMPLE_FLAG_PPG2_SUB3 | AS7058_SUB_SAMPLE_FLAG_PPG2_SUB4 |          \
     AS7058_SUB_SAMPLE_FLAG_PPG2_SUB5 | AS7058_SUB_SAMPLE_FLAG_PPG2_SUB6 | AS7058_SUB_SAMPLE_FLAG_PPG2_SUB7 |          \
     AS7058_SUB_SAMPLE_FLAG_PPG2_SUB8)

/*! Bitmask where the flags of all sub-samples of ECG SEQ1 are set. */
#define AS7058_SUB_SAMPLE_FLAG_ALL_ECG_SEQ1                                                                            \
    (AS7058_SUB_SAMPLE_FLAG_ECG_SEQ1_SUB1 | AS7058_SUB_SAMPLE_FLAG_ECG_SEQ1_SUB2)

/*! Bitmask where the flags of all sub-samples of ECG SEQ2 are set. */
#define AS7058_SUB_SAMPLE_FLAG_ALL_ECG_SEQ2 AS7058_SUB_SAMPLE_FLAG_ECG_SEQ2_SUB1

/*! } */

/*! Checks whether the module is in the expected state and returns ::ERR_PERMISSION otherwise. */
#define M_CHECK_STATE(expected)                                                                                        \
    do {                                                                                                               \
        if (g_state != (expected)) {                                                                                   \
            return ERR_PERMISSION;                                                                                     \
        }                                                                                                              \
    } while (0)

/*!
 * \brief Checks whether the pointer members of ::g_current_packet are set to a non-NULL value. This also implicitly
 * checks whether a non-finalized packet currently exists.
 */
#define M_CHECK_CURRENT_PACKET_POINTERS()                                                                              \
    do {                                                                                                               \
        M_CHECK_NULL_POINTER(g_current_packet.p_fifo_data_cnt);                                                        \
        M_CHECK_NULL_POINTER(g_current_packet.p_acc_data_cnt);                                                         \
        M_CHECK_NULL_POINTER(g_current_packet.p_flags);                                                                \
    } while (0)

/*! Contains information regarding a packet that is only need while it is not finalized. */
typedef struct {
    volatile uint8_t *p_fifo_data_cnt; /*!< Pointer to the FIFO data count header field. This field also serves as
                                            indicator whether the structure is valid. It is valid when the value of this
                                            field is not NULL. */
    volatile uint8_t *p_acc_data_cnt;  /*!< Pointer to the accelerometer samples count header field. */
    volatile uint8_t *p_flags;         /*!< Pointer to the flags header field. */
    vs_acc_data_t acc_data_buffer[AS7058_RAW_APP_MAX_ACC_SAMPLES_PER_PACKET]; /*!< Buffer for storing accelerometer
                                                                                   samples. The fill level is stored in
                                                                                   the packet header. */
} as7058_raw_app_non_finalized_packet_t;

/*! States of the module. */
typedef enum {
    AS7058_RAW_APP_STATE_UNINITIALIZED = 0, /*!< Module is in uninitialized state. */
    AS7058_RAW_APP_STATE_CONFIGURATION,     /*!< Module is in configuration state. */
    AS7058_RAW_APP_STATE_PROCESSING         /*!< Module is in processing state. */
} as7058_raw_app_state_t;

/******************************************************************************
 *                                  GLOBALS                                   *
 ******************************************************************************/

/*! The current state of the module. */
static volatile as7058_raw_app_state_t g_state = AS7058_RAW_APP_STATE_UNINITIALIZED;

/*! The maximum number of FIFO data samples to include in a single packet to ensure frequent updates. */
static volatile uint8_t g_fifo_data_cnt_threshold;

/*! Indicates whether accelerometer data shall be included in the output. */
static volatile uint8_t g_include_acc_data;

/*! The buffer used by the FIFO output queue. */
static volatile uint8_t g_output_queue_buffer[AS7058_RAW_APP_OUTPUT_QUEUE_SIZE + 1];

/*! Describes the FIFO output queue. */
static volatile fifo_t g_output_queue = {
    .itemsize = sizeof(g_output_queue_buffer[0]),
    .capacity = AS7058_RAW_APP_OUTPUT_QUEUE_SIZE,
    .in = 0,
    .out = 0,
    .data = (void *)g_output_queue_buffer,
};

/*!
 * \brief The AGC statuses that were provided to the module previously. See ::g_agc_statuses_num for the number of valid
 *        items in the array.
 */
static agc_status_t g_last_agc_statuses[AGC_MAX_CHANNEL_CNT];

/*!
 * \brief The number of enabled AGC channels. When the number is not known yet, it is set to
 *        ::AS7058_RAW_APP_AGC_STATUSES_NUM_UNKNOWN. In this case, ::g_last_agc_statuses contains no valid data.
 *        Otherwise, this variable contains the number of valid items in the ::g_last_agc_statuses array.
 */
static uint8_t g_agc_statuses_num;

/*! The current non-finalized output packet. */
static volatile as7058_raw_app_non_finalized_packet_t g_current_packet;

/*! The number of finalized output packets. It is expected to overflow. */
static volatile uint8_t g_packet_counter;

/******************************************************************************
 *                               LOCAL FUNCTIONS                              *
 ******************************************************************************/

/*!
 * \brief Checks whether the AGC statuses changed in a way that require transmission of the AGC statuses.
 *
 * \param[in] p_new_agc_statuses    Pointer to the array containing the current AGC statuses.
 * \param[in] new_agc_statuses_num  Number of items in the new AGC statuses array.
 * \param[in] p_last_agc_statuses   Pointer to the array containing the old AGC statuses.
 * \param[in] last_agc_statuses_num Number of items in the old AGC statuses array or
 *                                  ::AS7058_RAW_APP_AGC_STATUSES_NUM_UNKNOWN if there are no valid last AGC statuses.
 *
 * \retval ::TRUE  AGC statuses transmission required.
 * \retval ::FALSE AGC statuses transmission not required.
 */
static uint8_t check_agc_statuses_change(const agc_status_t *p_new_agc_statuses, uint8_t new_agc_statuses_num,
                                         const agc_status_t *p_last_agc_statuses, uint8_t last_agc_statuses_num)
{
    if (NULL == p_new_agc_statuses || new_agc_statuses_num > AGC_MAX_CHANNEL_CNT) {
        return FALSE;
    }

    uint8_t agc_statuses_changed = FALSE;
    if (last_agc_statuses_num != AS7058_RAW_APP_AGC_STATUSES_NUM_UNKNOWN) {
        /* When last_agc_statuses_num is not set to AS7058_RAW_APP_AGC_STATUSES_NUM_UNKNOWN, AGC status information has
         * been received before and p_last_agc_statuses contains valid data */

        if (new_agc_statuses_num != last_agc_statuses_num) {
            /* Number of AGC statuses should never change during a measurement, so this should never happen */
            return FALSE;
        }

        for (uint8_t i = 0; i < new_agc_statuses_num; i++) {
            const agc_status_t *p_new = &p_new_agc_statuses[i];
            const agc_status_t *p_last = &p_last_agc_statuses[i];

            /* For detecting an AGC status change, all fields of the AGC status are looked at separately. If the value
             * of a current field changes, the AGC status is always considered to have changed. If a change state
             * changes to a value other than AGC_STATE_UNCHANGED, the AGC status is also considered to have changed.
             * The check for AGC_STATE_UNCHANGED is implemented to suppress AGC status changes that contain no
             * information. (For example, when the PD offset current is increased, the AGC status of that AGC execution
             * contains the increased PD offset current and its PD offset change state is set to AGC_STATE_INCREASED.
             * Assuming no further PD offset current changes, the AGC status of the next AGC execution contains the same
             * PD offset current as before, but the change state changes to AGC_STATE_UNCHANGED. If the check for
             * AGC_STATE_UNCHANGED hadn't been implemented, this would also have been considered an AGC status change.
             *
             * No special handling for AGC_STATE_NOT_CONTROLLED and AGC_STATE_UNDEFINED is required as if one of these
             * statuses is present in a change state field, it is also present in that field in each other AGC status
             * that is generated throughout the entire measurement. The corresponding current value also remains set to
             * a constant value throughout the entire measurement.
             *
             * This information is valid for version 2.0.0 of the AGC algorithm. */

            uint8_t led_status_changed =
                (p_new->led_change != p_last->led_change) && (p_new->led_change != AGC_STATE_UNCHANGED);
            uint8_t led_current_changed = p_new->led_current != p_last->led_current;
            uint8_t pd_offset_status_changed = (p_new->pd_offset_change != p_last->pd_offset_change) &&
                                               (p_new->pd_offset_change != AGC_STATE_UNCHANGED);
            uint8_t pd_offset_current_changed = p_new->pd_offset_current != p_last->pd_offset_current;

            if (led_status_changed || led_current_changed || pd_offset_status_changed || pd_offset_current_changed) {
                agc_statuses_changed = TRUE;
                break;
            }
        }
    } else {
        /* When last_agc_statuses_num is still set to AS7058_RAW_APP_AGC_STATUSES_NUM_UNKNOWN, this is the first time we
         * receive AGC status information. */

        /* Always send first AGC statuses */
        agc_statuses_changed = TRUE;
    }

    return agc_statuses_changed;
}

/*!
 * \brief Checks whether the status event changed.
 *
 * \param[in] new_status_events Current status event.
 *
 * \retval ::TRUE  Status event transmission required.
 * \retval ::FALSE Status event transmission not required.
 */
static uint8_t check_status_events_change(as7058_status_events_t new_status_events)
{
    const as7058_status_events_t empty_status_events = {
        .status_seq = 0,
        .status_led = 0,
        .status_asata = 0,
        .status_asatb = 0,
        .status_vcsel = 0,
        .status_vcsel_vss = 0,
        .status_vcsel_vdd = 0,
        .status_leadoff = 0,
        .status_iir = 0,
    };
    uint8_t status_events_set =
        (memcmp(&new_status_events, &empty_status_events, sizeof(as7058_status_events_t)) ? TRUE : FALSE);

    return status_events_set;
}

/*!
 * \brief Returns the size of a packet with the given number of FIFO data samples, accelerometer samples, and flags.
 *
 * \param[in] fifo_data_cnt Number of FIFO data samples.
 * \param[in] acc_data_cnt  Number of accelerometer samples.
 * \param[in] flags         Header flags, see \ref AS7058_RAW_APP_FLAGS.
 *
 * \returns the size of a packet with the given number of FIFO data samples, accelerometer samples, and flags.
 */
static uint32_t size_of_packet(uint8_t fifo_data_cnt, uint8_t acc_data_cnt, uint8_t flags)
{
    uint32_t size = AS7058_RAW_APP_HEADER_SIZE;
    size += fifo_data_cnt * AS7058_FIFO_SAMPLE_SIZE;
    size += acc_data_cnt * sizeof(vs_acc_data_t);
    size += sizeof(agc_status_t) * (flags & AS7058_FLAGS_AGC_STATUSES_NUM_MASK);
    if (flags & AS7058_FLAGS_STATUS_EVENTS_PRESENT) {
        size += sizeof(as7058_status_events_t);
    }
    if (flags & AS7058_FLAGS_EXT_EVENT_CNT_PRESENT) {
        size += sizeof(uint8_t);
    }
    return size;
}

/*!
 * \brief Returns the remaining size in a given packet, based on the maximum size of a single packet.
 *
 * This function does not take the output queue buffer size into consideration.
 *
 * \param[in] p_packet Pointer to packet structure.
 *
 * \returns the remaining size in a given packet.
 */
static uint32_t remaining_size_in_packet(const volatile as7058_raw_app_non_finalized_packet_t *p_packet)
{
    if (!p_packet) {
        return 0;
    }

    uint32_t used_size = size_of_packet(*p_packet->p_fifo_data_cnt, *p_packet->p_acc_data_cnt, *p_packet->p_flags);

    if (used_size > AS7058_RAW_APP_MAX_PACKET_SIZE) {
        /* Should never happen */
        return 0;
    } else {
        return AS7058_RAW_APP_MAX_PACKET_SIZE - used_size;
    }
}

/*!
 * \brief Creates a packet if no non-finalized packet exists.
 *
 * \retval ::ERR_SUCCESS Packet created or no creation needed.
 * \retval ::ERR_FIFO    Buffer full.
 */
static err_code_t create_packet_if_needed(void)
{
    if (g_current_packet.p_fifo_data_cnt) {
        /* Current non-finalized packet exists, no creation needed */
        return ERR_SUCCESS;
    }

    uint8_t packet_counter = g_packet_counter;
    M_CHECK_SUCCESS(FIFO_Put(&g_output_queue, &packet_counter));

    uint8_t zero = 0;

    g_current_packet.p_fifo_data_cnt = g_output_queue_buffer + g_output_queue.in;
    M_CHECK_SUCCESS(FIFO_Put(&g_output_queue, &zero));

    g_current_packet.p_acc_data_cnt = g_output_queue_buffer + g_output_queue.in;
    M_CHECK_SUCCESS(FIFO_Put(&g_output_queue, &zero));

    uint8_t flags = AS7058_FLAGS_INTERNAL_NOT_READY_FOR_OUTPUT;

    g_current_packet.p_flags = g_output_queue_buffer + g_output_queue.in;
    M_CHECK_SUCCESS(FIFO_Put(&g_output_queue, &flags));

    return ERR_SUCCESS;
}

/*!
 * \brief Adds AGC status information to the current packet.
 *
 * \param[in]  p_agc_statuses   Pointer to the array containing the current AGC statuses.
 * \param[in]  agc_statuses_num Number of items in the AGC statuses array.
 *
 * \retval ::ERR_SUCCESS  AGC status information processed successfully. (Note that this status code is also returned
 *                        when the provided AGC status information was not added to the packet.)
 * \retval ::ERR_POINTER  Invalid arguments or no non-finalized packet exists.
 * \retval ::ERR_ARGUMENT More AGC status information items provided than supported.
 * \retval ::ERR_MESSAGE  Packet already contains AGC status or other field that appears after the AGC status field or
 *                        remaining size in packet is insufficient.
 */
static err_code_t handle_agc_statuses_change(const agc_status_t *p_agc_statuses, uint8_t agc_statuses_num)
{
    M_CHECK_NULL_POINTER(p_agc_statuses);
    M_CHECK_ARGUMENT_LOWER_EQUAL(agc_statuses_num, AGC_MAX_CHANNEL_CNT);
    M_CHECK_CURRENT_PACKET_POINTERS();

    if (*g_current_packet.p_flags & (AS7058_FLAGS_AGC_STATUSES_NUM_MASK | AS7058_FLAGS_STATUS_EVENTS_PRESENT |
                                     AS7058_FLAGS_EXT_EVENT_CNT_PRESENT)) {
        /* Packet already contains AGC statuses or a field that appears after the AGC statuses field */
        return ERR_MESSAGE;
    }

    if (remaining_size_in_packet(&g_current_packet) < sizeof(agc_status_t) * agc_statuses_num) {
        /* Remaining size in packet is insufficient to store AGC statuses */
        return ERR_MESSAGE;
    }

    /* AGC statuses are added to a global buffer first to detect future changes. */
    memcpy(&g_last_agc_statuses, p_agc_statuses, sizeof(agc_status_t) * agc_statuses_num);
    g_agc_statuses_num = agc_statuses_num;
    *g_current_packet.p_flags |= agc_statuses_num & AS7058_FLAGS_AGC_STATUSES_NUM_MASK;

    return ERR_SUCCESS;
}

/*!
 * \brief Adds status event information to the current packet.
 *
 * \param[in]  status_events Status event information to add.
 * \param[out] p_added       ::TRUE when status event was added to the current packet, ::FALSE otherwise.
 *
 * \retval ::ERR_SUCCESS Status event information processed successfully. (Note that this status code is also returned
 *                       when the provided status event information was not added to the packet.)
 * \retval ::ERR_POINTER Invalid arguments or no non-finalized packet exists.
 * \retval ::ERR_MESSAGE Packet already contains status event or other field that appears after the status event field.
 */
static err_code_t handle_status_events_change(as7058_status_events_t status_events, uint8_t *p_added)
{
    M_CHECK_NULL_POINTER(p_added);
    M_CHECK_CURRENT_PACKET_POINTERS();

    if (*g_current_packet.p_flags & (AS7058_FLAGS_STATUS_EVENTS_PRESENT | AS7058_FLAGS_EXT_EVENT_CNT_PRESENT)) {
        /* Packet already contains status event or other field that appears after the status event field. */
        return ERR_MESSAGE;
    }

    if (remaining_size_in_packet(&g_current_packet) < sizeof(status_events)) {
        /* Remaining size in packet is insufficient to store status event */
        *p_added = FALSE;
        return ERR_SUCCESS;
    }

    /* Status event is added directly to the output buffer, as packets containing this field are finalized afterwards */
    M_CHECK_SUCCESS(FIFO_PutMultiple(&g_output_queue, &status_events, sizeof(status_events)));
    *g_current_packet.p_flags |= AS7058_FLAGS_STATUS_EVENTS_PRESENT;

    *p_added = TRUE;
    return ERR_SUCCESS;
}

/*!
 * \brief Adds the external event occurrence counter to the current packet.
 *
 * \param[in]  ext_event_cnt Number of occurred external events.
 * \param[out] p_added       ::TRUE when the flag was set in the current packet, ::FALSE otherwise.
 *
 * \retval ::ERR_SUCCESS External event processed successfully. (Note that this status code is also returned when the
 *                       flag was not set in the packet.)
 * \retval ::ERR_POINTER Invalid arguments or no non-finalized packet exists.
 * \retval ::ERR_MESSAGE Packet already contains external event occurrence counter.
 */
static err_code_t handle_ext_event_cnt(uint8_t ext_event_cnt, uint8_t *p_added)
{
    M_CHECK_NULL_POINTER(p_added);
    M_CHECK_CURRENT_PACKET_POINTERS();

    if (*g_current_packet.p_flags & AS7058_FLAGS_EXT_EVENT_CNT_PRESENT) {
        /* Packet already contains external event occurrence counter */
        return ERR_MESSAGE;
    }

    if (remaining_size_in_packet(&g_current_packet) < sizeof(uint8_t)) {
        /* Remaining size in packet is insufficient to store external event occurrence counter */
        *p_added = FALSE;
        return ERR_SUCCESS;
    }

    /* Count is added directly to the output buffer, as packets containing this field are finalized afterwards */
    M_CHECK_SUCCESS(FIFO_Put(&g_output_queue, &ext_event_cnt));
    *g_current_packet.p_flags |= AS7058_FLAGS_EXT_EVENT_CNT_PRESENT;

    *p_added = TRUE;
    return ERR_SUCCESS;
}

/*!
 * \brief Adds FIFO data to the current packet.
 *
 * \param[in]  p_fifo_data    Pointer to the FIFO data to add.
 * \param[in]  fifo_data_size Size of the FIFO data to add.
 * \param[out] p_added_size   Number of bytes of FIFO data that were added to the packet.
 *
 * \retval ::ERR_SUCCESS FIFO data processed successfully. (Note that this status code is also returned when none or not
 *                       all of the provided FIFO data was added to the packet.)
 * \retval ::ERR_POINTER Invalid arguments or no non-finalized packet exists.
 * \retval ::ERR_FIFO    Failed to insert data in output queue.
 */
static err_code_t handle_fifo_data(const uint8_t *p_fifo_data, uint16_t fifo_data_size, uint16_t *p_added_size)
{
    M_CHECK_NULL_POINTER(p_fifo_data);
    M_CHECK_NULL_POINTER(p_added_size);
    M_CHECK_CURRENT_PACKET_POINTERS();

    if (*g_current_packet.p_flags &
        ~(AS7058_FLAGS_INTERNAL_NOT_READY_FOR_OUTPUT | AS7058_FLAGS_AGC_STATUSES_NUM_MASK)) {
        /* Any flag other than ::AS7058_FLAGS_INTERNAL_NOT_READY_FOR_OUTPUT or ::AS7058_FLAGS_AGC_STATUSES_NUM_MASK
         * indicate the presence of data which follows after FIFO data in the output structure when set. As a result, no
         * FIFO data can be added to the packet. (::AS7058_FLAGS_AGC_STATUSES_NUM_MASK can be set as the flag is set
         * before the AGC statuses are actually copied to the packet.) */
        return ERR_MESSAGE;
    }

    /* The entire remaining size of the current packet can be used for FIFO data as long as the FIFO data counter in the
     * header doesn't overflow */
    uint16_t input_cnt = fifo_data_size / AS7058_FIFO_SAMPLE_SIZE;
    uint32_t remaining_cnt_packet = remaining_size_in_packet(&g_current_packet) / AS7058_FIFO_SAMPLE_SIZE;
    uint32_t remaining_cnt_header = UINT8_MAX - *g_current_packet.p_fifo_data_cnt;
    uint32_t add_cnt = M_MIN(input_cnt, remaining_cnt_packet);
    add_cnt = M_MIN(add_cnt, remaining_cnt_header);
    uint32_t add_size = add_cnt * AS7058_FIFO_SAMPLE_SIZE;

    /* FIFO data can be copied directly to output buffer since this data appears first in the packet (after header) */
    M_CHECK_SUCCESS(FIFO_PutMultiple(&g_output_queue, p_fifo_data, add_size));

    /* Update count in packet header */
    *g_current_packet.p_fifo_data_cnt += add_cnt;

    *p_added_size = add_size;
    return ERR_SUCCESS;
}

/*!
 * \brief Adds accelerometer data to the current packet.
 *
 * \param[in]  p_acc_data     Pointer to the accelerometer data to add.
 * \param[in]  acc_data_cnt   Number of samples in the accelerometer data.
 * \param[out] p_added_cnt    Number of accelerometer data samples that were added to the packet.
 *
 * \retval ::ERR_SUCCESS Accelerometer data processed successfully. (Note that this status code is also returned when
 *                       none or not all of the provided accelerometer data was added to the packet.)
 * \retval ::ERR_POINTER Invalid arguments or no non-finalized packet exists.
 */
static err_code_t handle_acc_data(const vs_acc_data_t *p_acc_data, uint16_t acc_data_cnt, uint16_t *p_added_cnt)
{
    M_CHECK_NULL_POINTER(p_acc_data);
    M_CHECK_NULL_POINTER(p_added_cnt);
    M_CHECK_CURRENT_PACKET_POINTERS();

    if (*g_current_packet.p_flags & AS7058_FLAGS_INTERNAL_ACC_DATA_COPIED) {
        /* Accelerometer data has already been copied to the output buffer, i.e. it has been finalized */
        return ERR_MESSAGE;
    }

    if (*g_current_packet.p_acc_data_cnt > AS7058_RAW_APP_MAX_ACC_SAMPLES_PER_PACKET) {
        /* Accelerometer data buffer already contains more data than it can hold; should never happen */
        return ERR_OVERFLOW;
    }

    /* The maximum number of accelerometer samples that can be stored in the current packet is limited by the remaining
     * packet size and by the remaining space in the separate accelerometer buffer */
    uint32_t remaining_cnt_acc_buffer = AS7058_RAW_APP_MAX_ACC_SAMPLES_PER_PACKET - *g_current_packet.p_acc_data_cnt;
    uint32_t remaining_cnt_packet = remaining_size_in_packet(&g_current_packet) / sizeof(vs_acc_data_t);
    uint32_t add_cnt = M_MIN(acc_data_cnt, remaining_cnt_acc_buffer);
    add_cnt = M_MIN(add_cnt, remaining_cnt_packet);

    /* Accelerometer samples are stored in separate buffer, which will be copied to output buffer later during packet
     * finalization */
    memcpy((void *)&g_current_packet.acc_data_buffer[*g_current_packet.p_acc_data_cnt], p_acc_data,
           add_cnt * sizeof(vs_acc_data_t));

    /* Update count in packet header */
    *g_current_packet.p_acc_data_cnt += add_cnt;

    *p_added_cnt = add_cnt;
    return ERR_SUCCESS;
}

/*!
 * \brief Inserts accelerometer data from the separate buffer in the output buffer.
 *
 * Note that no more FIFO or accelerometer data can be added to the current packet after calling this function.
 *
 * \retval ::ERR_SUCCESS Accelerometer data copied successfully.
 * \retval ::ERR_MESSAGE Accelerometer data has already been copied to output buffer.
 * \retval ::ERR_POINTER No non-finalized packet exists.
 * \retval ::ERR_FIFO    Failed to insert data in output queue.
 */
static err_code_t copy_acc_data()
{
    M_CHECK_CURRENT_PACKET_POINTERS();

    if (*g_current_packet.p_flags & AS7058_FLAGS_INTERNAL_ACC_DATA_COPIED) {
        /* Accelerometer data has already been copied to output buffer */
        return ERR_MESSAGE;
    }

    uint32_t acc_data_size = *g_current_packet.p_acc_data_cnt * sizeof(vs_acc_data_t);
    M_CHECK_SUCCESS(FIFO_PutMultiple(&g_output_queue, (void *)g_current_packet.acc_data_buffer, acc_data_size));

    *g_current_packet.p_flags |= AS7058_FLAGS_INTERNAL_ACC_DATA_COPIED;
    return ERR_SUCCESS;
}

/*!
 * \brief Inserts AGC data from the separate buffer in the output buffer.
 *
 * Note that no more FIFO, accelerometer or AGC data can be added to the current packet after calling this function.
 *
 * \retval ::ERR_SUCCESS AGC data copied successfully or nothing needs to be copied.
 * \retval ::ERR_MESSAGE AGC data has already been copied to output buffer.
 * \retval ::ERR_POINTER No non-finalized packet exists.
 * \retval ::ERR_FIFO    Failed to insert data in output queue.
 */
static err_code_t copy_agc_data()
{
    M_CHECK_CURRENT_PACKET_POINTERS();

    if ((*g_current_packet.p_flags & AS7058_FLAGS_AGC_STATUSES_NUM_MASK) == 0) {
        /* Nothing to copy - Jump out of this function */
        return ERR_SUCCESS;
    }

    if (*g_current_packet.p_flags & (AS7058_FLAGS_STATUS_EVENTS_PRESENT | AS7058_FLAGS_EXT_EVENT_CNT_PRESENT)) {
        /* Packet already contains a field that appears after the AGC statuses field */
        return ERR_MESSAGE;
    }

    /* Copy AGC statuses directly to the output buffer */
    M_CHECK_ARGUMENT_LOWER_EQUAL(g_agc_statuses_num, AGC_MAX_CHANNEL_CNT);
    M_CHECK_SUCCESS(FIFO_PutMultiple(&g_output_queue, g_last_agc_statuses, sizeof(agc_status_t) * g_agc_statuses_num));

    return ERR_SUCCESS;
}

/*!
 * \brief Finalizes the current packet for output.
 *
 * \retval ::ERR_SUCCESS Packet finalized successfully.
 * \retval ::ERR_POINTER No non-finalized packet exists.
 * \retval ::ERR_FIFO    Failed to insert data in output queue.
 */
static err_code_t finalize_packet(void)
{
    M_CHECK_CURRENT_PACKET_POINTERS();

    volatile uint8_t *p_flags = g_current_packet.p_flags;

    /* p_fifo_data_cnt is cleared last because this serves as indicator whether a non-finalized packet exists */
    g_current_packet.p_flags = NULL;
    g_current_packet.p_acc_data_cnt = NULL;
    g_current_packet.p_fifo_data_cnt = NULL;

    /* Packet is now ready for output, clear internal flags */
    *p_flags &= ~(AS7058_FLAGS_INTERNAL_NOT_READY_FOR_OUTPUT | AS7058_FLAGS_INTERNAL_ACC_DATA_COPIED);

    g_packet_counter++;

    return ERR_SUCCESS;
}

/*!
 * \brief Gets the oldest packet from the output queue.
 *
 * \param[out]   p_dest Pointer to the buffer where packet shall be copied to. If this parameter is NULL, the function
 *                      only checks whether a packet is available for output.
 * \param[inout] p_size Pointer to the maximum size of the destination buffer. Will be updated with the actual size of
 *                      the packet after copying. Can be NULL if p_dest is NULL.
 *
 * \retval ::ERR_SUCCESS  Packet exists for output and has been copied to destination buffer, if p_dest is not NULL.
 * \retval ::ERR_NO_DATA  No packet exists for output.
 * \retval ::ERR_POINTER  Non-NULL destination buffer pointer provided, but p_size is NULL.
 * \retval ::ERR_ARGUMENT Destination buffer is too small.
 * \retval ::ERR_FIFO     Failed to get data from the output queue.
 */
static err_code_t get_packet_from_output_queue(void *p_dest, uint16_t *p_size)
{
    uint32_t item_cnt;
    M_CHECK_SUCCESS(FIFO_GetItemCount(&g_output_queue, &item_cnt));
    if (item_cnt < AS7058_RAW_APP_HEADER_SIZE) {
        return ERR_NO_DATA;
    }

    uint8_t flags =
        g_output_queue_buffer[(g_output_queue.out + AS7058_RAW_APP_FIELD_OFFSET_FLAGS) % g_output_queue.capacity];
    if (flags & AS7058_FLAGS_INTERNAL_NOT_READY_FOR_OUTPUT) {
        return ERR_NO_DATA;
    }

    uint8_t fifo_data_cnt = g_output_queue_buffer[(g_output_queue.out + AS7058_RAW_APP_FIELD_OFFSET_FIFO_DATA_CNT) %
                                                  g_output_queue.capacity];
    uint8_t acc_data_cnt = g_output_queue_buffer[(g_output_queue.out + AS7058_RAW_APP_FIELD_OFFSET_ACC_DATA_CNT) %
                                                 g_output_queue.capacity];
    uint32_t packet_size = size_of_packet(fifo_data_cnt, acc_data_cnt, flags);
    if (item_cnt < packet_size) {
        /* Packets with the AS7058_FLAGS_INTERNAL_NOT_READY_FOR_OUTPUT flag cleared are supposed to be complete, so
         * this should never happen */
        return ERR_NO_DATA;
    }

    if (p_dest) {
        M_CHECK_NULL_POINTER(p_size);

        if (*p_size < packet_size) {
            return ERR_ARGUMENT;
        }

        M_CHECK_SUCCESS(FIFO_GetMultiple(&g_output_queue, p_dest, packet_size));

        *p_size = packet_size;
    }

    return ERR_SUCCESS;
}

/*!
 * \brief Returns the number of bits set in the input.
 */
static uint8_t count_bits(uint32_t input)
{
    /* Source: https://graphics.stanford.edu/~seander/bithacks.html#CountBitsSetKernighan */
    uint32_t count;
    for (count = 0; input; count++) {
        input &= input - 1;
    }
    return count;
}

static err_code_t calculate_average_sample_period_us(uint32_t ppg_sample_period_us, uint32_t ecg_seq1_sample_period_us,
                                                     uint32_t ecg_seq2_sample_period_us, uint32_t fifo_map,
                                                     uint32_t *p_result)
{
    uint32_t enabled_sub_samples_num_ppg = count_bits(fifo_map & AS7058_SUB_SAMPLE_FLAG_ALL_PPG);
    uint32_t enabled_sub_samples_num_ecg_seq1 = count_bits(fifo_map & AS7058_SUB_SAMPLE_FLAG_ALL_ECG_SEQ1);
    uint32_t enabled_sub_samples_num_ecg_seq2 = count_bits(fifo_map & AS7058_SUB_SAMPLE_FLAG_ALL_ECG_SEQ2);

    /* Calculate average time between two samples via the following formula:
     * avg_sample_period_us = 1 / ((1 / ppg_sample_period_us) * enabled_sub_samples_num_ppg + (1 /
     * ecg_seq1_sample_period_us) * enabled_sub_samples_num_ecg_seq1 + (1 / ecg_seq2_sample_period_us) *
     * enabled_sub_samples_num_ecg_seq2)*/

    /* At least one sub-sample needs to be enabled */
    if (0 == enabled_sub_samples_num_ppg && 0 == enabled_sub_samples_num_ecg_seq1 &&
        0 == enabled_sub_samples_num_ecg_seq2) {
        return ERR_ARGUMENT;
    }

    /* For each sequencer with enabled sub-samples, the sample period needs to be non-zero; if a sequencer has no
     * enabled sub-samples, the sample period can be set to a random non-zero value since it has no effect on the final
     * result */
    if (0 == ppg_sample_period_us) {
        if (enabled_sub_samples_num_ppg > 0) {
            return ERR_ARGUMENT;
        } else {
            ppg_sample_period_us = 1;
        }
    }
    if (0 == ecg_seq1_sample_period_us) {
        if (enabled_sub_samples_num_ecg_seq1 > 0) {
            return ERR_ARGUMENT;
        } else {
            ecg_seq1_sample_period_us = 1;
        }
    }
    if (0 == ecg_seq2_sample_period_us) {
        if (enabled_sub_samples_num_ecg_seq2 > 0) {
            return ERR_ARGUMENT;
        } else {
            ecg_seq2_sample_period_us = 1;
        }
    }

    /* Calculate using simplified formula, see
     * https://www.wolframalpha.com/input?i=simplify+1%2F%28n%2Fa%2Bm%2Fb%2Bo%2Fc%29 */
    uint32_t avg_sample_period_us =
        ((uint64_t)ppg_sample_period_us * ecg_seq1_sample_period_us * ecg_seq2_sample_period_us) /
        ((uint64_t)ppg_sample_period_us * ecg_seq1_sample_period_us * enabled_sub_samples_num_ecg_seq2 +
         (uint64_t)ppg_sample_period_us * ecg_seq2_sample_period_us * enabled_sub_samples_num_ecg_seq1 +
         (uint64_t)ecg_seq1_sample_period_us * ecg_seq2_sample_period_us * enabled_sub_samples_num_ppg);

    if (0 == avg_sample_period_us) {
        /* Set sample period to 1 us if it less than 1 us */
        avg_sample_period_us = 1;
    }

    *p_result = avg_sample_period_us;

    return ERR_SUCCESS;
}

static err_code_t set_sample_period(uint32_t ppg_sample_period_us, uint32_t ecg_seq1_sample_period_us,
                                    uint32_t ecg_seq2_sample_period_us, uint32_t fifo_map)
{
    uint32_t sample_period_us;
    M_CHECK_SUCCESS(calculate_average_sample_period_us(ppg_sample_period_us, ecg_seq1_sample_period_us,
                                                       ecg_seq2_sample_period_us, fifo_map, &sample_period_us));

    if (0 == sample_period_us) {
        return ERR_ARGUMENT;
    }

    uint32_t sample_freq_hz = (1000 * 1000) / sample_period_us;
    if (sample_freq_hz > 0) {
        if (sample_freq_hz > UINT8_MAX) {
            /* Sample period is very high, no threshold needed as maximum packet size is reached within less than a
             * second */
            g_fifo_data_cnt_threshold = UINT8_MAX;
        } else {
            g_fifo_data_cnt_threshold = sample_freq_hz;
        }
    } else {
        /* Output separate packet for each sample when sample rate is below 1 Hz */
        g_fifo_data_cnt_threshold = 1;
    }

    return ERR_SUCCESS;
}

/******************************************************************************
 *                             GLOBAL FUNCTIONS                               *
 ******************************************************************************/

err_code_t as7058_raw_app_initialize(void)
{
    M_CHECK_SUCCESS(FIFO_Reset(&g_output_queue));
    g_fifo_data_cnt_threshold = UINT8_MAX;
    g_include_acc_data = FALSE;
    g_agc_statuses_num = AS7058_RAW_APP_AGC_STATUSES_NUM_UNKNOWN;
    g_current_packet.p_fifo_data_cnt = NULL;
    g_current_packet.p_acc_data_cnt = NULL;
    g_current_packet.p_flags = NULL;
    g_packet_counter = 0;

    g_state = AS7058_RAW_APP_STATE_CONFIGURATION;

    return ERR_SUCCESS;
}

err_code_t as7058_raw_app_configure(const void *p_config, uint8_t size)
{
    M_CHECK_STATE(AS7058_RAW_APP_STATE_CONFIGURATION);

    M_CHECK_NULL_POINTER(p_config);
    M_CHECK_SIZE(size, sizeof(as7058_raw_app_configuration_t));

    const as7058_raw_app_configuration_t *p_app_config = (const as7058_raw_app_configuration_t *)p_config;

    if (p_app_config->include_acc) {
        g_include_acc_data = TRUE;
    } else {
        g_include_acc_data = FALSE;
    }

    return ERR_SUCCESS;
}

err_code_t as7058_raw_app_start(uint32_t ppg_sample_period_us, uint32_t ecg_seq1_sample_period_us,
                                uint32_t ecg_seq2_sample_period_us, uint32_t fifo_map)
{
    M_CHECK_STATE(AS7058_RAW_APP_STATE_CONFIGURATION);

    M_CHECK_SUCCESS(
        set_sample_period(ppg_sample_period_us, ecg_seq1_sample_period_us, ecg_seq2_sample_period_us, fifo_map));

    M_CHECK_SUCCESS(FIFO_Reset(&g_output_queue));
    g_agc_statuses_num = AS7058_RAW_APP_AGC_STATUSES_NUM_UNKNOWN;
    g_current_packet.p_fifo_data_cnt = NULL;
    g_current_packet.p_acc_data_cnt = NULL;
    g_current_packet.p_flags = NULL;
    g_packet_counter = 0;

    g_state = AS7058_RAW_APP_STATE_PROCESSING;

    return ERR_SUCCESS;
}

err_code_t as7058_raw_app_set_input(const uint8_t *p_fifo_data, uint16_t fifo_data_size,
                                    as7058_status_events_t status_events, const agc_status_t *p_agc_statuses,
                                    uint8_t agc_statuses_num, const vs_acc_data_t *p_acc_data, uint8_t acc_data_cnt,
                                    uint8_t ext_event_cnt, bio_execution_status_t *p_result)
{
    M_CHECK_STATE(AS7058_RAW_APP_STATE_PROCESSING);

    if (fifo_data_size > 0) {
        M_CHECK_NULL_POINTER(p_fifo_data);
    }
    if (acc_data_cnt > 0) {
        M_CHECK_NULL_POINTER(p_acc_data);
    }
    M_CHECK_NULL_POINTER(p_result);

    const uint8_t *p_fifo_data_current = p_fifo_data;
    const vs_acc_data_t *p_acc_data_current = p_acc_data;

    if (!g_include_acc_data) {
        /* Prevent handling of accelerometer data by overwriting the sample count */
        acc_data_cnt = 0;
    }

    uint8_t agc_statuses_in_packet =
        g_current_packet.p_flags ? (*g_current_packet.p_flags & AS7058_FLAGS_AGC_STATUSES_NUM_MASK) : FALSE;
    uint8_t fifo_data_in_packet = g_current_packet.p_fifo_data_cnt ? (0 != *g_current_packet.p_fifo_data_cnt) : FALSE;
    uint8_t agc_statuses_pending =
        check_agc_statuses_change(p_agc_statuses, agc_statuses_num, g_last_agc_statuses, g_agc_statuses_num);
    uint8_t finalize_existing_packet = agc_statuses_pending && (agc_statuses_in_packet || fifo_data_in_packet);
    uint8_t status_events_pending = check_status_events_change(status_events);
    uint8_t ext_event_cnt_pending = ext_event_cnt > 0;
#define M_FIFO_DATA_PENDING() (fifo_data_size - (p_fifo_data_current - p_fifo_data))
#define M_ACC_DATA_PENDING() (acc_data_cnt - (p_acc_data_current - p_acc_data))

    while (M_FIFO_DATA_PENDING() || M_ACC_DATA_PENDING() || agc_statuses_pending || status_events_pending ||
           ext_event_cnt_pending) {
        M_CHECK_SUCCESS(create_packet_if_needed());

        if (!finalize_existing_packet) {
            if (agc_statuses_pending) {
                M_CHECK_SUCCESS(handle_agc_statuses_change(p_agc_statuses, agc_statuses_num));
                agc_statuses_pending = FALSE;
            }

            if (M_FIFO_DATA_PENDING()) {
                uint16_t fifo_data_added_size = 0;
                M_CHECK_SUCCESS(handle_fifo_data(p_fifo_data_current, M_FIFO_DATA_PENDING(), &fifo_data_added_size));
                p_fifo_data_current += fifo_data_added_size;
            }

            if (M_ACC_DATA_PENDING()) {
                uint16_t acc_data_added_cnt = 0;
                M_CHECK_SUCCESS(handle_acc_data(p_acc_data_current, M_ACC_DATA_PENDING(), &acc_data_added_cnt));
                p_acc_data_current += acc_data_added_cnt;
            }
        }

        if (M_FIFO_DATA_PENDING() || M_ACC_DATA_PENDING() || finalize_existing_packet || status_events_pending ||
            ext_event_cnt_pending || *g_current_packet.p_fifo_data_cnt >= g_fifo_data_cnt_threshold ||
            AS7058_RAW_APP_MAX_PACKET_SIZE == size_of_packet(*g_current_packet.p_fifo_data_cnt,
                                                             *g_current_packet.p_acc_data_cnt,
                                                             *g_current_packet.p_flags)) {
            M_CHECK_SUCCESS(copy_acc_data());

            M_CHECK_SUCCESS(copy_agc_data());

            uint8_t status_events_added = FALSE;
            if (status_events_pending) {
                M_CHECK_SUCCESS(handle_status_events_change(status_events, &status_events_added));
                if (status_events_added) {
                    status_events_pending = FALSE;
                }
            }

            uint8_t ext_event_cnt_added = FALSE;
            if (ext_event_cnt_pending) {
                M_CHECK_SUCCESS(handle_ext_event_cnt(ext_event_cnt, &ext_event_cnt_added));
                if (ext_event_cnt_added) {
                    ext_event_cnt_pending = FALSE;
                }
            }

            finalize_existing_packet = FALSE;

            M_CHECK_SUCCESS(finalize_packet());
        }
    }
#undef M_FIFO_DATA_PENDING
#undef M_ACC_DATA_PENDING

    if (ERR_SUCCESS == get_packet_from_output_queue(NULL, NULL)) {
        *p_result = BIO_EXECUTION_STATUS_EXECUTABLE;
    } else {
        *p_result = BIO_EXECUTION_STATUS_NOT_EXECUTABLE;
    }

    return ERR_SUCCESS;
}

err_code_t as7058_raw_app_execute(bio_output_status_t *p_result)
{
    M_CHECK_STATE(AS7058_RAW_APP_STATE_PROCESSING);

    M_CHECK_NULL_POINTER(p_result);

    if (ERR_SUCCESS == get_packet_from_output_queue(NULL, NULL)) {
        *p_result = BIO_OUTPUT_STATUS_DATA_AVAILABLE;
    } else {
        *p_result = BIO_OUTPUT_STATUS_DATA_UNAVAILABLE;
    }

    return ERR_SUCCESS;
}

err_code_t as7058_raw_app_get_output(void *p_dest, uint16_t *p_size)
{
    M_CHECK_STATE(AS7058_RAW_APP_STATE_PROCESSING);

    M_CHECK_NULL_POINTER(p_dest);
    M_CHECK_NULL_POINTER(p_size);

    return get_packet_from_output_queue(p_dest, p_size);
}

err_code_t as7058_raw_app_stop(void)
{
    if (AS7058_RAW_APP_STATE_UNINITIALIZED == g_state) {
        return ERR_PERMISSION;
    }

    g_state = AS7058_RAW_APP_STATE_CONFIGURATION;

    return ERR_SUCCESS;
}

err_code_t as7058_raw_app_shutdown(void)
{
    g_state = AS7058_RAW_APP_STATE_UNINITIALIZED;

    return ERR_SUCCESS;
}

#if AGC_MAX_CHANNEL_CNT > 15
#error Maximum number of AGC channels supported by output format is 15.
#endif
