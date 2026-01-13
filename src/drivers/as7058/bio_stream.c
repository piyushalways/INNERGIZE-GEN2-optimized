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

#include "bio_stream.h"

#include "bio_stream_version.h"
#include "error_codes.h"
#include "fifo.h"
#include "std_inc.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

/*!
 * Causes the function where this macro is used to return with ::ERR_PERMISSION if the app is in an unexpected
 * state.
 */
#define M_CHECK_STATE(expected)                                                                                        \
    do {                                                                                                               \
        if (g_state != (expected)) {                                                                                   \
            return ERR_PERMISSION;                                                                                     \
        }                                                                                                              \
    } while (0)

/*!
 * Causes the function where this macro is used to return with ::ERR_PERMISSION if the app is in an unexpected
 * state.
 */
#define M_CHECK_STATE_NOT(not_expected)                                                                                \
    do {                                                                                                               \
        if ((not_expected) == g_state) {                                                                               \
            return ERR_PERMISSION;                                                                                     \
        }                                                                                                              \
    } while (0)

/*! Maximum payload size of a single item without fragmentation. */
#define MAX_ITEM_PAYLOAD_SIZE()                                                                                        \
    (M_MIN(BIO_STREAM_ITEM_HEADER_SIZE_MASK, g_config.max_packet_size - BIO_STREAM_ITEM_HEADER_SIZE))

/*! States of the app. */
enum bio_stream_state {
    BIO_STREAM_STATE_UNINITIALIZED = 0, /*!< App is uninitialized. */
    BIO_STREAM_STATE_CONFIGURATION,     /*!< App is in configuration state. */
    BIO_STREAM_STATE_PROCESSING,        /*!< App is in processing state. */
};

#define MAX_ID 63 /*!< Maximum allowed item ID. */

#define DEFAULT_ITEM_FILTER UINT64_MAX /*!< Default value for the item ID filter. */
#define DEFAULT_MAX_PACKET_SIZE 150 /*!< Default value for maximum package size. */
#define DEFAULT_RESERVED_DATA 0 /*!< Default value for reserved data. */

#ifndef BIO_STREAM_OUTPUT_QUEUE_SIZE
#define BIO_STREAM_OUTPUT_QUEUE_SIZE 2999 /*!< Size of the output queue. */
#endif

#ifndef BIO_STREAM_TEMP_BUFFER_SIZE
#define BIO_STREAM_TEMP_BUFFER_SIZE 200 /*!< Maximum payload size of one item. */
#endif

/******************************************************************************
 *                                  GLOBALS                                   *
 ******************************************************************************/

/*! Current state of the app. */
static volatile enum bio_stream_state g_state = BIO_STREAM_STATE_UNINITIALIZED;

/*! Current app configuration. */
static bio_stream_configuration_t g_config;

/*! Buffer used by the output queue. */
static volatile uint8_t g_output_queue_buffer[BIO_STREAM_OUTPUT_QUEUE_SIZE + 1];

/*! Number of finalized output packets. It is expected to overflow. */
static uint8_t g_packet_counter;

/*! Configuration of the output queue. */
static volatile fifo_t g_output_queue = {
    .itemsize = sizeof(g_output_queue_buffer[0]),
    .capacity = BIO_STREAM_OUTPUT_QUEUE_SIZE + 1,
    .in = 0,
    .out = 0,
    .data = (void *)g_output_queue_buffer,
};

/*! Temporary buffer to save the data of the last item so that data with the same ID can be appended. */
static volatile struct {
    uint8_t buffer[BIO_STREAM_TEMP_BUFFER_SIZE];
    uint8_t id;
    uint16_t fill_size;
    uint16_t maximum_size;
} g_temp_data;

/*!
 * Identifies at which queue `in` index the package shall be force-closed. UINT32_MAX means that no force-closing
 * should be performed.
 */
static volatile uint32_t g_close_package_queue_in;

/******************************************************************************
 *                               LOCAL FUNCTIONS                              *
 ******************************************************************************/

err_code_t create_header_bytes(bio_stream_header_t structure, uint8_t bytes[BIO_STREAM_ITEM_HEADER_SIZE])
{
    uint16_t data;

    if ((structure.id & ~BIO_STREAM_ITEM_HEADER_ID_MASK) ||
        (structure.fragmentation & ~BIO_STREAM_ITEM_HEADER_FRAG_MASK) ||
        (structure.size & ~BIO_STREAM_ITEM_HEADER_SIZE_MASK)) {
        return ERR_ARGUMENT;
    }

    data = (structure.id << BIO_STREAM_ITEM_HEADER_ID_SHIFT) |
           (structure.fragmentation << BIO_STREAM_ITEM_HEADER_FRAG_SHIFT) |
           (structure.size << BIO_STREAM_ITEM_HEADER_SIZE_SHIFT);

    bytes[0] = data & 0xFF;
    bytes[1] = (data >> 8) & 0xFF;

    return ERR_SUCCESS;
}

static uint32_t get_item_aligned_queue_size(uint32_t size)
{
    uint8_t header_bytes[BIO_STREAM_ITEM_HEADER_SIZE];
    bio_stream_header_t header;
    uint32_t item_aligned_size = 0;
    uint32_t read_index;

    while (item_aligned_size < size) {
        /* TODO: This is a very bad workaround to get the sizes because it reads the internal FIFO buffer directly.
         * A better approach would be to add a FIFO_PeekMultiple function inside the FIFO module. */

        read_index = g_output_queue.out + item_aligned_size;
        if (read_index >= g_output_queue.capacity) {
            read_index -= g_output_queue.capacity;
        }
        header_bytes[0] = g_output_queue_buffer[read_index];

        if (read_index == g_close_package_queue_in) {
            g_close_package_queue_in = UINT32_MAX;
            if (item_aligned_size) {
                break;
            }
        }

        /* Read the second byte */
        read_index++;
        if (read_index >= g_output_queue.capacity) {
            read_index -= g_output_queue.capacity;
        }
        header_bytes[1] = g_output_queue_buffer[read_index];

        header = bio_stream_extract_header_bytes(header_bytes);

        if (item_aligned_size + header.size + sizeof(header_bytes) > size) {
            break;
        } else {
            item_aligned_size += header.size + sizeof(header_bytes);
        }
    }

    return item_aligned_size;
}

static err_code_t add_item_to_queue(uint8_t id, volatile const void *p_data, uint16_t size,
                                    uint8_t external_fragmentation)
{
    bio_stream_header_t header = {.id = id, .fragmentation = FALSE, .size = 0};
    uint16_t sent_size = 0;
    uint32_t free_count;

    /* Calculate needed FIFO size and check whether it can be put into the FIFO. */
    uint16_t number_of_items = (size + MAX_ITEM_PAYLOAD_SIZE() - 1) / MAX_ITEM_PAYLOAD_SIZE();
    uint16_t item_size = size + (number_of_items * BIO_STREAM_ITEM_HEADER_SIZE);
    M_CHECK_SUCCESS(FIFO_GetFreeCount(&g_output_queue, &free_count));
    if (free_count < item_size) {
        return ERR_FIFO;
    }

    while (0 < size) {
        uint8_t header_bytes[BIO_STREAM_ITEM_HEADER_SIZE];
        header.size = M_MIN(MAX_ITEM_PAYLOAD_SIZE(), size);
        header.fragmentation =
            ((header.size == MAX_ITEM_PAYLOAD_SIZE()) && (size > header.size)) || !!external_fragmentation;
        M_CHECK_SUCCESS(create_header_bytes(header, header_bytes));
        M_CHECK_SUCCESS(FIFO_PutMultiple(&g_output_queue, header_bytes, sizeof(header_bytes)));
        M_CHECK_SUCCESS(FIFO_PutMultiple(&g_output_queue, ((const uint8_t *)p_data) + sent_size, header.size));
        size -= header.size;
        sent_size += header.size;
    }

    return ERR_SUCCESS;
}

static err_code_t get_available_output_data_size(uint16_t *p_available_output_data_size)
{
    uint32_t queue_size;

    M_CHECK_SUCCESS(FIFO_GetItemCount(&g_output_queue, &queue_size));

    if (0 == queue_size) {
        return ERR_NO_DATA;
    } else if ((BIO_STREAM_STATE_PROCESSING == g_state) && (UINT32_MAX == g_close_package_queue_in) &&
               (g_config.max_packet_size >
                (queue_size + g_temp_data.fill_size))) { /* Size of packet counter has been subtracted from
                                                            g_config.max_packet_size in bio_stream_configure */
        return ERR_NO_DATA;
    }

    if (UINT16_MAX < queue_size) {
        return ERR_SIZE;
    }

    if (p_available_output_data_size) {
        *p_available_output_data_size = (uint16_t)queue_size;
    }

    return ERR_SUCCESS;
}

static err_code_t get_items_from_queue(uint8_t *p_dest, uint16_t *p_size)
{
    uint16_t available_output_data_size;

    M_CHECK_SUCCESS(get_available_output_data_size(&available_output_data_size));

    /* Size of packet counter has been subtracted from g_config.max_packet_size in bio_stream_configure */
    available_output_data_size =
        get_item_aligned_queue_size(M_MIN(available_output_data_size, g_config.max_packet_size));

    if (available_output_data_size + sizeof(g_packet_counter) > *p_size) {
        return ERR_SIZE;
    }

    M_CHECK_SUCCESS(
        FIFO_GetMultiple(&g_output_queue, p_dest + sizeof(g_packet_counter), (uint32_t)available_output_data_size));
    *p_size = available_output_data_size + sizeof(g_packet_counter);
    p_dest[0] = g_packet_counter++;

    return ERR_SUCCESS;
}

/******************************************************************************
 *                              GLOBAL FUNCTIONS                              *
 ******************************************************************************/

bio_stream_header_t bio_stream_extract_header_bytes(const uint8_t bytes[BIO_STREAM_ITEM_HEADER_SIZE])
{
    bio_stream_header_t header;
    uint16_t data = bytes[0] | (bytes[1] << 8);

    header.id = (data >> BIO_STREAM_ITEM_HEADER_ID_SHIFT) & BIO_STREAM_ITEM_HEADER_ID_MASK;
    header.fragmentation = (data >> BIO_STREAM_ITEM_HEADER_FRAG_SHIFT) & BIO_STREAM_ITEM_HEADER_FRAG_MASK;
    header.size = (data >> BIO_STREAM_ITEM_HEADER_SIZE_SHIFT) & BIO_STREAM_ITEM_HEADER_SIZE_MASK;

    return header;
}

err_code_t bio_stream_initialize(void)
{
    (void)bio_stream_shutdown();

    g_config.item_filter = DEFAULT_ITEM_FILTER;
    /* g_config.max_packet_size does not contain the size of the packet counter */
    g_config.max_packet_size = DEFAULT_MAX_PACKET_SIZE - sizeof(g_packet_counter);
    g_config.reserved = DEFAULT_RESERVED_DATA;

    M_CHECK_SUCCESS(FIFO_Reset(&g_output_queue));
    g_packet_counter = 0;

    g_temp_data.id = 0;
    g_temp_data.fill_size = 0;
    g_temp_data.maximum_size =
        M_MIN(sizeof(g_temp_data.buffer), g_config.max_packet_size - BIO_STREAM_ITEM_HEADER_SIZE);
    g_close_package_queue_in = UINT32_MAX;

    g_state = BIO_STREAM_STATE_CONFIGURATION;

    return ERR_SUCCESS;
}

err_code_t bio_stream_configure(const void *p_config, uint8_t size)
{
    M_CHECK_STATE(BIO_STREAM_STATE_CONFIGURATION);

    M_CHECK_NULL_POINTER(p_config);
    M_CHECK_SIZE(size, sizeof(bio_stream_configuration_t));

    const bio_stream_configuration_t *p_stream_config = (const bio_stream_configuration_t *)p_config;

    /* Expect at least a size of 4 bytes to support a minimum payload size of 1 */
    if ((BIO_STREAM_ITEM_HEADER_SIZE + sizeof(g_packet_counter)) >= p_stream_config->max_packet_size) {
        return ERR_ARGUMENT;
    }
    /* Packet counter is not stored in output queue and is generated and prepended in get_items_from_queue */
    if (BIO_STREAM_OUTPUT_QUEUE_SIZE + sizeof(g_packet_counter) < p_stream_config->max_packet_size) {
        return ERR_ARGUMENT;
    }
    if (0 != p_stream_config->reserved) {
        return ERR_ARGUMENT;
    }

    memcpy((void *)&g_config, p_stream_config, sizeof(g_config));

    /* Subtract size of packet counter */
    g_config.max_packet_size -= sizeof(g_packet_counter);
    g_temp_data.maximum_size =
        M_MIN(sizeof(g_temp_data.buffer), g_config.max_packet_size - BIO_STREAM_ITEM_HEADER_SIZE);

    return ERR_SUCCESS;
}

err_code_t bio_stream_get_configuration(void *p_dest, uint8_t *p_size)
{
    M_CHECK_STATE(BIO_STREAM_STATE_CONFIGURATION);

    M_CHECK_NULL_POINTER(p_dest);
    M_CHECK_NULL_POINTER(p_size);

    if (*p_size < sizeof(bio_stream_configuration_t)) {
        return ERR_SIZE;
    }

    memcpy(p_dest, (void *)&g_config, sizeof(bio_stream_configuration_t));

    /* Undo subtraction of packet counter size */
    bio_stream_configuration_t *p_stream_config = (bio_stream_configuration_t *)p_dest;
    p_stream_config->max_packet_size += sizeof(g_packet_counter);

    *p_size = sizeof(bio_stream_configuration_t);

    return ERR_SUCCESS;
}

err_code_t bio_stream_start(void)
{
    M_CHECK_STATE(BIO_STREAM_STATE_CONFIGURATION);

    M_CHECK_SUCCESS(FIFO_Reset(&g_output_queue));
    g_packet_counter = 0;

    g_temp_data.id = 0;
    g_temp_data.fill_size = 0;
    g_close_package_queue_in = UINT32_MAX;

    g_state = BIO_STREAM_STATE_PROCESSING;

    return ERR_SUCCESS;
}

err_code_t bio_stream_set_input(uint8_t id, const void *p_data, uint16_t size, uint8_t option_flags,
                                bio_execution_status_t *p_result)
{
    M_CHECK_STATE(BIO_STREAM_STATE_PROCESSING);

    M_CHECK_NULL_POINTER(p_data);

    if (MAX_ID < id) {
        return ERR_ARGUMENT;
    }
    if (0 == size) {
        return ERR_SIZE;
    }

    if (FALSE == ((1ull << id) & g_config.item_filter)) {
        return ERR_SUCCESS;
    }

    if (BIO_STREAM_SEND_OPTION_FLAG_ALLOW_EXTENSION & option_flags) {
        /* Send the temporary data to the queue if the ID differs or if there is not enough space for the new data */
        if (g_temp_data.fill_size && (id != g_temp_data.id)) {
            M_CHECK_SUCCESS(add_item_to_queue(g_temp_data.id, g_temp_data.buffer, g_temp_data.fill_size, FALSE));
            g_temp_data.fill_size = 0;
        } else if (g_temp_data.fill_size && ((g_temp_data.maximum_size - g_temp_data.fill_size) <= size)) {
            /* Fill up the temporary buffer */
            memcpy((void *)(g_temp_data.buffer + g_temp_data.fill_size), p_data,
                   g_temp_data.maximum_size - g_temp_data.fill_size);
            /* Transmit the temporary buffer to the queue */
            M_CHECK_SUCCESS(add_item_to_queue(g_temp_data.id, g_temp_data.buffer, g_temp_data.maximum_size, TRUE));
            /* Remove the already copied data from input buffer */
            size -= g_temp_data.maximum_size - g_temp_data.fill_size;
            p_data = ((const uint8_t *)p_data) + (g_temp_data.maximum_size - g_temp_data.fill_size);
            g_temp_data.fill_size = 0;
        }

        /* Copy only a multiple of the temp buffer size to the queue to reduce impact of item header overhead. */
        uint16_t transfer_size = (size / g_temp_data.maximum_size) * g_temp_data.maximum_size;
        if (transfer_size) {
            /* Temporary buffer is guaranteed to be empty */
            M_CHECK_SUCCESS(add_item_to_queue(id, p_data, transfer_size, size > transfer_size));
            /* Remove the already copied data from input buffer */
            size -= transfer_size;
            p_data = ((const uint8_t *)p_data) + transfer_size;
        }

        /* Save the remaining data inside the temporary buffer */
        if (size) {
            /* Remaining data is guaranteed to fit in temporary buffer */
            memcpy((void *)(g_temp_data.buffer + g_temp_data.fill_size), p_data, size);
            g_temp_data.fill_size += size;
        }

        g_temp_data.id = id;

        /* Temporary buffer must be transferred to the queue if the package is force-closed */
        if (g_temp_data.fill_size && (BIO_STREAM_SEND_OPTION_FLAG_CLOSE_PACKAGE & option_flags)) {
            M_CHECK_SUCCESS(add_item_to_queue(g_temp_data.id, g_temp_data.buffer, g_temp_data.fill_size, FALSE));
            g_temp_data.fill_size = 0;
        }
    } else {
        /* Transfer the temporary buffer to the queue (if it contains data) and add the new data to the queue */
        if (g_temp_data.fill_size) {
            M_CHECK_SUCCESS(add_item_to_queue(g_temp_data.id, g_temp_data.buffer, g_temp_data.fill_size, FALSE));
            g_temp_data.fill_size = 0;
        }
        M_CHECK_SUCCESS(add_item_to_queue(id, p_data, size, FALSE));
    }

    if ((BIO_STREAM_SEND_OPTION_FLAG_CLOSE_PACKAGE & option_flags)) {
        g_close_package_queue_in = g_output_queue.in;
    }

    if (p_result) {
        if (ERR_SUCCESS == get_available_output_data_size(NULL)) {
            *p_result = BIO_EXECUTION_STATUS_EXECUTABLE;
        } else {
            *p_result = BIO_EXECUTION_STATUS_NOT_EXECUTABLE;
        }
    }

    return ERR_SUCCESS;
}

err_code_t bio_stream_execute(bio_output_status_t *p_result)
{
    M_CHECK_STATE(BIO_STREAM_STATE_PROCESSING);
    M_CHECK_NULL_POINTER(p_result);

    if (ERR_SUCCESS == get_available_output_data_size(NULL)) {
        *p_result = BIO_OUTPUT_STATUS_DATA_AVAILABLE;
    } else {
        *p_result = BIO_OUTPUT_STATUS_DATA_UNAVAILABLE;
    }

    return ERR_SUCCESS;
}

err_code_t bio_stream_get_output(void *p_dest, uint16_t *p_size)
{
    M_CHECK_STATE_NOT(BIO_STREAM_STATE_UNINITIALIZED);

    M_CHECK_NULL_POINTER(p_dest);
    M_CHECK_NULL_POINTER(p_size);

    return get_items_from_queue((uint8_t *)p_dest, p_size);
}

err_code_t bio_stream_stop(void)
{
    M_CHECK_STATE_NOT(BIO_STREAM_STATE_UNINITIALIZED);

    /* Before stopping, transfer the temporary buffer to the queue if it contains data */
    if (g_temp_data.fill_size) {
        /* bio_stream_stop and bio_stream_set_input can be called from different contexts. Both functions add data to
         * the queue and manipulate g_temp_data. This can result in corrupted data. */
        M_CHECK_SUCCESS(add_item_to_queue(g_temp_data.id, g_temp_data.buffer, g_temp_data.fill_size, FALSE));
        g_temp_data.fill_size = 0;
    }

    g_state = BIO_STREAM_STATE_CONFIGURATION;

    return ERR_SUCCESS;
}

err_code_t bio_stream_shutdown(void)
{
    g_state = BIO_STREAM_STATE_UNINITIALIZED;

    return ERR_SUCCESS;
}

const char *bio_stream_get_version(void)
{
    return BIO_STREAM_VERSION;
}
