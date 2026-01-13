/******************************************************************************
 * Copyright © 2022 ams-OSRAM AG                                              *
 * All rights are reserved.                                                   *
 *                                                                            *
 * FOR FULL LICENSE TEXT SEE LICENSE.TXT                                      *
 *                                                                            *
 ******************************************************************************/

#ifndef __BIO_STREAM_TYPEDEFS_H__
#define __BIO_STREAM_TYPEDEFS_H__

/*!
 * \file       bio_stream_typedefs.h
 * \authors    ARIT
 * \copyright  ams OSRAM
 * \addtogroup bio_stream_group Streaming Application
 *
 * @{
 */

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include "bio_common.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

/*! Size of the compressed item header. */
#define BIO_STREAM_ITEM_HEADER_SIZE 2

/*! Bitmask for the item ID bits in the compressed item header. */
#define BIO_STREAM_ITEM_HEADER_ID_MASK 0x003F

/*! Bit shift value for the item ID bits in the compressed item header. */
#define BIO_STREAM_ITEM_HEADER_ID_SHIFT 10

/*! Bitmask for the fragmentation bit in the compressed item header. */
#define BIO_STREAM_ITEM_HEADER_FRAG_MASK 0x0001

/*! Bit shift value for the fragmentation bit in the compressed item header. */
#define BIO_STREAM_ITEM_HEADER_FRAG_SHIFT 9

/*! Bitmask for the size bits in the compressed item header. */
#define BIO_STREAM_ITEM_HEADER_SIZE_MASK 0x01FF

/*! Bit shift value for the size bits in the compressed item header. */
#define BIO_STREAM_ITEM_HEADER_SIZE_SHIFT 0

/*! Options for send function. */
enum bio_stream_send_option_flags {
    BIO_STREAM_SEND_OPTION_FLAG_NONE = 0x00,            /*!< All options are disabled. */
    BIO_STREAM_SEND_OPTION_FLAG_ALLOW_EXTENSION = 0x01, /*!< Append data to the last item instead of creating new item,
                                                             if possible. Data can only be appended if buffer sizes
                                                             allow for it and if item ID of the last item is identical
                                                             to the item ID of the data to append. */
    BIO_STREAM_SEND_OPTION_FLAG_CLOSE_PACKAGE = 0x02,   /*!< Package is force-closed after inserting this item. */
};

/*! Contains uncompressed header data of one item. */
typedef struct {
    uint8_t id;            /*!< ID of the item. */
    uint8_t fragmentation; /*!< If non-zero, the current item is fragmented over more then one package. */
    uint16_t size;         /*!< Payload size of this item. */
} bio_stream_header_t;

/*! Contains the configuration options of the streaming app. */
typedef struct {
    uint64_t item_filter;     /*!< Can be used to suppress items with specific IDs in the output packages. Bit index 0
                                   corresponds to item ID 0, bit index 1 to item ID 1. If a bit is not set, items with
                                   the corresponding ID are suppressed. Default value is 0xFFFFFFFFFFFFFFFF, i.e. no
                                   items are suppressed by default. */
    uint32_t max_packet_size; /*!< Maximum size of a single packet. Default value is 150 bytes. */
    uint32_t reserved;        /*!< Unused padding byte. Needs to be set to zero. */
} bio_stream_configuration_t;

/*! @} */

/******************************************************************************
 *                            TYPE SIZE VALIDATION                            *
 ******************************************************************************/

M_STATIC_ASSERT_TYPE_SIZE(bio_stream_configuration_t, 16);
M_STATIC_ASSERT_TYPE_SIZE(bio_stream_header_t, 4);

#endif /* __BIO_STREAM_TYPEDEFS_H__ */
