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

#ifndef __ERROR_CODES_H__
#define __ERROR_CODES_H__

/*!
 * \file      error_codes.h
 * \authors   ARIT
 * \copyright ams
 */

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

/*!
 * \addtogroup error_group Error Codes
 *
 * Generic error codes used by ams libraries.
 *
 * @{ */

/*! Error Codes. */
enum error_codes {
    ERR_SUCCESS = 0,             /*!< Operation was successful. */
    ERR_PERMISSION = 1,          /*!< Operation is not permitted. */
    ERR_MESSAGE = 2,             /*!< Message is invalid. (Unsupported message type, incorrect CRC, ...) */
    ERR_MESSAGE_SIZE = 3,        /*!< Message has the wrong size. */
    ERR_POINTER = 4,             /*!< Pointer is invalid. (NULL pointer, pointer wrong memory region, ...) */
    ERR_ACCESS = 5,              /*!< Access is denied. */
    ERR_ARGUMENT = 6,            /*!< Argument is invalid. */
    ERR_SIZE = 7,                /*!< An argument has the wrong size. */
    ERR_NOT_SUPPORTED = 8,       /*!< Function is not supported or not implemented. */
    ERR_TIMEOUT = 9,             /*!< Operation timed out. */
    ERR_CHECKSUM = 10,           /*!< Checksum comparision failed. */
    ERR_OVERFLOW = 11,           /*!< Data overflow occurred. */
    ERR_EVENT = 12,              /*!< Getting or setting an event failed. (Event queue is full or empty, unexpected
                                      event received, ...) */
    ERR_INTERRUPT = 13,          /*!< Getting or setting an interrupt failed. (Interrupt resource is not available, ...)
                                  */
    ERR_TIMER_ACCESS = 14,       /*!< Accessing the timer peripheral failed. */
    ERR_LED_ACCESS = 15,         /*!< Accessing the LED peripheral failed. */
    ERR_TEMP_SENSOR_ACCESS = 16, /*!< Accessing the temperature sensor failed. */
    ERR_DATA_TRANSFER = 17,      /*!< Communication error occurred. */
    ERR_FIFO = 18,               /*!< FIFO operation failed. */
    ERR_OVER_TEMP = 19,          /*!< Overtemperature detected. */
    ERR_IDENTIFICATION = 20,     /*!< Sensor identification failed. */
    ERR_COM_INTERFACE = 21,      /*!< Generic communication interface error. (Communication interface is not available,
                                      error while opening or closing a communication interface, ...) */
    ERR_SYNCHRONISATION = 22,    /*!< Synchronization error occurred. */
    ERR_PROTOCOL = 23,           /*!< Generic protocol error occurred. */
    ERR_MEMORY = 24,             /*!< Memory allocation error occurred. */
    ERR_THREAD = 25,             /*!< Thread handling operation failed. */
    ERR_SPI = 26,                /*!< Accessing the SPI peripheral failed. */
    ERR_DAC_ACCESS = 27,         /*!< Accessing the DAC peripheral failed. */
    ERR_I2C = 28,                /*!< Accessing the I2C peripheral failed. */
    ERR_NO_DATA = 29,            /*!< No data available. */
    ERR_SYSTEM_CONFIG = 30,      /*!< System configuration failed. (System resource is not available, system resource
                                      generates an error, ...) */
    ERR_USB_ACCESS = 31,         /*!< Accessing the USB peripheral failed. */
    ERR_ADC_ACCESS = 32,         /*!< Accessing the ADC peripheral failed. */
    ERR_SENSOR_CONFIG = 33,      /*!< Sensor configuration failed. */
    ERR_SATURATION = 34,         /*!< Saturation detected. */
    ERR_MUTEX = 35,              /*!< Mutex handling operation filed. */
    ERR_ACCELEROMETER = 36,      /*!< Accessing the accelerometer failed. */
    ERR_CONFIG = 37,             /*!< Software component is unusable due to incomplete or incorrect configuration. */
    ERR_BLE = 38,                /*!< BLE stack handling operation failed. */
    ERR_FILE = 39,               /*!< File handling operation failed. */
    ERR_DATA = 40,               /*!< Internal data inconsistency detected. */
    ERR_BUSY = 41,               /*!< Module is busy. */
};

/*! This definition will be used for function return values. */
typedef enum error_codes err_code_t;

/*! @} */

/*! Returns an error code if the arg_value is greater than the max_value. */
#define M_CHECK_ARGUMENT_LOWER_EQUAL(arg_value, max_value)                                                             \
    do {                                                                                                               \
        if (arg_value > max_value) {                                                                                   \
            return ERR_ARGUMENT;                                                                                       \
        }                                                                                                              \
    } while (0)

/*! Returns an error code if the first value is greater or equal than the second one. */
#define M_CHECK_ARGUMENT_LOWER(arg_value, max_value)                                                                   \
    do {                                                                                                               \
        if (arg_value >= max_value) {                                                                                  \
            return ERR_ARGUMENT;                                                                                       \
        }                                                                                                              \
    } while (0)

/*! Returns an error code if the value is zero. */
#define M_CHECK_ARGUMENT_NOT_ZERO(value)                                                                               \
    do {                                                                                                               \
        if (0 == value) {                                                                                              \
            return ERR_ARGUMENT;                                                                                       \
        }                                                                                                              \
    } while (0)

/** Returns an error code if the value is not a multiple of multiplier. */
#define M_CHECK_ARGUMENT_MULTIPLE_OF(multiplier, value)                                                                \
    do {                                                                                                               \
        if ((multiplier % value) != 0) {                                                                               \
            return ERR_ARGUMENT;                                                                                       \
        }                                                                                                              \
    } while (0)

/*! Returns an error code if the given address is zero. */
#define M_CHECK_NULL_POINTER(pointer)                                                                                  \
    do {                                                                                                               \
        if (NULL == pointer) {                                                                                         \
            return ERR_POINTER;                                                                                        \
        }                                                                                                              \
    } while (0)

/** Returns an error code if the values are not equal. */
#define M_CHECK_SIZE(expected, given)                                                                                  \
    do {                                                                                                               \
        if (expected != given) {                                                                                       \
            return ERR_SIZE;                                                                                           \
        }                                                                                                              \
    } while (0)

/*! Checks whether the provided result is ERR_SUCCESS and returns the result as-is otherwise. */
#define M_CHECK_SUCCESS(result)                                                                                        \
    do {                                                                                                               \
        err_code_t _result = (result);                                                                                 \
        if (_result != ERR_SUCCESS) {                                                                                  \
            return _result;                                                                                            \
        }                                                                                                              \
    } while (0)

/*! Mark unused arguments to get no fails on static code analysis. */
#ifndef M_UNUSED_PARAM
#define M_UNUSED_PARAM(x) (void)(x)
#endif

/******************************************************************************
 *                                 FUNCTIONS                                  *
 ******************************************************************************/

#endif /* __ERROR_CODES_H__ */
