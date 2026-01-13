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

#ifndef __STD_INC_H__
#define __STD_INC_H__

/*!
 * \file      std_inc.h
 * \authors   SSHW
 * \copyright ams
 * \addtogroup standard includes
 *
 * \brief Description of standard includes
 *
 * Here you can find generic standard includes,
 * which are used by ams projects.
 *
 *  @{
 */

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/
#ifndef __KERNEL__
#include <math.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#else
#include <linux/kernel.h>
#include <linux/math64.h>
#include <linux/printk.h>
#include <linux/types.h>

#include <asm/string.h>
#endif

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

/*! Boolean representation of 'true' to be used with flat uint8_t type */
#ifndef TRUE
#define TRUE 1
#endif

/*! Boolean representation of 'false' to be used with flat uint8_t type */
#ifndef FALSE
#define FALSE 0
#endif

/*! Pointer to void */
#ifndef PVOID
#define PVOID void *
#endif

/*!
 * Returns the minimum of two integers
 *
 * \warning The argument that is the minimum is evaluated twice. If a function call or a volatile variable is used in
 *          the argument which turns out to be the minimum, the function is called twice or the volatile variable is
 *          read twice.
 */
#define M_MIN(a, b) ((a) < (b) ? (a) : (b))

/*!
 * Returns the maximum of two integers
 *
 * \warning The argument that is the maximum is evaluated twice. If a function call or a volatile variable is used in
 *          the argument which turns out to be the maximum, the function is called twice or the volatile variable is
 *          read twice.
 */
#define M_MAX(a, b) ((a) > (b) ? (a) : (b))

/*! Checks at compile-time whether an expression evaluates to true */
#ifdef __cplusplus
#define M_STATIC_ASSERT(expr, error_str) static_assert((expr), error_str)
#else
#define M_STATIC_ASSERT(expr, error_str) _Static_assert((expr), error_str)
#endif

/*! Checks at compile-time whether a type has the expected size */
#define M_STATIC_ASSERT_TYPE_SIZE(type, expected_size)                                                                 \
    M_STATIC_ASSERT(sizeof(type) == (expected_size),                                                                   \
                    "The type " #type " does not have the expected size " #expected_size ".")

/*! System specific signed 64bit wide divide function */
#ifdef __KERNEL__
#define DIV64_S64(s64dividend, s64divisor) div64_s64(s64dividend, s64divisor)
#else
#define DIV64_S64(s64dividend, s64divisor) (s64dividend / s64divisor)
#endif

/*! System specific signed 64bit wide divide function */
#ifdef __KERNEL__
#define DIV64_U64(u64dividend, u64divisor) div64_u64(u64dividend, u64divisor)
#else
#define DIV64_U64(u64dividend, u64divisor) (u64dividend / u64divisor)
#endif

/*! Definitions of the min/max values of flat data types */
#ifdef __KERNEL__
#define UINT8_MAX U8_MAX
#define INT8_MAX S8_MAX
#define INT8_MIN S8_MIN
#define UINT16_MAX U16_MAX
#define INT16_MAX S16_MAX
#define INT16_MIN S16_MIN
#define UINT32_MAX U32_MAX
#define INT32_MAX S32_MAX
#define INT32_MIN S32_MIN
#define UINT64_MAX U64_MAX
#define INT64_MAX S64_MAX
#define INT64_MIN S64_MIN
#endif

/******************************************************************************
 *                                 FUNCTIONS                                  *
 ******************************************************************************/

/*!
 * \brief Calculate the square root for a given integer value
 *
 * \param[in] x         Value to calculate the square root of
 *
 * \retval uint32_t     The calcuated square root
 */
#ifdef __KERNEL__
static inline uint32_t sqrt(uint64_t x)
{
    return int_sqrt64(x);
}
#endif

/*! @} */

#endif /* __STD_INC_H__ */
