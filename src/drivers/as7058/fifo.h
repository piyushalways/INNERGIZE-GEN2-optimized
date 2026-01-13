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

#ifndef __FIFO_H__
#define __FIFO_H__

#ifdef __cplusplus
extern "C" {
#endif

/*!
 * \file      fifo.h
 * \copyright ams
 * \addtogroup utilities
 *
 * \brief Simple implementation of a circular buffer
 *
 * General usage:
 *  Call FIFO_Declare(name,cnt,type), which allocates a buffer object.
 *
 *  \note: FIFO_Declare is actually a definition of the object, so take care
 *  of the scope.
 *
 *  @{
 */

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include <stdint.h>

#include "error_codes.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

#ifndef FIFO_FUNC_DECL
/*! Preprocessor macro that is placed in front of every public function declaration with external linkage. By default
 *  this macro is defined to expand to nothing, but it can be defined externally. Example use cases include setting
 *  keywords. */
#define FIFO_FUNC_DECL
#endif

/*! FIFO type definition  */
typedef volatile struct fifo {
    uint32_t itemsize;
    uint32_t capacity;
    uint32_t in;
    uint32_t out;
    void *data;
} fifo_t;

#define MERGE(x, y) x##y /*!< merge two arguments */

/*! Declaration of the FIFO */
#define FIFO_Declare(name, cnt, type)                                                                                  \
    type MERGE(name, _buf)[cnt + 1];                                                                                   \
    fifo_t name = {sizeof(type), cnt + 1, 0, 0, MERGE(name, _buf)}

/******************************************************************************
 *                                 FUNCTIONS                                  *
 ******************************************************************************/

/*!
 * \brief Get count of current elements in FIFO
 *
 * \param[in] *p_fifo               Pointer to FIFO object
 * \param[out] *p_count             Pointer where the number of elements can be saved.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_POINTER            Pointer to FIFO is zero.
 */
FIFO_FUNC_DECL err_code_t FIFO_GetItemCount(fifo_t *p_fifo, uint32_t *p_count);

/*!
 * \brief Get count of free elements in FIFO
 *
 * \param[in] *p_fifo               Pointer to FIFO object
 * \param[out] *p_count             Pointer where the number of elements can be saved.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_POINTER            Pointer to FIFO is zero.
 */
FIFO_FUNC_DECL err_code_t FIFO_GetFreeCount(fifo_t *p_fifo, uint32_t *p_count);

/*!
 * \brief Put an element into FIFO
 *
 * \param[in] *p_fifo               Pointer to FIFO object.
 * \param[in] *p_item               Pointer to value to put into FIFO.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_POINTER            Pointer to FIFO is zero.
 * \retval ::ERR_FIFO               FIFO-Buffer is full.
 */
FIFO_FUNC_DECL err_code_t FIFO_Put(fifo_t *p_fifo, const void *p_item);

/*!
 * \brief Put multiple elements into FIFO
 *
 * \param[in] *p_fifo               Pointer to FIFO object.
 * \param[in] *p_items              Pointer to begin of buffer containing items to put into FIFO.
 * \param[in] item_cnt              Number of items to put into FIFO.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_POINTER            Pointer to FIFO is zero.
 * \retval ::ERR_FIFO               FIFO buffer is full.
 */
FIFO_FUNC_DECL err_code_t FIFO_PutMultiple(fifo_t *p_fifo, const void *p_items, uint32_t item_cnt);

/*!
 * \brief Get next element in FIFO
 *
 * \param[in] *p_fifo               Pointer to FIFO object.
 * \param[out] *p_item              Pointer to variable, to which the value shall be written.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_POINTER            Pointer to FIFO is zero.
 * \retval ::ERR_FIFO               FIFO-Buffer is empty.
 */
FIFO_FUNC_DECL err_code_t FIFO_Get(fifo_t *p_fifo, void *p_item);

/*!
 * \brief Get next n elements in FIFO
 *
 * \param[in] *p_fifo               Pointer to FIFO object.
 * \param[out] *p_items             Pointer to begin of buffer where the items shall be written.
 * \param[in] item_cnt              Number of items to get from the FIFO.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_POINTER            Pointer to FIFO is zero.
 * \retval ::ERR_FIFO               FIFO buffer contains fewer elements than requested.
 */
FIFO_FUNC_DECL err_code_t FIFO_GetMultiple(fifo_t *p_fifo, void *p_items, uint32_t item_cnt);

/*!
 * \brief Peek next element in FIFO.
 *
 * \note This function is basically the same as FIFO_Get, except the value
 *       is not "consumed" when it is being read
 *
 * \param[in] *p_fifo               Pointer to FIFO object.
 * \param[out] *p_item              Pointer to variable, to which the value shall be written.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_POINTER            Pointer to FIFO is zero.
 * \retval ::ERR_FIFO               FIFO-Buffer is empty.
 */
FIFO_FUNC_DECL err_code_t FIFO_Peek(fifo_t *p_fifo, void *p_item);

/*!
 * \brief Reset FIFO.
 *
 * \param[in] *p_fifo               Pointer to FIFO object.
 *
 * \retval ::ERR_SUCCESS            Function returns without error.
 * \retval ::ERR_POINTER            Pointer to FIFO is zero.
 */
FIFO_FUNC_DECL err_code_t FIFO_Reset(fifo_t *p_fifo);

/*!
 *  @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __FIFO_H__ */
