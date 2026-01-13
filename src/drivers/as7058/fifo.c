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

/******************************************************************************
 *                                 INCLUDES                                   *
 ******************************************************************************/

#include <stddef.h>
#include <string.h>

#include "error_codes.h"
#include "fifo.h"

/******************************************************************************
 *                                DEFINITIONS                                 *
 ******************************************************************************/

#ifndef FIFO_FUNC_DEFN
/*! Preprocessor macro that is placed in front of every definition of a public function with external linkage. By
 *  default this macro is defined to expand to nothing, but it can be defined externally. Example use cases include
 *  setting keywords. */
#define FIFO_FUNC_DEFN
#endif

/******************************************************************************
 *                                  GLOBALS                                   *
 ******************************************************************************/

/******************************************************************************
 *                               LOCAL FUNCTIONS                              *
 ******************************************************************************/

/******************************************************************************
 *                             GLOBAL FUNCTIONS                               *
 ******************************************************************************/

FIFO_FUNC_DEFN err_code_t FIFO_GetItemCount(fifo_t *p_fifo, uint32_t *p_count)
{
    M_CHECK_NULL_POINTER(p_fifo);
    M_CHECK_NULL_POINTER(p_count);

    *p_count = (p_fifo->in - p_fifo->out + p_fifo->capacity) % p_fifo->capacity;

    return ERR_SUCCESS;
}

FIFO_FUNC_DEFN err_code_t FIFO_GetFreeCount(fifo_t *p_fifo, uint32_t *p_count)
{
    int32_t temp;

    M_CHECK_NULL_POINTER(p_fifo);
    M_CHECK_NULL_POINTER(p_count);

    temp = p_fifo->in - p_fifo->out;

    if (temp < 0) {
        temp += p_fifo->capacity;
    }

    temp = p_fifo->capacity - temp - 1;

    if (temp < 0) {
        temp = 0;
    }

    *p_count = temp;

    return ERR_SUCCESS;
}

FIFO_FUNC_DEFN err_code_t FIFO_Put(fifo_t *p_fifo, const void *p_item)
{
    err_code_t result;
    uint32_t temp;
    uint32_t i;

    M_CHECK_NULL_POINTER(p_fifo);
    M_CHECK_NULL_POINTER(p_item);

    result = FIFO_GetFreeCount(p_fifo, &temp);
    if (ERR_SUCCESS != result) {
        return result;
    }
    if (0 == temp) {
        return ERR_FIFO;
    }

    /* copy item value */
    for (i = 0; i < p_fifo->itemsize; i++) {
        ((uint8_t *)(p_fifo->data))[(p_fifo->in * p_fifo->itemsize) + i] = ((uint8_t *)(p_item))[i];
    }

    /* increase next write index */
    temp = p_fifo->in + 1;
    if (temp >= p_fifo->capacity) {
        temp = 0;
    }
    p_fifo->in = temp;

    return ERR_SUCCESS;
}

FIFO_FUNC_DEFN err_code_t FIFO_PutMultiple(fifo_t *p_fifo, const void *p_items, uint32_t item_cnt)
{
    M_CHECK_NULL_POINTER(p_fifo);
    M_CHECK_NULL_POINTER(p_items);

    uint32_t free_cnt;
    err_code_t result = FIFO_GetFreeCount(p_fifo, &free_cnt);
    if (ERR_SUCCESS != result) {
        return result;
    }
    if (item_cnt > free_cnt) {
        return ERR_FIFO;
    }

    uint32_t remaining_size_to_put = item_cnt * p_fifo->itemsize;
    uint32_t buffer_size = p_fifo->capacity * p_fifo->itemsize;
    uint32_t current_offset_in_buffer = p_fifo->in * p_fifo->itemsize;

    uint32_t size_until_buffer_end = buffer_size - current_offset_in_buffer;
    if (remaining_size_to_put < size_until_buffer_end) {
        size_until_buffer_end = remaining_size_to_put;
    }

    memcpy((uint8_t *)p_fifo->data + current_offset_in_buffer, p_items, size_until_buffer_end);
    remaining_size_to_put -= size_until_buffer_end;

    if (remaining_size_to_put > 0) {
        memcpy(p_fifo->data, (uint8_t *)p_items + size_until_buffer_end, remaining_size_to_put);
    }

    uint32_t temp = p_fifo->in + item_cnt;
    if (temp >= p_fifo->capacity) {
        temp -= p_fifo->capacity;
    }
    p_fifo->in = temp;

    return ERR_SUCCESS;
}

FIFO_FUNC_DEFN err_code_t FIFO_Get(fifo_t *p_fifo, void *p_item)
{
    err_code_t result;
    uint32_t temp;
    uint32_t i;

    M_CHECK_NULL_POINTER(p_fifo);
    M_CHECK_NULL_POINTER(p_item);

    result = FIFO_GetItemCount(p_fifo, &temp);
    if (ERR_SUCCESS != result) {
        return result;
    }
    if (0 == temp) {
        return ERR_FIFO;
    }

    /* copy item value */
    for (i = 0; i < p_fifo->itemsize; i++) {
        ((uint8_t *)(p_item))[i] = ((uint8_t *)(p_fifo->data))[(p_fifo->out * p_fifo->itemsize) + i];
    }

    /* increase next read index */
    temp = p_fifo->out + 1;
    if (temp >= p_fifo->capacity) {
        temp = 0;
    }
    p_fifo->out = temp;

    return ERR_SUCCESS;
}

FIFO_FUNC_DEFN err_code_t FIFO_GetMultiple(fifo_t *p_fifo, void *p_items, uint32_t item_cnt)
{
    M_CHECK_NULL_POINTER(p_fifo);
    M_CHECK_NULL_POINTER(p_items);

    uint32_t avail_cnt;
    err_code_t result = FIFO_GetItemCount(p_fifo, &avail_cnt);
    if (ERR_SUCCESS != result) {
        return result;
    }
    if (item_cnt > avail_cnt) {
        return ERR_FIFO;
    }

    uint32_t remaining_size_to_get = item_cnt * p_fifo->itemsize;
    uint32_t buffer_size = p_fifo->capacity * p_fifo->itemsize;
    uint32_t current_offset_in_buffer = p_fifo->out * p_fifo->itemsize;

    uint32_t size_until_buffer_end = buffer_size - current_offset_in_buffer;
    if (remaining_size_to_get < size_until_buffer_end) {
        size_until_buffer_end = remaining_size_to_get;
    }

    memcpy(p_items, (uint8_t *)p_fifo->data + current_offset_in_buffer, size_until_buffer_end);
    remaining_size_to_get -= size_until_buffer_end;

    if (remaining_size_to_get > 0) {
        memcpy((uint8_t *)p_items + size_until_buffer_end, p_fifo->data, remaining_size_to_get);
    }

    uint32_t temp = p_fifo->out + item_cnt;
    if (temp >= p_fifo->capacity) {
        temp -= p_fifo->capacity;
    }
    p_fifo->out = temp;

    return ERR_SUCCESS;
}

FIFO_FUNC_DEFN err_code_t FIFO_Peek(fifo_t *p_fifo, void *p_item)
{
    uint32_t i;

    M_CHECK_NULL_POINTER(p_fifo);
    M_CHECK_NULL_POINTER(p_item);

    if (p_fifo->in == p_fifo->out) {
        /* circular buffer is empty*/
        return ERR_FIFO;
    }

    /* copy item value */
    for (i = 0; i < p_fifo->itemsize; i++) {
        ((uint8_t *)(p_item))[i] = ((uint8_t *)(p_fifo->data))[(p_fifo->out * p_fifo->itemsize) + i];
    }
    return ERR_SUCCESS;
}

FIFO_FUNC_DEFN err_code_t FIFO_Reset(fifo_t *p_fifo)
{
    M_CHECK_NULL_POINTER(p_fifo);

    p_fifo->in = 0;
    p_fifo->out = 0;

    return ERR_SUCCESS;
}
