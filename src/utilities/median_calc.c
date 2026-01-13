#include "median_calc.h"
#include "libpqueue/src/pqueue.h"
#include "circularbuffer/circularbuffer.h"

#include <zephyr/kernel.h>
#include <string.h>

typedef struct{
    double data;
    size_t pos;
}heap_node_t;

CircularBufferContext mad_vals_buf_ctx;
heap_node_t mad_values[MAD_WINDOW_SIZE];

uint16_t mad_value_index = 0;

pqueue_t *min_pq = NULL; //Larger values
pqueue_t *max_pq = NULL; // Smaller values

static pqueue_pri_t get_priority(void *a)
{
    return ((heap_node_t *)a)->data;
}

static void set_priority(void *a, pqueue_pri_t pri)
{
    // Do nothing
}

static size_t get_pos(void *a)
{
    return ((heap_node_t *)a)->pos;
}

static void set_pos(void *a, size_t pos)
{
    ((heap_node_t *)a)->pos = pos;
} 

static int max_priority_compare_cb(pqueue_pri_t next, pqueue_pri_t curr)
{
    return (next > curr); 
}

static int min_priority_compare_cb(pqueue_pri_t next, pqueue_pri_t curr)
{

    return (next <= curr); 
}

bool median_calc_init()
{
    max_pq = pqueue_init((MAD_WINDOW_SIZE/2), max_priority_compare_cb, get_priority, set_priority,
                        get_pos, set_pos);
    min_pq = pqueue_init((MAD_WINDOW_SIZE/2), min_priority_compare_cb, get_priority, set_priority,
                        get_pos, set_pos);

    if(max_pq == NULL || min_pq == NULL){
        return false;
    }

    CircularBufferInit(&mad_vals_buf_ctx, mad_values, MAD_WINDOW_SIZE, sizeof(heap_node_t));
    
    return true;
}

double median_update(double value, double *current_median)
{
    heap_node_t val_node = {.data = value, .pos = 0};
    heap_node_t *max_node_root = pqueue_peek(max_pq);
    heap_node_t *write_node = NULL;

    CircularBufferPushBack(&mad_vals_buf_ctx, &val_node);
    CircularBufferPeek(&mad_vals_buf_ctx, (CircularBufferSize(&mad_vals_buf_ctx) - 1), (void **)(&write_node));
    mad_value_index++;

    if(max_node_root){
        if(value <= max_node_root->data){
            pqueue_insert(max_pq, write_node);
        }
        else{
            pqueue_insert(min_pq, write_node);
        }
    }
    else{
        // Empty queue, add to max
        pqueue_insert(max_pq, write_node);
    }

    if(mad_value_index >= MAD_WINDOW_SIZE){
        heap_node_t _temp_node;
        CircularBufferPopFront(&mad_vals_buf_ctx, &_temp_node);
        if(_temp_node.data > *current_median){
            pqueue_remove(min_pq, &_temp_node);
        }
        else{
            pqueue_remove(max_pq, &_temp_node);
        }

        mad_value_index -= 1;
    }

    uint16_t max_len = pqueue_size(max_pq);
    uint16_t min_len = pqueue_size(min_pq);

    while(max_len > (min_len + 1)){
        heap_node_t *_temp = pqueue_pop(max_pq);
        val_node.data = _temp->data;
        pqueue_insert(min_pq, &val_node);

        max_len = pqueue_size(max_pq);
    }

    while(min_len > (max_len + 1)){
        heap_node_t *_temp = pqueue_pop(min_pq);
        val_node.data = _temp->data;
        pqueue_insert(max_pq, &val_node);

        min_len = pqueue_size(min_pq);
    }

    // printk("Max %d, Min %d\r\n", max_len, min_len);

    if(max_len == min_len){
        heap_node_t *_temp_max = pqueue_peek(max_pq);
        heap_node_t *_temp_min = pqueue_peek(min_pq);

        if(_temp_max != NULL && _temp_min != NULL){
            *current_median = (_temp_max->data + _temp_min->data) / 2;
        }

        // printk("Median a: %f\r\n", *current_median);
    }
    else if(max_len > min_len){
        heap_node_t *_temp_max = pqueue_peek(max_pq);
        *current_median = _temp_max->data;

        // printk("Median b: %f\r\n", *current_median);
    }
    else{
        heap_node_t *_temp_min = pqueue_peek(min_pq);
        *current_median = _temp_min->data;
        // printk("Median c: %f\r\n", *current_median);
    }

    return *current_median;
}