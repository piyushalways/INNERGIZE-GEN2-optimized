#ifndef MEDIAN_CALC_H
#define MEDIAN_CALC_H

#include <stdbool.h>

#define MAD_WINDOW_SIZE        256

bool median_calc_init();
double median_update(double value, double *current_median);

#endif