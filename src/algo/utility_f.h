#ifndef UTILITY_F_H
#define UTILITY_F_H

#include <math.h>
#include <stdbool.h>
#include <stddef.h>   /* for NULL */
#include "ppg_workspace_f.h"

#ifdef __cplusplus
extern "C" {
#endif

float py_roundf_bankers(float x);

int   custom_diff_f(const float *arr, int n, float *out);
float custom_mean_f(const float *arr, int n);
float custom_std_nan_omit_unbiased_f(const float *arr, int n);
float custom_var_unbiased_f(const float *arr, int n);
float custom_min_f(const float *arr, int n);
float custom_max_f(const float *arr, int n);
float custom_trapz_f(const float *segment, int n);

void  manual_sort_float(float *arr, int n);
void  sort_int(int *a, int n);
int   unique_sorted_int(int *a, int n);

float custom_median_f_ws(const float *arr, int n, float *scratch);
float custom_prctile_f_ws(const float *x, int n, float p, float *scratch);

float custom_skewness_f(const float *data, int n);
float custom_kurtosis_f_ws(const float *x, int n, float *scratch);

int   custom_median_filter_5tap_f(const float *input, int n, float *output);
void  reverse_array_f(const float *in, int n, float *out);
int   even_mirror_pad_f(const float *x, int n, int pad_len, float *out);

int   iir_filter_direct_form_i_f(const float *x, int n,
                                 const float *b, int nb,
                                 const float *a, int na,
                                 float *y);

void  remove_dc_offset_f(const float *in, int n, float *out);

FeaturesF make_nan_features_f(void);

#ifdef __cplusplus
}
#endif

#endif
