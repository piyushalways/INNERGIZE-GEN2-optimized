#include "utility_f.h"

float py_roundf_bankers(float x)
{
    if (!isfinite(x)) return x;

    float ax = fabsf(x);
    float f = floorf(ax);
    float frac = ax - f;

    float r;
    if (frac > 0.5f) r = f + 1.0f;
    else if (frac < 0.5f) r = f;
    else {
        int fi = (int)f;
        r = ((fi % 2) == 0) ? f : (f + 1.0f);
    }
    return (x < 0.0f) ? -r : r;
}

int custom_diff_f(const float *arr, int n, float *out)
{
    if (!arr || !out || n < 2) return 0;
    for (int i = 0; i < n - 1; i++) out[i] = arr[i + 1] - arr[i];
    return n - 1;
}

float custom_mean_f(const float *arr, int n)
{
    if (!arr || n <= 0) return 0.0f;
    float s = 0.0f;
    for (int i = 0; i < n; i++) s += arr[i];
    return s / (float)n;
}

float custom_std_nan_omit_unbiased_f(const float *arr, int n)
{
    if (!arr || n <= 1) return NAN;

    float sum = 0.0f;
    int count = 0;
    for (int i = 0; i < n; i++) {
        float v = arr[i];
        if (!isnan(v)) { sum += v; count++; }
    }
    if (count <= 1) return NAN;

    float mean = sum / (float)count;
    float ss = 0.0f;
    for (int i = 0; i < n; i++) {
        float v = arr[i];
        if (!isnan(v)) {
            float d = v - mean;
            ss += d * d;
        }
    }
    return sqrtf(ss / (float)(count - 1));
}

float custom_var_unbiased_f(const float *arr, int n)
{
    if (!arr || n <= 1) return NAN;
    float mean = custom_mean_f(arr, n);
    float ss = 0.0f;
    for (int i = 0; i < n; i++) {
        float d = arr[i] - mean;
        ss += d * d;
    }
    return ss / (float)(n - 1);
}

float custom_min_f(const float *arr, int n)
{
    float mn = arr[0];
    for (int i = 1; i < n; i++) if (arr[i] < mn) mn = arr[i];
    return mn;
}

float custom_max_f(const float *arr, int n)
{
    float mx = arr[0];
    for (int i = 1; i < n; i++) if (arr[i] > mx) mx = arr[i];
    return mx;
}

float custom_trapz_f(const float *segment, int n)
{
    if (!segment || n < 2) return 0.0f;
    float area = 0.5f * segment[0];
    for (int i = 1; i < n - 1; i++) area += segment[i];
    area += 0.5f * segment[n - 1];
    return area;
}

void manual_sort_float(float *arr, int n)
{
    if (arr == NULL || n <= 1) return;

    /* --- build max heap --- */
    for (int start = (n - 2) / 2; start >= 0; start--) {

        int root = start;
        while (1) {
            int child = (root << 1) + 1;   /* left child */
            if (child > n - 1) break;

            /* select larger child */
            if (child + 1 <= n - 1 && arr[child] < arr[child + 1]) {
                child++;
            }

            /* if root smaller than largest child, swap */
            if (arr[root] < arr[child]) {
                float t = arr[root]; arr[root] = arr[child]; arr[child] = t;
                root = child;
            } else {
                break;
            }
        }
    }

    /* --- heap sort --- */
    for (int end = n - 1; end > 0; end--) {

        /* move max to end */
        float t = arr[0]; arr[0] = arr[end]; arr[end] = t;

        /* restore heap on [0..end-1] */
        int root = 0;
        while (1) {
            int child = (root << 1) + 1;
            if (child > end - 1) break;

            if (child + 1 <= end - 1 && arr[child] < arr[child + 1]) {
                child++;
            }

            if (arr[root] < arr[child]) {
                float tt = arr[root]; arr[root] = arr[child]; arr[child] = tt;
                root = child;
            } else {
                break;
            }
        }
    }
}


void sort_int(int *a, int n)
{
    if (a == NULL || n <= 1) return;

    /* sift down in max-heap */
    for (int start = (n - 2) / 2; start >= 0; start--) {

        int root = start;
        while (1) {
            int child = (root << 1) + 1;
            if (child > n - 1) break;

            if (child + 1 <= n - 1 && a[child] < a[child + 1]) child++;

            if (a[root] < a[child]) {
                int t = a[root]; a[root] = a[child]; a[child] = t;
                root = child;
            } else {
                break;
            }
        }
    }

    for (int end = n - 1; end > 0; end--) {

        int t = a[0]; a[0] = a[end]; a[end] = t;

        int root = 0;
        while (1) {
            int child = (root << 1) + 1;
            if (child > end - 1) break;

            if (child + 1 <= end - 1 && a[child] < a[child + 1]) child++;

            if (a[root] < a[child]) {
                int tt = a[root]; a[root] = a[child]; a[child] = tt;
                root = child;
            } else {
                break;
            }
        }
    }
}


int unique_sorted_int(int *a, int n)
{
    if (n <= 1) return n;
    int w = 1;
    for (int i = 1; i < n; i++) if (a[i] != a[w - 1]) a[w++] = a[i];
    return w;
}

float custom_median_f_ws(const float *arr, int n, float *scratch)
{
    if (!arr || !scratch || n <= 0) return NAN;
    for (int i = 0; i < n; i++) scratch[i] = arr[i];
    manual_sort_float(scratch, n);
    if (n & 1) return scratch[(n + 1) / 2 - 1];
    return 0.5f * (scratch[n / 2 - 1] + scratch[n / 2]);
}

float custom_prctile_f_ws(const float *x, int n, float p, float *scratch)
{
    if (!x || !scratch || n <= 0) return NAN;

    int m = 0;
    for (int i = 0; i < n; i++) {
        float v = x[i];
        if (isfinite(v)) scratch[m++] = v;
    }
    if (m == 0) return NAN;

    manual_sort_float(scratch, m);

    if (p <= 0.0f) return scratch[0];
    if (p >= 100.0f) return scratch[m - 1];

    float pn = p / 100.0f;
    float h = (float)m * pn + 0.5f;

    if (h <= 1.0f) return scratch[0];
    if (h >= (float)m) return scratch[m - 1];

    int j = (int)h - 1;
    float t = h - (float)((int)h);

    return scratch[j] * (1.0f - t) + scratch[j + 1] * t;
}

float custom_skewness_f(const float *data, int n)
{
    if (!data || n < 3) return NAN;

    float mu = custom_mean_f(data, n);
    float sigma = custom_std_nan_omit_unbiased_f(data, n);
    if (sigma == 0.0f) return 0.0f;
    if (isnan(sigma)) return NAN;

    float sum = 0.0f;
    for (int i = 0; i < n; i++) {
        float z = (data[i] - mu) / sigma;
        sum += z * z * z;
    }
    return sum / (float)n;
}

float custom_kurtosis_f_ws(const float *x, int n, float *scratch)
{
    if (!x || !scratch || n <= 0) return NAN;

    int m = 0;
    for (int i = 0; i < n; i++) {
        float v = x[i];
        if (!isnan(v)) scratch[m++] = v;
    }
    if (m == 0) return NAN;

    float mu = 0.0f;
    for (int i = 0; i < m; i++) mu += scratch[i];
    mu /= (float)m;

    float m2 = 0.0f, m4 = 0.0f;
    for (int i = 0; i < m; i++) {
        float d = scratch[i] - mu;
        float d2 = d * d;
        m2 += d2;
        m4 += d2 * d2;
    }
    m2 /= (float)m;
    m4 /= (float)m;

    if (m2 == 0.0f) return NAN;
    return m4 / (m2 * m2);
}

int custom_median_filter_5tap_f(const float *input, int n, float *output)
{
    if (!input || !output || n <= 0) return 0;

    /* compare-swap helper */
    #define CSWAP(a,b) do { if ((a) > (b)) { float _t = (a); (a) = (b); (b) = _t; } } while (0)

    for (int ii = 0; ii < n; ii++) {
        int L = ii - 2; if (L < 0) L = 0;
        int R = ii + 2; if (R > n - 1) R = n - 1;
        int m = R - L + 1;

        /* Collect up to 5 samples */
        float w0 = input[L];
        float w1 = (m > 1) ? input[L + 1] : w0;
        float w2 = (m > 2) ? input[L + 2] : w1;
        float w3 = (m > 3) ? input[L + 3] : w2;
        float w4 = (m > 4) ? input[L + 4] : w3;

        float med;

        if (m == 1) {
            med = w0;
        } else if (m == 2) {
            CSWAP(w0, w1);
            med = 0.5f * (w0 + w1);
        } else if (m == 3) {
            CSWAP(w0, w1); CSWAP(w1, w2); CSWAP(w0, w1);
            med = w1;
        } else if (m == 4) {
            /* sort 4 values using compare-swap network */
            CSWAP(w0, w1); CSWAP(w2, w3);
            CSWAP(w0, w2); CSWAP(w1, w3);
            CSWAP(w1, w2);
            med = 0.5f * (w1 + w2);
        } else { /* m == 5 */
            /* sort 5 values (simple fixed network) */
            CSWAP(w0, w1); CSWAP(w3, w4);
            CSWAP(w2, w4); CSWAP(w2, w3);
            CSWAP(w1, w4); CSWAP(w0, w3);
            CSWAP(w0, w2); CSWAP(w1, w3);
            CSWAP(w1, w2);
            med = w2; /* median */
        }

        output[ii] = med;
    }

    #undef CSWAP
    return n;
}


void reverse_array_f(const float *in, int n, float *out)
{
    for (int i = 0; i < n; i++) out[i] = in[n - i - 1];
}

int even_mirror_pad_f(const float *x, int n, int pad_len, float *out)
{
    if (!x || !out || n <= 0 || pad_len < 0) return 0;

    for (int i = 0; i < pad_len; i++) out[i] = 2.0f * x[0] - x[pad_len - i];
    for (int i = 0; i < n; i++) out[pad_len + i] = x[i];
    for (int i = 0; i < pad_len; i++) out[pad_len + n + i] = 2.0f * x[n - 1] - x[n - i - 2];

    return n + 2 * pad_len;
}

int iir_filter_direct_form_i_f(const float *x, int n,
                               const float *b, int nb,
                               const float *a, int na,
                               float *y)
{
    if (!x || !b || !a || !y || n <= 0) return 0;

    /* Assumes nb == 9 and na == 9 (as used in preprocessing) */

    /* local copies for faster access */
    const float b0 = b[0], b1 = b[1], b2 = b[2], b3 = b[3], b4 = b[4],
                b5 = b[5], b6 = b[6], b7 = b[7], b8 = b[8];

    const float a1 = a[1], a2 = a[2], a3 = a[3], a4 = a[4],
                a5 = a[5], a6 = a[6], a7 = a[7], a8 = a[8];

    for (int i = 0; i < n; i++) {
        float acc = 0.0f;

        /* feedforward (k = 0..8) */
        acc += b0 * x[i];
        if (i >= 1) acc += b1 * x[i - 1];
        if (i >= 2) acc += b2 * x[i - 2];
        if (i >= 3) acc += b3 * x[i - 3];
        if (i >= 4) acc += b4 * x[i - 4];
        if (i >= 5) acc += b5 * x[i - 5];
        if (i >= 6) acc += b6 * x[i - 6];
        if (i >= 7) acc += b7 * x[i - 7];
        if (i >= 8) acc += b8 * x[i - 8];

        /* feedback (k = 1..8) */
        if (i >= 1) acc -= a1 * y[i - 1];
        if (i >= 2) acc -= a2 * y[i - 2];
        if (i >= 3) acc -= a3 * y[i - 3];
        if (i >= 4) acc -= a4 * y[i - 4];
        if (i >= 5) acc -= a5 * y[i - 5];
        if (i >= 6) acc -= a6 * y[i - 6];
        if (i >= 7) acc -= a7 * y[i - 7];
        if (i >= 8) acc -= a8 * y[i - 8];

        y[i] = acc;
    }

    return n;
}


void remove_dc_offset_f(const float *in, int n, float *out)
{
    float mean = custom_mean_f(in, n);
    for (int i = 0; i < n; i++) out[i] = in[i] - mean;
}

FeaturesF make_nan_features_f(void)
{
    FeaturesF f;
    f.HR_mean = NAN; f.SDNN = NAN; f.RMSSD = NAN; f.ibi_mean = NAN;
    f.rise_time_ms_mean = NAN; f.rise_slope_mean = NAN; f.pulse_dur_ms_mean = NAN;
    f.systolic_area_mean = NAN; f.ppg_area_mean = NAN;
    f.pulse_skew_mean = NAN; f.pulse_kurt_mean = NAN;
    return f;
}
