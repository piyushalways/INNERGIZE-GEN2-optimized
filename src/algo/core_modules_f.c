#include "core_modules_f.h"
#include <math.h>

void acc_prepare_vm_f(ppg_workspace_f_t *ws)
{
    /* 1) Convert mg->g and compute means (for detrend) */
    float sx = 0.0f, sy = 0.0f, sz = 0.0f;

    for (int i = 0; i < WIN_SAMP_ACC; i++) {
        sx += ws->acc_x[i] / 1000.0f;
        sy += ws->acc_y[i] / 1000.0f;
        sz += ws->acc_z[i] / 1000.0f;
    }

    float mx = sx / (float)WIN_SAMP_ACC;
    float my = sy / (float)WIN_SAMP_ACC;
    float mz = sz / (float)WIN_SAMP_ACC;

    /* 2) Detrend + vector magnitude directly into acc_vm[] */
    for (int i = 0; i < WIN_SAMP_ACC; i++) {
        float xg = (ws->acc_x[i] / 1000.0f) - mx;
        float yg = (ws->acc_y[i] / 1000.0f) - my;
        float zg = (ws->acc_z[i] / 1000.0f) - mz;

        ws->acc_vm[i] = sqrtf(xg*xg + yg*yg + zg*zg);
    }
}


void preprocess_ppg_f(ppg_workspace_f_t *ws)
{
    static const float b_bp[9] = {
        0.3094565596591001f, 0.0f, -1.237826238636401f, 0.0f,
        1.856739357954601f, 0.0f, -1.237826238636401f, 0.0f, 0.3094565596591001f
    };
    static const float a_bp[9] = {
        1.0f, -1.844389910081383f, -0.2760718740260203f, 1.310524431484202f,
        0.8267674698208216f, -0.8855547413607049f, -0.4014335679604472f,
        0.1744010549993891f, 0.0959587307421902f
    };

    /* ---- A) median filter: buf_ppg -> scratch1 (replaces seg_med) ---- */
    custom_median_filter_5tap_f(ws->buf_ppg, WIN_SAMP_PPG, ws->scratch1);

    /* ---- B) remove DC: scratch1 -> scratch2 (replaces x0) ---- */
    remove_dc_offset_f(ws->scratch1, WIN_SAMP_PPG, ws->scratch2);

    int M = 9;
    int pad_len = 3 * (M - 1); /* 24 */
    if (pad_len < 1) pad_len = 1;
    if (pad_len > WIN_SAMP_PPG - 2) pad_len = WIN_SAMP_PPG - 2;

    /* ---- C) mirror-pad: scratch2 -> xp ---- */
    int xp_len = even_mirror_pad_f(ws->scratch2, WIN_SAMP_PPG, pad_len, ws->xp);

    /* ---- D) forward IIR: xp -> tmp ---- */
    iir_filter_direct_form_i_f(ws->xp, xp_len, b_bp, 9, a_bp, 9, ws->tmp);

    /* ---- E) reverse tmp -> xp ---- */
    reverse_array_f(ws->tmp, xp_len, ws->xp);

    /* ---- F) backward IIR: xp -> tmp ---- */
    iir_filter_direct_form_i_f(ws->xp, xp_len, b_bp, 9, a_bp, 9, ws->tmp);

    /* ---- G) reverse tmp -> xp (final filtfilt output in xp) ---- */
    reverse_array_f(ws->tmp, xp_len, ws->xp);

    /* ---- H) unpad center -> buf_filt ---- */
    for (int i = 0; i < WIN_SAMP_PPG; i++) {
        ws->buf_filt[i] = ws->xp[pad_len + i];
    }

    /* ---- I) final DC removal in-place ---- */
    remove_dc_offset_f(ws->buf_filt, WIN_SAMP_PPG, ws->buf_filt);
}


/* internal peak/onset */
static void vpg_peak_onset_detection3_f(ppg_workspace_f_t *ws, const float *seg_filt)
{
    ws->n_peaks = 0;
    ws->n_onsets = 0;

    ws->vpg_len = custom_diff_f(seg_filt, WIN_SAMP_PPG, ws->vpg);

    int cand_pk[MAX_CAND];
    int cand_pk_n = 0;
    for (int i = 0; i < ws->vpg_len - 1; i++) {
        if (ws->vpg[i] > 0.0f && ws->vpg[i + 1] <= 0.0f) {
            if (cand_pk_n < MAX_CAND) cand_pk[cand_pk_n++] = i + 2;
        }
    }

    int w_snap = (int)py_roundf_bankers(0.04f * (float)FS_PPG);

    for (int k = 0; k < cand_pk_n; k++) {
        int cand0 = cand_pk[k] - 1;
        int i0 = cand0 - w_snap; if (i0 < 0) i0 = 0;
        int i1 = cand0 + w_snap; if (i1 > WIN_SAMP_PPG - 1) i1 = WIN_SAMP_PPG - 1;

        float max_val = seg_filt[i0];
        int max_idx = i0;
        for (int idx = i0; idx <= i1; idx++) {
            if (seg_filt[idx] > max_val) { max_val = seg_filt[idx]; max_idx = idx; }
        }
        cand_pk[k] = max_idx + 1;
    }

    sort_int(cand_pk, cand_pk_n);
    cand_pk_n = unique_sorted_int(cand_pk, cand_pk_n);

    float ppg_med = custom_median_f_ws(seg_filt, WIN_SAMP_PPG, ws->scratch1);
    for (int i = 0; i < WIN_SAMP_PPG; i++) ws->scratch2[i] = fabsf(seg_filt[i] - ppg_med);
    float ppg_mad = custom_median_f_ws(ws->scratch2, WIN_SAMP_PPG, ws->scratch1);
    float amp_thr = ppg_med + 0.1f * ppg_mad;

    int cand_pk2[MAX_CAND];
    int cand_pk2_n = 0;
    for (int i = 0; i < cand_pk_n; i++) {
        int idx0 = cand_pk[i] - 1;
        if (seg_filt[idx0] > amp_thr) cand_pk2[cand_pk2_n++] = cand_pk[i];
    }
    if (cand_pk2_n == 0) return;

    int min_gap = (int)py_roundf_bankers(0.40f * (float)FS_PPG);

    int peak_idx[MAX_PEAKS];
    int peak_n = 0;
    peak_idx[peak_n++] = cand_pk2[0];

    for (int k = 1; k < cand_pk2_n; k++) {
        int cur = cand_pk2[k];
        int last = peak_idx[peak_n - 1];
        if (cur - last >= min_gap) {
            if (peak_n < MAX_PEAKS) peak_idx[peak_n++] = cur;
        } else {
            if (seg_filt[cur - 1] > seg_filt[last - 1]) peak_idx[peak_n - 1] = cur;
        }
    }

    int cand_on[MAX_CAND];
    int cand_on_n = 0;
    for (int i = 0; i < ws->vpg_len - 1; i++) {
        if (ws->vpg[i] < 0.0f && ws->vpg[i + 1] >= 0.0f) {
            if (cand_on_n < MAX_CAND) cand_on[cand_on_n++] = i + 2;
        }
    }

    for (int k = 0; k < cand_on_n; k++) {
        int cand0 = cand_on[k] - 1;
        int i0 = cand0 - w_snap; if (i0 < 0) i0 = 0;
        int i1 = cand0 + w_snap; if (i1 > WIN_SAMP_PPG - 1) i1 = WIN_SAMP_PPG - 1;

        if (i1 > i0) {
            float min_val = seg_filt[i0];
            int min_idx = i0;
            for (int idx = i0; idx <= i1; idx++) {
                if (seg_filt[idx] < min_val) { min_val = seg_filt[idx]; min_idx = idx; }
            }
            cand_on[k] = min_idx + 1;
        }
    }

    sort_int(cand_on, cand_on_n);
    cand_on_n = unique_sorted_int(cand_on, cand_on_n);

    int min_onset_peak_gap = (int)py_roundf_bankers(0.2f * (float)FS_PPG);
    int max_onset_peak_gap = (int)py_roundf_bankers(0.8f * (float)FS_PPG);

    int onset_idx[MAX_ONSETS];
    int onset_n = 0;

    int used_onsets[MAX_ONSETS];
    int used_n = 0;

    for (int p = 0; p < peak_n; p++) {
        int current_peak = peak_idx[p];

        int valid_onsets[MAX_CAND];
        int valid_n = 0;

        for (int i = 0; i < cand_on_n; i++) {
            int onset = cand_on[i];
            if (onset < current_peak) {
                int gap = current_peak - onset;
                if (gap >= min_onset_peak_gap && gap <= max_onset_peak_gap) {
                    valid_onsets[valid_n++] = onset;
                }
            }
        }

        if (valid_n > 0) {
            int best_onset = valid_onsets[0];
            float min_amp = seg_filt[best_onset - 1];

            for (int i = 1; i < valid_n; i++) {
                int onset = valid_onsets[i];
                float amp = seg_filt[onset - 1];
                if (amp < min_amp) { min_amp = amp; best_onset = onset; }
            }

            int already = 0;
            for (int i = 0; i < used_n; i++) if (used_onsets[i] == best_onset) { already = 1; break; }

            if (!already) {
                if (onset_n < MAX_ONSETS) onset_idx[onset_n++] = best_onset;
                if (used_n < MAX_ONSETS) used_onsets[used_n++] = best_onset;
            }
        }
    }

    if (onset_n < peak_n) {
        for (int p = onset_n; p < peak_n; p++) {
            int estimated = peak_idx[p] - (int)py_roundf_bankers(0.3f * (float)FS_PPG);
            if (estimated < 1) estimated = 1;
            if (onset_n < MAX_ONSETS) onset_idx[onset_n++] = estimated;
        }
    }

    int min_onset_gap = (int)py_roundf_bankers(0.4f * (float)FS_PPG);
    if (onset_n > 0) {
        sort_int(onset_idx, onset_n);

        int final_on[MAX_ONSETS];
        int final_n = 0;
        final_on[final_n++] = onset_idx[0];

        for (int k = 1; k < onset_n; k++) {
            int cur = onset_idx[k];
            int last = final_on[final_n - 1];

            if (cur - last >= min_onset_gap) final_on[final_n++] = cur;
            else {
                if (seg_filt[cur - 1] < seg_filt[last - 1]) final_on[final_n - 1] = cur;
            }
        }

        onset_n = final_n;
        for (int i = 0; i < onset_n; i++) onset_idx[i] = final_on[i];
    }

    sort_int(onset_idx, onset_n);
    sort_int(peak_idx, peak_n);

    int peaks_clean[MAX_PEAKS];
    int peaks_clean_n = 0;

    if (onset_n > 0) {
        int first_on = onset_idx[0];
        int last_on  = onset_idx[onset_n - 1];
        for (int i = 0; i < peak_n; i++) {
            int pk = peak_idx[i];
            if (first_on < pk && pk < last_on) peaks_clean[peaks_clean_n++] = pk;
        }
    } else {
        for (int i = 0; i < peak_n; i++) peaks_clean[peaks_clean_n++] = peak_idx[i];
    }

    ws->n_peaks  = (peaks_clean_n < MAX_PEAKS) ? peaks_clean_n : MAX_PEAKS;
    ws->n_onsets = (onset_n < MAX_ONSETS) ? onset_n : MAX_ONSETS;

    for (int i = 0; i < ws->n_peaks; i++) ws->peaks[i] = peaks_clean[i];
    for (int i = 0; i < ws->n_onsets; i++) ws->onsets[i] = onset_idx[i];
}

float SQI_PPG_f(ppg_workspace_f_t *ws)
{
    const int max_hr = 150;
    const int min_hr = 40;

    /* ---- thresholds ---- */
    float dur_sec   = (float)WIN_SAMP_PPG / (float)FS_PPG;
    float max_beats = ((float)max_hr / 60.0f) * dur_sec;
    int   min_beats = (int)py_roundf_bankers(((float)min_hr / 60.0f) * dur_sec);
    float th_sg     = 4.0f * max_beats;

    /* ---- Hjorth-like metrics ---- */
    float activity_b = custom_var_unbiased_f(ws->buf_filt, WIN_SAMP_PPG);

    float mobility_b   = 0.0f;
    float complexity_b = 0.0f;

    if (activity_b == 0.0f) {
        mobility_b = 0.0f;
        complexity_b = 0.0f;
    } else {
        int dlen = custom_diff_f(ws->buf_filt, WIN_SAMP_PPG, ws->scratch1);

        float d1_var = custom_var_unbiased_f(ws->scratch1, dlen);
        if (d1_var <= 0.0f) {
            mobility_b = 0.0f;
            complexity_b = 0.0f;
        } else {
            mobility_b = sqrtf(d1_var / activity_b);

            if (mobility_b == 0.0f) {
                complexity_b = 0.0f;
            } else {
                int d2len = custom_diff_f(ws->scratch1, dlen, ws->scratch2);
                float d2_var = custom_var_unbiased_f(ws->scratch2, d2len);
                if (d2_var <= 0.0f) complexity_b = 0.0f;
                else complexity_b = sqrtf(d2_var / d1_var) / mobility_b;
            }
        }
    }

    float skew_b = custom_skewness_f(ws->buf_filt, WIN_SAMP_PPG);
    float kur_b  = custom_kurtosis_f_ws(ws->buf_filt, WIN_SAMP_PPG, ws->scratch1);

    float vals_b[3] = { skew_b, kur_b, complexity_b };
    float m_b = custom_mean_f(vals_b, 3);
    float s_b = custom_std_nan_omit_unbiased_f(vals_b, 3);

    float cv_b;
    if (m_b == 0.0f) cv_b = INFINITY;
    else cv_b = s_b / fabsf(m_b);

    /* ---- slope sign-change count ---- */
    int dppg_len = custom_diff_f(ws->buf_filt, WIN_SAMP_PPG, ws->scratch1);
    float sg_c_b = INFINITY;
    if (dppg_len >= 2) {
        int count = 0;
        for (int i = 0; i < dppg_len - 1; i++) {
            if (ws->scratch1[i] * ws->scratch1[i + 1] < 0.0f) count++;
        }
        sg_c_b = (float)count;
    }

    /* ---- peaks & onsets ---- */
    vpg_peak_onset_detection3_f(ws, ws->buf_filt);
    int n_peaks  = ws->n_peaks;
    int n_onsets = ws->n_onsets;

    /* ---- RR-based metrics from peaks ---- */
    float c_j = INFINITY;
    float p_j = INFINITY;

    if (n_peaks >= min_beats) {

        int rr_len = 0;
        for (int i = 0; i < n_peaks - 1; i++) {
            float diff_samp = (float)(ws->peaks[i + 1] - ws->peaks[i]);
            ws->scratch1[rr_len++] = diff_samp / (float)FS_PPG * 1000.0f; /* ms */
        }

        /* MATLAB: if any(RR<=0) OR numel(RR) < min_beats-1 => Inf */
        int bad = 0;
        for (int i = 0; i < rr_len; i++) {
            if (ws->scratch1[i] <= 0.0f) { bad = 1; break; }
        }

        if (!bad && rr_len >= (min_beats - 1) && rr_len >= 2) {

            int drr_len = 0;
            for (int i = 0; i < rr_len - 1; i++) {
                ws->scratch2[drr_len++] = fabsf(ws->scratch1[i + 1] - ws->scratch1[i]);
            }

            c_j = custom_prctile_f_ws(ws->scratch2, drr_len, 95.0f, ws->scratch2) /
                  custom_mean_f(ws->scratch1, rr_len);

            p_j = custom_max_f(ws->scratch1, rr_len) / custom_min_f(ws->scratch1, rr_len);
        }
    }

    /* ---- OO-based metrics from onsets ---- */
    float co_j = INFINITY;
    float po_j = INFINITY;

    if (n_onsets >= min_beats) {

        int oo_len = 0;
        for (int i = 0; i < n_onsets - 1; i++) {
            float diff_samp = (float)(ws->onsets[i + 1] - ws->onsets[i]);
            ws->scratch1[oo_len++] = diff_samp / (float)FS_PPG * 1000.0f; /* ms */
        }

        int bad = 0;
        for (int i = 0; i < oo_len; i++) {
            if (ws->scratch1[i] <= 0.0f) { bad = 1; break; }
        }

        if (!bad && oo_len >= (min_beats - 1) && oo_len >= 2) {

            int doo_len = 0;
            for (int i = 0; i < oo_len - 1; i++) {
                ws->scratch2[doo_len++] = fabsf(ws->scratch1[i + 1] - ws->scratch1[i]);
            }

            co_j = custom_prctile_f_ws(ws->scratch2, doo_len, 95.0f, ws->scratch2) /
                   custom_mean_f(ws->scratch1, oo_len);

            po_j = custom_max_f(ws->scratch1, oo_len) / custom_min_f(ws->scratch1, oo_len);
        }
    }

    /* ---- conditions ---- */
    int cond1 = (cv_b   < 1.0f);
    int cond2 = (sg_c_b < th_sg);
    int cond3 = (c_j    < 0.3f);
    int cond4 = (p_j    < 2.5f);
    int cond5 = (co_j   < 0.3f);
    int cond6 = (po_j   < 2.5f);

    return ((cond1 ? 1.0f : 0.0f) +
            (cond2 ? 1.0f : 0.0f) +
            (cond3 ? 1.0f : 0.0f) +
            (cond4 ? 1.0f : 0.0f) +
            (cond5 ? 1.0f : 0.0f) +
            (cond6 ? 1.0f : 0.0f)) / 6.0f;
}


int Acc_activity_f(ppg_workspace_f_t *ws)
{
    float s = 0.0f;
    for (int i = 0; i < WIN_SAMP_ACC; i++) {
        float enmo = ws->acc_vm[i] - 0.1f;
        if (enmo < 0.0f) enmo = 0.0f;
        s += enmo;
    }
    int si = (int)s;
    return (s > (float)si) ? (si + 1) : si;
}

void make_nan_features_f_ws(ppg_workspace_f_t *ws)
{
    ws->features = make_nan_features_f();
}

void feature_extraction_PPG_f(ppg_workspace_f_t *ws)
{
    float minv = custom_min_f(ws->buf_filt, WIN_SAMP_PPG);
    float maxv = custom_max_f(ws->buf_filt, WIN_SAMP_PPG);
    float denom = maxv - minv;

    if (denom == 0.0f) {
        for (int i = 0; i < WIN_SAMP_PPG; i++) ws->ppg_norm[i] = 0.0f;
    } else {
        for (int i = 0; i < WIN_SAMP_PPG; i++) ws->ppg_norm[i] = (ws->buf_filt[i] - minv) / denom;
    }

    vpg_peak_onset_detection3_f(ws, ws->ppg_norm);

    if (ws->n_peaks < 3 || ws->n_onsets < 3) { make_nan_features_f_ws(ws); return; }

    int ibi_len = 0;
    for (int i = 0; i < ws->n_peaks - 1; i++) {
        float d = (float)(ws->peaks[i + 1] - ws->peaks[i]);
        ws->ibi[ibi_len++] = d / (float)FS_PPG * 1000.0f;
    }

    int ibi_clean_len = 0;
    for (int i = 0; i < ibi_len; i++) {
        if (ws->ibi[i] >= 300.0f && ws->ibi[i] <= 2000.0f) ws->ibi_clean[ibi_clean_len++] = ws->ibi[i];
    }

    float ibi_mean = (ibi_clean_len > 0) ? custom_median_f_ws(ws->ibi_clean, ibi_clean_len, ws->scratch1) : NAN;

    float HR_mean = NAN, SDNN = NAN, RMSSD = NAN;
    if (ibi_clean_len >= 2) {
        for (int i = 0; i < ibi_clean_len; i++) ws->scratch1[i] = 60000.0f / ws->ibi_clean[i];
        float median_hr = custom_median_f_ws(ws->scratch1, ibi_clean_len, ws->scratch2);
        if (!isnan(median_hr)) HR_mean = floorf(median_hr);

        SDNN = custom_std_nan_omit_unbiased_f(ws->ibi_clean, ibi_clean_len);

        float sum_sq = 0.0f;
        int dnn_len = 0;
        for (int i = 0; i < ibi_clean_len - 1; i++) {
            float dnn = ws->ibi_clean[i + 1] - ws->ibi_clean[i];
            sum_sq += dnn * dnn;
            dnn_len++;
        }
        RMSSD = (dnn_len > 0) ? sqrtf(sum_sq / (float)dnn_len) : NAN;
    }

    int n_beats = ((ws->n_onsets - 1) < ws->n_peaks) ? (ws->n_onsets - 1) : ws->n_peaks;

    int rt_n=0, rs_n=0, pd_n=0, sa_n=0, pa_n=0, psk_n=0, pku_n=0;

    for (int i = 0; i < n_beats; i++) {
        int on1 = ws->onsets[i] - 1; if (on1 < 0) on1 = 0;
        int on2 = ws->onsets[i + 1] - 1; if (on2 < 0) on2 = 0;
        int pk  = ws->peaks[i] - 1; if (pk < 0) pk = 0;

        if (pk <= on1 || pk >= on2) continue;

        float t_rise_sec  = (float)(pk - on1) / (float)FS_PPG;
        float t_pulse_sec = (float)(on2 - on1) / (float)FS_PPG;
        if (t_rise_sec <= 0.0f || t_pulse_sec <= 0.0f) continue;

        int seg_sys_len = (pk - on1) + 1;
        for (int k = 0; k < seg_sys_len; k++) ws->scratch1[k] = ws->ppg_norm[on1 + k];

        int seg_pulse_len = (on2 - on1) + 1;
        for (int k = 0; k < seg_pulse_len; k++) ws->scratch2[k] = ws->ppg_norm[on1 + k];

        ws->rise_time[rt_n++] = t_rise_sec * 1000.0f;

        float amp_rise = ws->ppg_norm[pk] - ws->ppg_norm[on1];
        ws->rise_slope[rs_n++] = amp_rise / t_rise_sec;

        ws->pulse_dur[pd_n++] = t_pulse_sec * 1000.0f;

        ws->systolic_area[sa_n++] = custom_trapz_f(ws->scratch1, seg_sys_len) / (float)FS_PPG;
        ws->ppg_area[pa_n++]      = custom_trapz_f(ws->scratch2, seg_pulse_len) / (float)FS_PPG;

        ws->pulse_sk[psk_n++]   = custom_skewness_f(ws->scratch2, seg_pulse_len);
        ws->pulse_kurt[pku_n++] = custom_kurtosis_f_ws(ws->scratch2, seg_pulse_len, ws->scratch1);
    }

    if (rt_n == 0) { make_nan_features_f_ws(ws); return; }

    ws->features.HR_mean = HR_mean;
    ws->features.SDNN = SDNN;
    ws->features.RMSSD = RMSSD;
    ws->features.ibi_mean = ibi_mean;

    ws->features.rise_time_ms_mean  = custom_median_f_ws(ws->rise_time, rt_n, ws->scratch1);
    ws->features.rise_slope_mean    = custom_median_f_ws(ws->rise_slope, rs_n, ws->scratch1);
    ws->features.pulse_dur_ms_mean  = custom_median_f_ws(ws->pulse_dur, pd_n, ws->scratch1);
    ws->features.systolic_area_mean = custom_median_f_ws(ws->systolic_area, sa_n, ws->scratch1);
    ws->features.ppg_area_mean      = custom_median_f_ws(ws->ppg_area, pa_n, ws->scratch1);
    ws->features.pulse_skew_mean    = custom_median_f_ws(ws->pulse_sk, psk_n, ws->scratch1);
    ws->features.pulse_kurt_mean    = custom_median_f_ws(ws->pulse_kurt, pku_n, ws->scratch1);
}
