#include <math.h>

#include "stim_logic_f.h"
#include "utility_f.h"   /* custom_mean_f, custom_std_nan_omit_unbiased_f */

void stim_state_init_f(ppg_workspace_f_t *ws)
{
    ws->stim_state.baseline_ready  = 0;
    ws->stim_state.baseline_count  = 0;
    ws->stim_state.baseline_target = BASELINE_TARGET_SAMPLES;

    ws->stim_state.baseline_mean = 0.0f;
    ws->stim_state.baseline_sd   = 0.0f;

    ws->stim_state.z_hr = 0.0f;
    ws->stim_state.stim = 0;

    for (int i = 0; i < MAX_BASELINE_SAMPLES; i++) {
        ws->stim_state.hr_baseline[i] = NAN;
    }
}

void stim_baseline_update_f(ppg_workspace_f_t *ws, float sqi, int activity, float hr)
{
    if (ws->stim_state.baseline_ready) return;

    /* baseline gate */
    if (!(sqi >= SQI_THR_BASELINE && activity < ACT_THR_BASELINE)) return;

    if (ws->stim_state.baseline_count < ws->stim_state.baseline_target &&
        ws->stim_state.baseline_count < MAX_BASELINE_SAMPLES) {

        ws->stim_state.hr_baseline[ws->stim_state.baseline_count++] = hr;
    }

    /* finalize baseline once enough HR samples collected */
    if (ws->stim_state.baseline_count >= ws->stim_state.baseline_target) {

        float mean = custom_mean_f(ws->stim_state.hr_baseline,
                                   ws->stim_state.baseline_count);

        float sd = custom_std_nan_omit_unbiased_f(ws->stim_state.hr_baseline,
                                                  ws->stim_state.baseline_count);

        /* safety: std must be finite and non-zero */
        if (!isfinite(sd) || sd < 1e-6f) {
            sd = 1e-6f;
        }

        ws->stim_state.baseline_mean  = mean;
        ws->stim_state.baseline_sd    = sd;
        ws->stim_state.baseline_ready = 1;

        ws->stim_state.z_hr = 0.0f;
        ws->stim_state.stim = 0;
    }
}

void stim_decide_f(ppg_workspace_f_t *ws, float sqi, int activity, float hr)
{
    ws->stim_state.stim = 0;
    ws->stim_state.z_hr = 0.0f;

    if (!ws->stim_state.baseline_ready) return;

    /* decision gate */
    if (!(sqi >= SQI_THR_BASELINE && activity < ACT_THR_BASELINE)) return;

    float z = (hr - ws->stim_state.baseline_mean) / ws->stim_state.baseline_sd;
    ws->stim_state.z_hr = z;

    if (z < Z_THR_STIM) ws->stim_state.stim = 1;
}
