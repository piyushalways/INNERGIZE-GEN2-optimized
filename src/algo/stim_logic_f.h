#ifndef STIM_LOGIC_F_H
#define STIM_LOGIC_F_H

#include "ppg_workspace_f.h"

/* init baseline state */
void stim_state_init_f(ppg_workspace_f_t *ws);

/* collect HR into baseline until baseline becomes ready (mean/sd computed once) */
void stim_baseline_update_f(ppg_workspace_f_t *ws, float sqi, int activity, float hr);

/* compute z-score and decide STIM/NO STIM (only when baseline ready) */
void stim_decide_f(ppg_workspace_f_t *ws, float sqi, int activity, float hr);

#endif /* STIM_LOGIC_F_H */
