#ifndef CORE_MODULES_F_H
#define CORE_MODULES_F_H

#include "ppg_workspace_f.h"
#include "utility_f.h"

#ifdef __cplusplus
extern "C" {
#endif

void  acc_prepare_vm_f(ppg_workspace_f_t *ws);
void  preprocess_ppg_f(ppg_workspace_f_t *ws);

float SQI_PPG_f(ppg_workspace_f_t *ws);
int   Acc_activity_f(ppg_workspace_f_t *ws);

void  feature_extraction_PPG_f(ppg_workspace_f_t *ws);
void  make_nan_features_f_ws(ppg_workspace_f_t *ws);

#ifdef __cplusplus
}
#endif

#endif
