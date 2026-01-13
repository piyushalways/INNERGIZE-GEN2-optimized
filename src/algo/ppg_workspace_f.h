#ifndef PPG_WORKSPACE_F_H
#define PPG_WORKSPACE_F_H

#include <stdint.h>
#include <math.h>

/* =============================
   Sampling + Window
   ============================= */
#ifndef FS_PPG
#define FS_PPG 40
#endif

#ifndef FS_ACC
#define FS_ACC 10
#endif

#ifndef WIN_SEC
#define WIN_SEC 10
#endif

#ifndef STEP_SEC
#define STEP_SEC 1
#endif


#define WIN_SAMP_PPG (WIN_SEC * FS_PPG)   /* e.g., 400 when WIN_SEC=10 and FS_PPG=40 */
#define WIN_SAMP_ACC (WIN_SEC * FS_ACC)   /* e.g., 100 when WIN_SEC=10 and FS_ACC=10 */

/* =============================
   IIR filtfilt padding
   ============================= */
/* Filter order = 8 => M=9 coefficients => pad_len = 3*(M-1)=24 */
#define FILT_M          9
#define FILT_PAD_LEN    (3 * (FILT_M - 1))  /* 24 */

/* Padded length = N + 2*pad */
#define XP_LEN          (WIN_SAMP_PPG + 2 * FILT_PAD_LEN)

/* =============================
   Peak / Onset detection sizes
   ============================= */
#ifndef MAX_PEAKS
#define MAX_PEAKS 150
#endif

#ifndef MAX_ONSETS
#define MAX_ONSETS 150
#endif

#ifndef MAX_CAND
#define MAX_CAND 300
#endif

/* =============================
   STIM decision configuration
   ============================= */


#define SQI_THR_BASELINE   0.75f
#define ACT_THR_BASELINE   1
#define Z_THR_STIM        -0.3f

#define BASELINE_MINUTES   5
#define BASELINE_TARGET_SAMPLES ((BASELINE_MINUTES * 60) / STEP_SEC)

#ifndef MAX_BASELINE_SAMPLES
#define MAX_BASELINE_SAMPLES BASELINE_TARGET_SAMPLES
#endif

typedef struct {
    float HR_mean;
    float SDNN;
    float RMSSD;
    float ibi_mean;
    float rise_time_ms_mean;
    float rise_slope_mean;
    float pulse_dur_ms_mean;
    float systolic_area_mean;
    float ppg_area_mean;
    float pulse_skew_mean;
    float pulse_kurt_mean;
} FeaturesF;

typedef struct {
    /* baseline collection */
    int   baseline_ready;                   /* 0/1 */
    int   baseline_count;                   /* collected HR count */
    int   baseline_target;                  /* required HR count */
    float hr_baseline[MAX_BASELINE_SAMPLES];

    /* baseline stats (computed once after baseline completes) */
    float baseline_mean;
    float baseline_sd;

    /* latest decision */
    float z_hr;
    int   stim;                             /* 1=STIM, 0=NO_STIM */
} StimStateF;

typedef struct {
    /* =============================
       INPUT WINDOWS
       ============================= */
    float buf_ppg[WIN_SAMP_PPG];
    float acc_x[WIN_SAMP_ACC];
    float acc_y[WIN_SAMP_ACC];
    float acc_z[WIN_SAMP_ACC];

    /* =============================
       ACC PROCESSING
       ============================= */
    float acc_vm[WIN_SAMP_ACC];     /* vector magnitude after detrend+scale */

    /* =============================
       PREPROCESS OUTPUT
       ============================= */
    float buf_filt[WIN_SAMP_PPG];   /* final filtered PPG */

    /* =============================
       FILTER SCRATCH (REDUCED)
       ============================= */
    float xp[XP_LEN];               /* mirror-padded signal */
    float tmp[XP_LEN];              /* reused for forward/reverse passes */

    /* =============================
       PEAK / ONSET
       ============================= */
    float vpg[WIN_SAMP_PPG];        /* derivative */
    int   peaks[MAX_PEAKS];         /* 1-based indices */
    int   onsets[MAX_ONSETS];       /* 1-based indices */
    int   n_peaks;
    int   n_onsets;
    int   vpg_len;

    /* =============================
       FEATURE EXTRACTION BUFFERS
       ============================= */
    float ppg_norm[WIN_SAMP_PPG];   /* normalized signal for morphology */

    float ibi[MAX_PEAKS];
    float ibi_clean[MAX_PEAKS];

    float rise_time[MAX_PEAKS];
    float rise_slope[MAX_PEAKS];
    float pulse_dur[MAX_PEAKS];
    float systolic_area[MAX_PEAKS];
    float ppg_area[MAX_PEAKS];
    float pulse_sk[MAX_PEAKS];
    float pulse_kurt[MAX_PEAKS];

    /* =============================
       GENERAL SCRATCH (REDUCED)
       ============================= */
    float scratch1[WIN_SAMP_PPG];
    float scratch2[WIN_SAMP_PPG];

    /* =============================
       OUTPUT FEATURES
       ============================= */
    FeaturesF features;

    /* =============================
       STIM DECISION STATE
       ============================= */
    StimStateF stim_state;

} ppg_workspace_f_t;

#endif /* PPG_WORKSPACE_F_H */
