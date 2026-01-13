#ifndef APP_DATA_TYPES_H
#define APP_DATA_TYPES_H

#include <stdint.h>

typedef struct{
    uint32_t on_time;
    uint32_t interval;
}ems_chan_data_t;

typedef struct{

    uint8_t control;

    struct{
        uint32_t current_session_len;
        uint32_t target_session_len;
    }session;

    uint32_t period;
    uint32_t ontime;
    uint32_t interval;
    uint32_t duration;
    uint32_t chan0playback;
    uint32_t chan0inductor;
    uint32_t chan0ontime;
    uint32_t chan0time;
    uint64_t pwm23time;
    uint64_t pwm23ontime;
    uint32_t chargeronoff;

}ems_status_data_t;


struct pwm_channel_data{
    struct{
        uint32_t on_time;
        uint32_t off_time;
    }chan0;

    ems_chan_data_t chan1; // On/off time in nanoseconds
    
    struct{
        uint8_t duty_cycle;
    }chan2;
    
    struct{
        uint8_t duty_cycle;
    }chan3;
};

struct ems_def{
    struct pwm_channel_data channels;
    ems_status_data_t status;  
};

struct ems_mode_data{
    struct pwm_channel_data pwm;
};

struct ems_intensity{
    ems_status_data_t intensit;
};

#endif