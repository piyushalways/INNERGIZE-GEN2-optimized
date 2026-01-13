# SPDX-License-Identifier: Apache-2.0

cmake_minimum_required(VERSION 3.20.0)

list(APPEND BOARD_ROOT ${CMAKE_CURRENT_SOURCE_DIR})

set(SHIELD npm1300_ek)

find_package(Zephyr REQUIRED HINTS $ENV{ZEPHYR_BASE})
project(adc_dt_1)


target_include_directories(app PRIVATE
    ${CMAKE_CURRENT_SOURCE_DIR}/src
    ${CMAKE_CURRENT_SOURCE_DIR}/src/drivers/bma580
    ${CMAKE_CURRENT_SOURCE_DIR}/src/drivers/as7058
    ${CMAKE_CURRENT_SOURCE_DIR}/src/drivers/npm1300
    ${CMAKE_CURRENT_SOURCE_DIR}/src/algo
    ${CMAKE_CURRENT_SOURCE_DIR}/src/ble

)

file(GLOB_RECURSE app_sources
    src/*.c
)

target_sources(app PRIVATE ${app_sources})


# If you also have headers:
# set_target_properties(mylib PROPERTIES INTERFACE_INCLUDE_DIRECTORIES
#     ${CMAKE_CURRENT_SOURCE_DIR}/include
# )