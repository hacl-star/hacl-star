project(fiat-curve25519 LANGUAGES C ASM)
cmake_minimum_required(VERSION 3.5)

set(FIAT_CURVE25519_SRC_DIR ${CMAKE_CURRENT_SOURCE_DIR} CACHE PATH "Where to find the Fiat Curve25519 sources.")
get_filename_component(FIAT_CURVE25519_SRC_DIR ${FIAT_CURVE25519_SRC_DIR} ABSOLUTE)
message("-- Using Fiat Curve25519 at ${FIAT_CURVE25519_SRC_DIR}")

add_library(fiat-curve25519 SHARED STATIC
  ${FIAT_CURVE25519_SRC_DIR}/femul.c
  ${FIAT_CURVE25519_SRC_DIR}/fesquare.c
  ${FIAT_CURVE25519_SRC_DIR}/freeze.c
  ${FIAT_CURVE25519_SRC_DIR}/ladderstep.c
  ${FIAT_CURVE25519_SRC_DIR}/scalarmult.c
  ${FIAT_CURVE25519_SRC_DIR}/liblow/cmovznz.c)
target_compile_options(fiat-curve25519 PRIVATE -Wno-parentheses -std=gnu11 -Wno-attributes -Wno-implicit-function-declaration)
target_include_directories(fiat-curve25519 PUBLIC ${FIAT_CURVE25519_SRC_DIR} ${FIAT_CURVE25519_SRC_DIR}/liblow)

if(CMAKE_SYSTEM_NAME STREQUAL "Darwin")
elseif(CMAKE_SYSTEM_NAME STREQUAL "Linux")
  target_compile_options(fiat-curve25519 PRIVATE -fPIC -fstack-check)
  target_link_libraries(fiat-curve25519 PRIVATE "-Xlinker -z -Xlinker noexecstack" "-Xlinker --unresolved-symbols=report-all")
elseif(CMAKE_SYSTEM_NAME STREQUAL "CYGWIN")
  target_compile_options(fiat-curve25519 PRIVATE -fno-asynchronous-unwind-tables)
endif()

if(ASAN)
  target_compile_options(fiat-curve25519 PRIVATE -g -fsanitize=undefined,address -fno-omit-frame-pointer -fno-sanitize-recover=all -fno-sanitize=function)
  target_link_libraries(fiat-curve25519 PRIVATE -g -fsanitize=address)
endif()
