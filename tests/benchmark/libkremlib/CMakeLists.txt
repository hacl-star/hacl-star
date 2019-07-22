project(libkremlib LANGUAGES C ASM)
cmake_minimum_required(VERSION 3.5)

if (NOT KREMLIB_DIR)
  set(KREMLIB_DIR $ENV{KREMLIN_HOME}/kremlib/dist/generic CACHE PATH "Where to find the KreMLib sources.")
endif()
get_filename_component(KREMLIB_DIR ${KREMLIB_DIR} REALPATH)
message("-- Using KreMLib sources at ${KREMLIB_DIR}")

if (NOT KREMLIN_INC)
  set(KREMLIN_INC $ENV{KREMLIN_HOME}/include CACHE PATH "Where to find the KreMLin headers.")
endif()
get_filename_component(KREMLIN_INC ${KREMLIN_INC} REALPATH)
message("-- Using KreMLin at ${KREMLIN_INC}")

add_library(kremlib STATIC
  ${KREMLIB_DIR}/c.c
  ${KREMLIB_DIR}/c_string.c
  ${KREMLIB_DIR}/FStar_BitVector.c
  ${KREMLIB_DIR}/fstar_bytes.c
  ${KREMLIB_DIR}/fstar_char.c
  ${KREMLIB_DIR}/fstar_date.c
  ${KREMLIB_DIR}/fstar_dyn.c
  ${KREMLIB_DIR}/fstar_hyperstack_io.c
  ${KREMLIB_DIR}/fstar_int16.c
  ${KREMLIB_DIR}/fstar_int32.c
  ${KREMLIB_DIR}/fstar_int64.c
  ${KREMLIB_DIR}/fstar_int8.c
  ${KREMLIB_DIR}/fstar_io.c
  ${KREMLIB_DIR}/FStar_ModifiesGen.c
  ${KREMLIB_DIR}/FStar_Order.c
  ${KREMLIB_DIR}/fstar_string.c
  ${KREMLIB_DIR}/fstar_uint16.c
  ${KREMLIB_DIR}/fstar_uint32.c
  ${KREMLIB_DIR}/fstar_uint64.c
  ${KREMLIB_DIR}/FStar_UInt_8_16_32_64.c
  ${KREMLIB_DIR}/fstar_uint8.c
  ${KREMLIB_DIR}/prims.c
  ${KREMLIB_DIR}/testlib.c)
target_include_directories(kremlib PUBLIC ${KREMLIN_INC} ${KREMLIB_DIR})
target_compile_options(kremlib PRIVATE
  -std=c11 -fwrapv
  -Wall -Wextra -Werror
  -Wno-unused-variable -Wno-unused-but-set-variable -Wno-unknown-warning-option
  -Wno-infinite-recursion -Wno-unused-parameter
  )
target_compile_definitions(kremlib PRIVATE _BSD_SOURCE _DEFAULT_SOURCE)

if(CMAKE_SYSTEM_NAME STREQUAL "CYGWIN")
  target_compile_definitions(kremlib PUBLIC __USE_MINGW_ANSI_STDIO)
else()
  target_compile_options(kremlib PUBLIC -fPIC)
endif()

if(CMAKE_COMPILER_IS_MSVC)
  target_sources(kremlib PRIVATE ${KREMLIB_DIR}/fstar_uint128_msvc.c)
else(CMAKE_COMPILER_IS_MSVC)
  target_sources(kremlib PRIVATE ${KREMLIB_DIR}/fstar_uint128.c)
endif(CMAKE_COMPILER_IS_MSVC)

if(ASAN)
  target_compile_options(kremlib PRIVATE -g -fsanitize=undefined,address -fno-omit-frame-pointer -fno-sanitize-recover=all -fno-sanitize=function)
  target_link_libraries(kremlib PRIVATE -g -fsanitize=address)
endif()
