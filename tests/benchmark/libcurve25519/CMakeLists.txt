project(libcurve25519 LANGUAGES C ASM)
cmake_minimum_required(VERSION 3.5)

set(LIBCURVE25519_SRC_DIR ${CMAKE_CURRENT_SOURCE_DIR} CACHE PATH "Where to find the library of Curve25519 implementations.")
get_filename_component(LIBCURVE25519_SRC_DIR ${LIBCURVE25519_SRC_DIR} ABSOLUTE)
message("-- Using Curve25519 implementations at ${LIBCURVE25519_SRC_DIR}")

add_library(libcurve25519 SHARED STATIC
  curve25519-donna64.c
  curve25519-evercrypt64.c
  curve25519-fiat64.c
  curve25519-hacl51.c
  curve25519-openssl.c
  curve25519-precomp.c)
target_include_directories(libcurve25519 PUBLIC ${LIBCURVE25519_SRC_DIR})

if(NOT CMAKE_SYSTEM_NAME STREQUAL "CYGWIN")
target_sources(libcurve25519 PRIVATE
  curve25519-amd64.c
  curve25519-amd64-asm.S)
endif()

if(CMAKE_SYSTEM_NAME STREQUAL "Darwin")
elseif(CMAKE_SYSTEM_NAME STREQUAL "Linux")
  target_compile_options(libcurve25519 PRIVATE -fPIC -fstack-check)
  target_link_libraries(libcurve25519 PRIVATE "-Xlinker -z -Xlinker noexecstack" "-Xlinker --unresolved-symbols=report-all")
elseif(CMAKE_SYSTEM_NAME STREQUAL "CYGWIN")
  # target_compile_options(libcurve25519 PRIVATE -fno-asynchronous-unwind-tables)
endif()

if(ASAN)
  target_compile_options(libcurve25519 PRIVATE -g -fsanitize=undefined,address -fno-omit-frame-pointer -fno-sanitize-recover=all -fno-sanitize=function)
  target_link_libraries(libcurve25519 PRIVATE -g -fsanitize=address)
endif()