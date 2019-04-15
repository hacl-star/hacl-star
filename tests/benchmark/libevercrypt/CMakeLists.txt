project(evercrypt LANGUAGES C ASM)
cmake_minimum_required(VERSION 3.12)

set(EVERCRYPT_SRC_DIR ${CMAKE_CURRENT_SOURCE_DIR}/../../../dist/compact-c89 CACHE PATH "Where to find the EverCrypt sources.")
message("-- Using EverCrypt at ${EVERCRYPT_SRC_DIR}")

include(${CMAKE_CURRENT_SOURCE_DIR}/../libkremlib/CMakeLists.txt)

add_library(evercrypt SHARED)
target_compile_options(evercrypt PRIVATE -Wno-parentheses -std=gnu11 -march=native -mtune=native)
target_include_directories(evercrypt PUBLIC ${EVERCRYPT_SRC_DIR})

target_sources(evercrypt PRIVATE
  ${EVERCRYPT_SRC_DIR}/EverCrypt_AEAD.c
  ${EVERCRYPT_SRC_DIR}/EverCrypt_AutoConfig2.c
  ${EVERCRYPT_SRC_DIR}/EverCrypt_Chacha20Poly1305.c
  ${EVERCRYPT_SRC_DIR}/EverCrypt_Cipher.c
  ${EVERCRYPT_SRC_DIR}/EverCrypt_Curve25519.c
  ${EVERCRYPT_SRC_DIR}/EverCrypt_Error.c
  ${EVERCRYPT_SRC_DIR}/EverCrypt_Hash.c
  ${EVERCRYPT_SRC_DIR}/EverCrypt_HKDF.c
  ${EVERCRYPT_SRC_DIR}/EverCrypt_HMAC.c
  ${EVERCRYPT_SRC_DIR}/EverCrypt_Poly1305.c
  ${EVERCRYPT_SRC_DIR}/EverCrypt_StaticConfig.c
  ${EVERCRYPT_SRC_DIR}/EverCrypt_Vale.c
  ${EVERCRYPT_SRC_DIR}/evercrypt_vale_stubs.c
  ${EVERCRYPT_SRC_DIR}/Hacl_AES.c
  ${EVERCRYPT_SRC_DIR}/Hacl_Chacha20.c
  ${EVERCRYPT_SRC_DIR}/Hacl_Chacha20Poly1305.c
  ${EVERCRYPT_SRC_DIR}/Hacl_Curve25519.c
  ${EVERCRYPT_SRC_DIR}/Hacl_Ed25519.c
  ${EVERCRYPT_SRC_DIR}/Hacl_Hash.c
  ${EVERCRYPT_SRC_DIR}/Hacl_Kremlib.c
  ${EVERCRYPT_SRC_DIR}/Hacl_Poly1305.c
  ${EVERCRYPT_SRC_DIR}/Hacl_SHA3.c
  ${EVERCRYPT_SRC_DIR}/Lib_PrintBuffer.c
  ${EVERCRYPT_SRC_DIR}/Lib_RandomBuffer.c
  ${EVERCRYPT_SRC_DIR}/Vale.c
)

if(${CMAKE_SYSTEM_PROCESSOR} STREQUAL "x86_64")
  if(CMAKE_COMPILER_IS_MSVC)
  set(VARIANT "msvc.asm")
  elseif(WIN32)
  set(VARIANT "mingw.S")
  elseif(APPLE)
  set(VARIANT "darwin.S")
  else(CMAKE_COMPILER_IS_MSVC)
  set(VARIANT "linux.S")
  endif(CMAKE_COMPILER_IS_MSVC)

  target_sources(evercrypt PRIVATE
    ${EVERCRYPT_SRC_DIR}/aes-x86_64-${VARIANT}
    ${EVERCRYPT_SRC_DIR}/aesgcm-x86_64-${VARIANT}
    ${EVERCRYPT_SRC_DIR}/cpuid-x86_64-${VARIANT}
    ${EVERCRYPT_SRC_DIR}/curve25519-x86_64-${VARIANT}
    ${EVERCRYPT_SRC_DIR}/poly1305-x86_64-${VARIANT}
    ${EVERCRYPT_SRC_DIR}/sha256-x86_64-${VARIANT})
endif(${CMAKE_SYSTEM_PROCESSOR} STREQUAL "x86_64")

if(${CMAKE_SYSTEM_NAME} STREQUAL "Linux")
  target_compile_options(evercrypt PUBLIC -fPIC -fstack-check)
  # target_link_libraries(evercrypt PUBLIC -Xlinker -z -Xlinker noexecstack -Xlinker --unresolved-symbols=report-all)
endif(${CMAKE_SYSTEM_NAME} STREQUAL "Linux")

# Hacl_Poly1305.o: CFLAGS += -mavx -mavx2
set_source_files_properties(${EVERCRYPT_SRC_DIR}/Hacl_Poly1305.c
    PROPERTIES COMPILE_FLAGS "-mavx -mavx2"
)

target_link_libraries(evercrypt PUBLIC kremlib)