project(evercrypt LANGUAGES C ASM)
cmake_minimum_required(VERSION 3.5)

if (NOT EVERCRYPT_SRC_DIR)
  set(EVERCRYPT_SRC_DIR ${CMAKE_CURRENT_SOURCE_DIR}/../../../dist/compact-gcc CACHE PATH "Where to find the EverCrypt sources.")
endif()
get_filename_component(EVERCRYPT_SRC_DIR ${EVERCRYPT_SRC_DIR} ABSOLUTE)
message("-- Using EverCrypt at ${EVERCRYPT_SRC_DIR}")

include(${CMAKE_CURRENT_SOURCE_DIR}/../libkremlib/CMakeLists.txt)

add_library(evercrypt STATIC
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
  ${EVERCRYPT_SRC_DIR}/Hacl_Poly1305_32.c
  ${EVERCRYPT_SRC_DIR}/Hacl_Poly1305_128.c
  ${EVERCRYPT_SRC_DIR}/Hacl_Poly1305_256.c
  ${EVERCRYPT_SRC_DIR}/Hacl_SHA3.c
  ${EVERCRYPT_SRC_DIR}/Lib_PrintBuffer.c
  ${EVERCRYPT_SRC_DIR}/Lib_RandomBuffer.c)
target_compile_options(evercrypt PRIVATE -Wno-parentheses -std=gnu11)
target_include_directories(evercrypt PUBLIC ${EVERCRYPT_SRC_DIR})

if(CMAKE_SYSTEM_PROCESSOR STREQUAL "x86_64")
  if(CMAKE_COMPILER_IS_MSVC)
  set(VARIANT "msvc.asm")
  elseif(CMAKE_SYSTEM_NAME STREQUAL "CYGWIN")
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
endif()

if(EXISTS ${EVERCRYPT_SRC_DIR}/MerkleTree.c)
  target_sources(evercrypt PRIVATE ${EVERCRYPT_SRC_DIR}/MerkleTree.c)
endif()
if(EXISTS ${EVERCRYPT_SRC_DIR}/LowStar.c)
  target_sources(evercrypt PRIVATE ${EVERCRYPT_SRC_DIR}/LowStar.c)
endif()

if(CMAKE_SYSTEM_NAME STREQUAL "Darwin")
elseif(CMAKE_SYSTEM_NAME STREQUAL "Linux")
  target_compile_options(evercrypt PRIVATE -fPIC -fstack-check)
  target_link_libraries(evercrypt PRIVATE "-Xlinker -z -Xlinker noexecstack" "-Xlinker --unresolved-symbols=report-all")
elseif(CMAKE_SYSTEM_NAME STREQUAL "CYGWIN")
  target_compile_options(evercrypt PRIVATE -fno-asynchronous-unwind-tables)
endif()

# Hacl_Poly1305_128.o: CFLAGS += -mavx
# Hacl_Poly1305_256.o: CFLAGS += -mavx -mavx2
set_source_files_properties(${EVERCRYPT_SRC_DIR}/Hacl_Poly1305_128.c PROPERTIES COMPILE_FLAGS "-mavx")
set_source_files_properties(${EVERCRYPT_SRC_DIR}/Hacl_Poly1305_256.c PROPERTIES COMPILE_FLAGS "-mavx -mavx2")

target_link_libraries(evercrypt PUBLIC kremlib)

if(ASAN)
target_compile_options(evercrypt PRIVATE -g -fsanitize=undefined,address -fno-omit-frame-pointer -fno-sanitize-recover=all -fno-sanitize=function)
target_link_libraries(evercrypt PRIVATE -g -fsanitize=address)
endif()
