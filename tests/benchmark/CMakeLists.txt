project(benchmark LANGUAGES C CXX ASM)
cmake_minimum_required(VERSION 3.6)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
set(CMAKE_LEGACY_CYGWIN_WIN32 0) # Remove when CMake >= 3.8.4 is required

option(USE_HACL "Use HaCl." ON)
option(USE_VALE "Use Vale." ON)
option(USE_BCRYPT "Use BCrypt." OFF)
option(USE_OPENSSL "Use OpenSSL." ON)
option(USE_RFC7748 "Use the RFC 7748 reference implementation" ON)

option(ASAN "Enable clang address sanitizer" OFF)

add_subdirectory(libevercrypt)

add_library(benchmark STATIC benchmark.cpp)
target_include_directories(benchmark PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(benchmark PRIVATE evercrypt)

add_executable(runbenchmark
  runbenchmark.cpp
  bench_hash.cpp
  bench_aead.cpp
  bench_curve25519.cpp
  bench_ed25519.cpp
  bench_merkle.cpp)
target_include_directories(runbenchmark PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(runbenchmark PRIVATE benchmark evercrypt)

if("${CMAKE_BUILD_TYPE}" STREQUAL "Debug")
  target_compile_definitions(benchmark PRIVATE _DEBUG)
  target_compile_definitions(runbenchmark PRIVATE _DEBUG)
endif()

if(USE_HACL)
  message("-- Using HaCl (via EverCrypt)")
  target_compile_definitions(runbenchmark PRIVATE HAVE_HACL)
endif(USE_HACL)

if(USE_VALE)
  message("-- Using Vale (via EverCrypt)")
  target_compile_definitions(runbenchmark PRIVATE HAVE_VALE)
endif(USE_VALE)

if(USE_BCRYPT)
  SET(CMAKE_FIND_LIBRARY_SUFFIXES ".dll")
  find_library(BCRYPT_LIB bcrypt.dll)
  find_path(BCRYPT_INC bcrypt.h)
  message("-- Using BCrypt at ${BCRYPT_LIB} with headers at ${BCRYPT_INC}")
  target_compile_definitions(runbenchmark PRIVATE HAVE_BCRYPT)
  target_link_libraries(runbenchmark PRIVATE ${BCRYPT_LIB})
  target_include_directories(runbenchmark PRIVATE ${BCRYPT_INC})
endif(USE_BCRYPT)

if(USE_OPENSSL)
  find_library(OPENSSL_LIB libcrypto.a PATHS $ENV{MLCRYPTO_HOME}/openssl NO_DEFAULT_PATH)
  find_library(OPENSSL_LIB libcrypto.a) # search default paths
  find_path(OPENSSL_INC openssl/crypto.h PATHS $ENV{MLCRYPTO_HOME}/openssl/include NO_DEFAULT_PATH)
  find_path(OPENSSL_INC openssl/crypto.h) # search default paths
  message("-- Using OpenSSL at ${OPENSSL_LIB} with headers at ${OPENSSL_INC}")
  target_compile_definitions(runbenchmark PRIVATE HAVE_OPENSSL)
  target_link_libraries(runbenchmark PRIVATE ${OPENSSL_LIB})
  target_include_directories(runbenchmark PRIVATE ${OPENSSL_INC})
  if(NOT ${CMAKE_SYSTEM_NAME} STREQUAL "Windows")
    target_link_libraries(runbenchmark PRIVATE dl pthread)
  endif(NOT ${CMAKE_SYSTEM_NAME} STREQUAL "Windows")
endif(USE_OPENSSL)

if(USE_RFC7748)
  add_subdirectory(librfc7748)
  target_compile_definitions(runbenchmark PRIVATE HAVE_RFC7748)
  target_link_libraries(runbenchmark PRIVATE rfc7748)
  target_include_directories(runbenchmark PRIVATE ${RFC7748_DIR})
endif(USE_RFC7748)

if(ASAN)
  target_compile_options(benchmark PRIVATE -g -fsanitize=undefined,address -fno-omit-frame-pointer -fno-sanitize-recover=all -fno-sanitize=function)
  target_link_libraries(benchmark PRIVATE -g -fsanitize=address)
  target_compile_options(runbenchmark PRIVATE -g -fsanitize=undefined,address -fno-omit-frame-pointer -fno-sanitize-recover=all -fno-sanitize=function)
  target_link_libraries(runbenchmark PRIVATE -g -fsanitize=address)
endif()

# set(KERNEL_DIR /usr/src/linux-headers-4.15.0-47-generic)
# target_sources(runbenchmark PRIVATE curve25519-fiat64.c)
# set_source_files_properties(curve25519-fiat64.c PROPERTIES COMPILE_FLAGS
#   "-nostdinc -isystem /usr/lib/gcc/x86_64-linux-gnu/7/include  -I${KERNEL_DIR}/curve25519_fiat64arch/x86/include -I${KERNEL_DIR}/arch/x86/include/generated  -I${KERNEL_DIR}/include -I${KERNEL_DIR}/arch/x86/include/uapi -I${KERNEL_DIR}/arch/x86/include/generated/uapi -I${KERNEL_DIR}/include/uapi -I${KERNEL_DIR}/include/generated/uapi -include ${KERNEL_DIR}/include/linux/kconfig.h -Iubuntu/include "
#   "-D__KERNEL__ -Wall -Wundef -Wstrict-prototypes -Wno-trigraphs -fno-strict-aliasing -fno-common -fshort-wchar "
#   "-Werror-implicit-function-declaration -Wno-format-security -std=gnu89 -fno-PIE -mno-sse -mno-mmx -mno-sse2 -mno-3dnow -mno-avx -m64 -falign-jumps=1 -falign-loops=1 -mno-80387 -mno-fp-ret-in-387 -mpreferred-stack-boundary=3 -mskip-rax-setup -mtune=generic -mno-red-zone -mcmodel=kernel -funit-at-a-time "
#   "-DCONFIG_X86_X32_ABI -DCONFIG_AS_CFI=1 -DCONFIG_AS_CFI_SIGNAL_FRAME=1 -DCONFIG_AS_CFI_SECTIONS=1 -DCONFIG_AS_FXSAVEQ=1 -DCONFIG_AS_SSSE3=1 -DCONFIG_AS_CRC32=1 -DCONFIG_AS_AVX=1 -DCONFIG_AS_AVX2=1 -DCONFIG_AS_AVX512=1 -DCONFIG_AS_SHA1_NI=1 -DCONFIG_AS_SHA256_NI=1 -pipe "
#   "-Wno-sign-compare -fno-asynchronous-unwind-tables -mindirect-branch=thunk-extern -mindirect-branch-register -DRETPOLINE -fno-delete-null-pointer-checks -Wno-frame-address -Wno-format-truncation -Wno-format-overflow -Wno-int-in-bool-context -O2 --param=allow-store-data-races=0 -DCC_HAVE_ASM_GOTO -Wframe-larger-than=1024 "
#   "-fstack-protector-strong -Wno-unused-but-set-variable -Wno-unused-const-variable -fno-omit-frame-pointer -fno-optimize-sibling-calls -fno-var-tracking-assignments -pg -mfentry -DCC_USING_FENTRY -Wdeclaration-after-statement -Wno-pointer-sign -fno-strict-overflow -fno-merge-all-constants -fmerge-constants -fno-stack-check "
#   "-fconserve-stack -Werror=implicit-int -Werror=strict-prototypes -Werror=date-time -Werror=incompatible-pointer-types -Werror=designated-init -O3 -D'pr_fmt(fmt)=KBUILD_MODNAME \": \" fmt'  -DMODULE  -DKBUILD_BASENAME='\"curve25519_fiat64\"'  -DKBUILD_MODNAME='\"kbench9000\"'")