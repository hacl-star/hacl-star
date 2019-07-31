set(CMAKE_LEGACY_CYGWIN_WIN32 0)
project(benchmark LANGUAGES C CXX ASM)
cmake_minimum_required(VERSION 3.5)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

option(USE_HACL "Use HaCl." ON)
option(USE_VALE "Use Vale." ON)
option(USE_BCRYPT "Use BCrypt." OFF)
option(USE_OPENSSL "Use OpenSSL." ON)
option(USE_RFC7748 "Use the RFC 7748 reference implementation" ON)
option(USE_FIAT_CURVE25519 "Use the Fiat Curve25519 implementation" ON)
option(USE_LIBCURVE25519 "Use the library Curve25519 implementations" OFF)
option(USE_LIBJC "Use libjc, the Jasmin crypto library." ON)

option(ASAN "Enable clang address sanitizer" OFF)

add_compile_options(-march=native -mtune=native)
if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
  add_compile_options(-flto -ffat-lto-objects)
elseif ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "Clang")
  add_compile_options(-fbracket-depth=512)
  # message("Disabling libjc")
  set(USE_LIBJC OFF)
endif()

add_subdirectory(libevercrypt)

add_library(benchmark STATIC benchmark.cpp)
target_include_directories(benchmark PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(benchmark PRIVATE evercrypt)
target_compile_options(benchmark PRIVATE -march=native -mtune=native -std=c++11)

add_executable(runbenchmark
  runbenchmark.cpp
  bench_hash.cpp
  bench_aead.cpp
  bench_curve25519.cpp
  bench_ed25519.cpp
  bench_merkle.cpp
  bench_cipher.cpp
  bench_mac.cpp
)
target_include_directories(runbenchmark PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(runbenchmark PRIVATE benchmark evercrypt)
target_compile_options(runbenchmark PRIVATE -march=native -mtune=native -std=c++11)

if ("${CMAKE_SYSTEM_NAME}" STREQUAL "CYGWIN")
  target_compile_definitions(benchmark PUBLIC WIN32)
endif()

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
  SET(CMAKE_FIND_LIBRARY_SUFFIXES "")
  SET(OPENSSL_LIB_NAME libcrypto.a)
  find_library(OPENSSL_LIB ${OPENSSL_LIB_NAME} PATHS $ENV{MLCRYPTO_HOME}/openssl NO_DEFAULT_PATH)
  find_library(OPENSSL_LIB ${OPENSSL_LIB_NAME}) # search default paths
  find_path(OPENSSL_INC openssl/crypto.h PATHS $ENV{MLCRYPTO_HOME}/openssl/include NO_DEFAULT_PATH)
  find_path(OPENSSL_INC openssl/crypto.h) # search default paths
  get_filename_component(OPENSSL_LIB ${OPENSSL_LIB} REALPATH)
  get_filename_component(OPENSSL_INC ${OPENSSL_INC} REALPATH)
  message("-- Using OpenSSL at ${OPENSSL_LIB} with headers at ${OPENSSL_INC}")
  target_compile_definitions(runbenchmark PRIVATE HAVE_OPENSSL)
  target_link_libraries(runbenchmark PRIVATE ${OPENSSL_LIB})
  target_include_directories(runbenchmark PRIVATE ${OPENSSL_INC})
  if("${CMAKE_SYSTEM_NAME}" STREQUAL "CYGWIN")
    target_link_libraries(runbenchmark PRIVATE Ws2_32)
  else()
    target_link_libraries(runbenchmark PRIVATE dl pthread)
  endif()
endif(USE_OPENSSL)

if(USE_RFC7748)
  add_subdirectory(librfc7748)
  target_compile_definitions(runbenchmark PRIVATE HAVE_RFC7748)
  target_link_libraries(runbenchmark PRIVATE rfc7748)
  target_include_directories(runbenchmark PRIVATE ${RFC7748_DIR})
endif(USE_RFC7748)

if(USE_LIBCURVE25519)
  add_subdirectory(libcurve25519)
  target_compile_definitions(runbenchmark PRIVATE HAVE_LIBCURVE25519)
  target_link_libraries(runbenchmark PRIVATE libcurve25519)
endif()

if(USE_FIAT_CURVE25519)
  add_subdirectory(libfiat-curve25519)
  target_compile_definitions(runbenchmark PRIVATE HAVE_FIAT_CURVE25519)
  target_link_libraries(runbenchmark PRIVATE fiat-curve25519)
endif()

if(USE_LIBJC)
  add_subdirectory(libjc)
  target_compile_definitions(runbenchmark PRIVATE HAVE_JC)
  target_link_libraries(runbenchmark PRIVATE jc)
endif()

if(ASAN)
  target_compile_options(benchmark PRIVATE -g -fsanitize=undefined,address -fno-omit-frame-pointer -fno-sanitize-recover=all -fno-sanitize=function)
  target_link_libraries(benchmark PRIVATE -g -fsanitize=address)
  target_compile_options(runbenchmark PRIVATE -g -fsanitize=undefined,address -fno-omit-frame-pointer -fno-sanitize-recover=all -fno-sanitize=function)
  target_link_libraries(runbenchmark PRIVATE -g -fsanitize=address)
endif()
