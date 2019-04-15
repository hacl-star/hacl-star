project(libbenchmark LANGUAGES C CXX ASM)
cmake_minimum_required(VERSION 3.12)

add_subdirectory(libevercrypt)

option(USE_BCRYPT "Use BCrypt." OFF)
option(USE_OPENSSL "Use OpenSSL." ON)

add_library(benchmark STATIC benchmark.cpp)
target_include_directories(benchmark PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})

add_executable(runbenchmark
  runbenchmark.cpp
  bench_hash.cpp)
target_include_directories(runbenchmark PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(runbenchmark PRIVATE benchmark evercrypt)

if(USE_BCRYPT)
  find_library(BCRYPT_LIB bcrypt.dll)
  find_path(BCRYPT_INC bcrypt.h)
  message("-- Using BCrypt at ${BCRYPT_LIB} with headers at ${BCRYPT_INC}")
  target_compile_definitions(runbenchmark PRIVATE HAVE_BCRYPT)
  target_sources(runbenchmark PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/my_bcrypt.c)
  target_link_libraries(runbenchmark PRIVATE BCRYPT_LIB)
  target_include_directories(runbenchmark PRIVATE ${BCRYPT_INC})
endif(USE_BCRYPT)

if(USE_OPENSSL)
  find_library(OPENSSL_LIB libcrypto.a PATHS $ENV{MLCRYPTO_HOME}/openssl NO_DEFAULT_PATH)
  find_library(OPENSSL_LIB libcrypto.a) # search default paths
  find_path(OPENSSL_INC openssl/crypto.h PATHS $ENV{MLCRYPTO_HOME}/openssl/include NO_DEFAULT_PATH)
  find_path(OPENSSL_INC openssl/crypto.h) # search default paths
  message("-- Using OpenSSL at ${OPENSSL_LIB} with headers at ${OPENSSL_INC}")
  target_compile_definitions(runbenchmark PRIVATE HAVE_OPENSSL)
  target_sources(runbenchmark PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/my_openssl.c)
  target_link_libraries(runbenchmark PRIVATE ${OPENSSL_LIB})
  target_include_directories(runbenchmark PRIVATE ${OPENSSL_INC})
  if(NOT ${CMAKE_SYSTEM_NAME} STREQUAL "Windows")
    target_link_libraries(runbenchmark PRIVATE dl pthread)
  endif(NOT ${CMAKE_SYSTEM_NAME} STREQUAL "Windows")
endif(USE_OPENSSL)