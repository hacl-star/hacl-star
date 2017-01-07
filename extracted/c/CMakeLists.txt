cmake_minimum_required(VERSION 3.6)

# Project Name
project (libhacl)

# Build settings
set(CMAKE_BUILD_TYPE Release)

# Include directories
include_directories(${CMAKE_CURRENT_SOURCE_DIR}/include)

# Project Files
set(SOURCE_FILES kremlib.c Hacl_Policies.c native128.c custom128.c Chacha20.c Salsa20.c HSalsa20.c Poly1305_64.c Curve25519.c NaCl.c)

# Generate a shared library
add_library(libhacl SHARED ${SOURCE_FILES})

