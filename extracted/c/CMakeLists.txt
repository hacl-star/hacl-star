cmake_minimum_required(VERSION 3.5)

# Project Name
project (hacl)

# Build settings
set(CMAKE_BUILD_TYPE Release)

# Include directories
include_directories(./)

# Project Files
set(SOURCE_FILES kremlib.c Hacl_Policies.c Chacha20.c Salsa20.c HSalsa20.c Poly1305_64.c Curve25519.c NaCl.c)

# Compilation options
set(GCC_COVERAGE_COMPILE_FLAGS "-flto -ccopt -march=nativ -Wno-error=pointer-sign -Wno-error=incompatible-pointer-types -Wno-error=format= ")

# Generate both a static and a shared library
add_library(hacl_static STATIC ${SOURCE_FILES})
set_target_properties(hacl_static PROPERTIES OUTPUT_NAME hacl)

add_library(hacl_shared SHARED ${SOURCE_FILES})
set_target_properties(hacl_shared PROPERTIES OUTPUT_NAME hacl)

# Note: on Windows, depending on the build system,
#       both static and shared can have the .lib extension
#       (You can change the OUTPUT_NAME in that case...)
