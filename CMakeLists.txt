cmake_minimum_required(VERSION 3.2)

# Project Name
project (hacl)

# Build settings
set(CMAKE_BUILD_TYPE Release)

# Include directories
include_directories(./snapshots/hacl-c ./snapshots/hacl-c-experimental)

# Verified Files
set(SOURCE_FILES_VERIFIED
   snapshots/hacl-c/kremlib.c
   snapshots/hacl-c/Hacl_Policies.c
   snapshots/hacl-c/Salsa20.c
   snapshots/hacl-c/HSalsa20.c
   snapshots/hacl-c/Curve25519.c
   snapshots/hacl-c/NaCl.c)

# Verified files that are redefined in experimental
set(SOURCE_FILES_VERIFIED_2
   snapshots/hacl-c/Chacha20.c
   snapshots/hacl-c/Poly1305_64.c)

# Experimental Files
set(SOURCE_FILES_EXPERIMENTAL
   snapshots/hacl-c-experimental/cpuid.c
   snapshots/hacl-c-experimental/drng.c
   snapshots/hacl-c-experimental/Random.c
   snapshots/hacl-c-experimental/SHA2.c
   snapshots/hacl-c-experimental/Chacha20.c
   snapshots/hacl-c-experimental/Poly1305_64.c
   snapshots/hacl-c-experimental/aead_chacha20_poly1305.c)

# Define a user variable to determinate if experimental files are build
option(Experimental "Include experimental code in HaCl build" OFF)

# Final set of files to build the libraries upon
if (Experimental)
   set(SOURCE_FILES ${SOURCE_FILES_VERIFIED} ${SOURCE_FILES_EXPERIMENTAL})
else ()
   set(SOURCE_FILES ${SOURCE_FILES_VERIFIED_2} ${SOURCE_FILES_VERIFIED})
endif ()

# Compilation options
set(GCC_COVERAGE_COMPILE_FLAGS "-march=nativ -Wno-error=pointer-sign -Wno-error=incompatible-pointer-types -Wno-error=format= ")

# Generate both a static and a shared library
add_library(hacl_static STATIC ${SOURCE_FILES})
set_target_properties(hacl_static PROPERTIES OUTPUT_NAME hacl)

add_library(hacl_shared SHARED ${SOURCE_FILES})
set_target_properties(hacl_shared PROPERTIES OUTPUT_NAME hacl)

# Note: on Windows, depending on the build system,
#       both static and shared can have the .lib extension
#       (You can change the OUTPUT_NAME in that case...)
