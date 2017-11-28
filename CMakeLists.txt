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
   snapshots/hacl-c/FStar.c
   snapshots/hacl-c/Hacl_Policies.c
   snapshots/hacl-c/AEAD_Poly1305_64.c
   snapshots/hacl-c/Hacl_Chacha20.c
   snapshots/hacl-c/Hacl_Chacha20Poly1305.c
   snapshots/hacl-c/Hacl_Curve25519.c
   snapshots/hacl-c/Hacl_Ed25519.c
   snapshots/hacl-c/Hacl_Poly1305_64.c
   snapshots/hacl-c/Hacl_SHA2_256.c
   snapshots/hacl-c/Hacl_SHA2_384.c
   snapshots/hacl-c/Hacl_SHA2_512.c
   snapshots/hacl-c/Hacl_HMAC_SHA2_256.c
   snapshots/hacl-c/Hacl_Salsa20.c
   snapshots/hacl-c/NaCl.c)

# Experimental Files
set(SOURCE_FILES_EXPERIMENTAL
   snapshots/hacl-c-experimental/cpuid.c
   snapshots/hacl-c-experimental/drng.c
   snapshots/hacl-c-experimental/Random.c)

# Define a user variable to determinate if experimental files are build
option(Experimental "Include experimental code in HaCl build" OFF)

# Final set of files to build the libraries upon
if (Experimental)
   set(SOURCE_FILES ${SOURCE_FILES_VERIFIED} ${SOURCE_FILES_EXPERIMENTAL})
else ()
   set(SOURCE_FILES ${SOURCE_FILES_VERIFIED})
endif ()

# Compilation options
# set(CMAKE_C_FLAGS "-Wall -Wextra")

# Compilation options depending on the architecture
if(CMAKE_SIZEOF_VOID_P EQUAL 8)
   # 64 bits
   if (MSVC)
      set(CMAKE_C_FLAGS "-DKRML_NOUINT128")
   endif()
elseif(CMAKE_SIZEOF_VOID_P EQUAL 4)
   # 32 bits
   set(CMAKE_C_FLAGS "-DKRML_NOUINT128")
endif()

# Generate both a static and a shared library
add_library(hacl_static STATIC ${SOURCE_FILES})
set_target_properties(hacl_static PROPERTIES OUTPUT_NAME hacl)

add_library(hacl_shared SHARED ${SOURCE_FILES})
set_target_properties(hacl_shared PROPERTIES OUTPUT_NAME hacl)

# Note: on Windows, depending on the build system,
#       both static and shared can have the .lib extension
#       (You can change the OUTPUT_NAME in that case...)
