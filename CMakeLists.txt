cmake_minimum_required(VERSION 3.2)

# Project Name
project (hacl)

# Build settings
set(CMAKE_BUILD_TYPE Release)

# Include directories
include_directories(./snapshots/hacl-c ./snapshots/hacl-c-experimental)

# Verified files
set(SOURCE_FILES_VERIFIED
    snapshots/hacl-c/AEAD_Poly1305_64.c
    snapshots/hacl-c/FStar_UInt128.c
    snapshots/hacl-c/Hacl_Chacha20.c
    snapshots/hacl-c/Hacl_Chacha20Poly1305.c
    snapshots/hacl-c/Hacl_Chacha20_Vec128.c
    snapshots/hacl-c/Hacl_Curve25519.c
    snapshots/hacl-c/Hacl_Ed25519.c
    snapshots/hacl-c/Hacl_HMAC_SHA2_256.c
    snapshots/hacl-c/Hacl_Policies.c
    snapshots/hacl-c/Hacl_Poly1305_32.c
    snapshots/hacl-c/Hacl_Poly1305_64.c
    snapshots/hacl-c/Hacl_Salsa20.c
    snapshots/hacl-c/Hacl_SHA2_256.c
    snapshots/hacl-c/Hacl_SHA2_384.c
    snapshots/hacl-c/Hacl_SHA2_512.c
    snapshots/hacl-c/NaCl.c)

# Trusted files
set(SOURCE_FILES_TRUSTED
    snapshots/api/haclnacl.c
    snapshots/hacl-c/kremlib.c
    snapshots/experimental/Hacl_Unverified_Random.c)

# Experimental Files
set(SOURCE_FILES_EXPERIMENTAL
    snapshots/hacl-c-experimental/cpuid.c
    snapshots/hacl-c-experimental/drng.c
    snapshots/hacl-c-experimental/Hacl_Random.c)

# Public header files
set(HEADER_FILES
    snapshots/api/HACL.h
    snapshots/api/haclnacl.h
    snapshots/hacl-c/vec128.h
    snapshots/hacl-c/kremlib_base.h
    snapshots/hacl-c/kremlib.h
    snapshots/hacl-c/AEAD_Poly1305_64.h
    snapshots/hacl-c/FStar_UInt128.h
    snapshots/hacl-c/Hacl_Chacha20.h
    snapshots/hacl-c/Hacl_Chacha20Poly1305.h
    snapshots/hacl-c/Hacl_Chacha20_Vec128.h
    snapshots/hacl-c/Hacl_Curve25519.h
    snapshots/hacl-c/Hacl_Ed25519.h
    snapshots/hacl-c/Hacl_HMAC_SHA2_256.h
    snapshots/hacl-c/Hacl_Policies.h
    snapshots/hacl-c/Hacl_Poly1305_32.h
    snapshots/hacl-c/Hacl_Poly1305_64.h
    snapshots/hacl-c/Hacl_Salsa20.h
    snapshots/hacl-c/Hacl_SHA2_256.h
    snapshots/hacl-c/Hacl_SHA2_384.h
    snapshots/hacl-c/Hacl_SHA2_512.h
    snapshots/hacl-c/NaCl.h)

# Define a user variable to determinate if experimental files are build
option(Experimental "Include experimental code in HACL* build" OFF)

# Final set of files to build the libraries upon
if (Experimental)
   set(SOURCE_FILES ${SOURCE_FILES_VERIFIED} ${SOURCE_FILES_TRUSTED} ${SOURCE_FILES_EXPERIMENTAL})
else ()
   set(SOURCE_FILES ${SOURCE_FILES_VERIFIED} ${SOURCE_FILES_TRUSTED})
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
#
# Note: on Windows, depending on the build system,
#       both static and shared can have the .lib extension
#       (You can change the OUTPUT_NAME in that case...)
add_library(hacl_static STATIC ${SOURCE_FILES})
set_target_properties(hacl_static PROPERTIES OUTPUT_NAME hacl)

add_library(hacl_shared SHARED ${SOURCE_FILES})
set_target_properties(hacl_shared PROPERTIES OUTPUT_NAME hacl)

set_target_properties(hacl_shared hacl_static PROPERTIES
    PUBLIC_HEADER "${HEADER_FILES}")

INSTALL(TARGETS hacl_shared hacl_static LIBRARY
    DESTINATION "lib"
    ARCHIVE DESTINATION "lib"
    PUBLIC_HEADER DESTINATION "include/hacl")
