cmake_minimum_required(VERSION 3.2)

# Project Name
project (hacl)

# Build settings
set(CMAKE_BUILD_TYPE Release)

# Verified files
set(SOURCE_FILES_VERIFIED
    AEAD_Poly1305_64.c
    FStar_UInt128.c
    Hacl_Chacha20.c
    Hacl_Chacha20Poly1305.c
    Hacl_Chacha20_Vec128.c
    Hacl_Curve25519.c
    Hacl_Ed25519.c
    Hacl_HMAC_SHA2_256.c
    Hacl_Policies.c
    Hacl_Poly1305_32.c
    Hacl_Poly1305_64.c
    Hacl_Salsa20.c
    Hacl_SHA2_256.c
    Hacl_SHA2_384.c
    Hacl_SHA2_512.c
    NaCl.c)

# Trusted files
set(SOURCE_FILES_TRUSTED
    haclnacl.c
    kremlib.c
    Hacl_Unverified_Random.c)

# Public header files
set(HEADER_FILES
    HACL.h
    haclnacl.h
    vec128.h
    kremlib_base.h
    kremlib.h
    AEAD_Poly1305_64.h
    FStar_UInt128.h
    Hacl_Chacha20.h
    Hacl_Chacha20Poly1305.h
    Hacl_Chacha20_Vec128.h
    Hacl_Curve25519.h
    Hacl_Ed25519.h
    Hacl_HMAC_SHA2_256.h
    Hacl_Policies.h
    Hacl_Poly1305_32.h
    Hacl_Poly1305_64.h
    Hacl_Salsa20.h
    Hacl_SHA2_256.h
    Hacl_SHA2_384.h
    Hacl_SHA2_512.h
    NaCl.h)


set(SOURCE_FILES ${SOURCE_FILES_VERIFIED} ${SOURCE_FILES_TRUSTED})


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
