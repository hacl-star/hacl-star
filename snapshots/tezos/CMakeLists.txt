cmake_minimum_required(VERSION 3.2)

# Project Name
project (hacl)

# Build settings
set(CMAKE_BUILD_TYPE Release)

# Include directories
include_directories(./include)

# Verified Files
set(SOURCE_FILES_VERIFIED
   kremlib.c
   FStar.c
   Hacl_Policies.c
   AEAD_Poly1305_64.c
   Hacl_Chacha20.c
   Hacl_Chacha20Poly1305.c
   Hacl_Curve25519.c
   Hacl_Ed25519.c
   Hacl_Poly1305_64.c
   Hacl_SHA2_256.c
   Hacl_SHA2_384.c
   Hacl_SHA2_512.c
   Hacl_HMAC_SHA2_256.c
   Hacl_HMAC_SHA2_384.c
   Hacl_HMAC_SHA2_512.c
   Hacl_Salsa20.c
   NaCl.c
   haclnacl.c
   Hacl_Unverified_Random.c)

# Final set of files to build the libraries upon
set(SOURCE_FILES ${SOURCE_FILES_VERIFIED})

# Compilation options
set(CMAKE_C_FLAGS "-Wall")

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
