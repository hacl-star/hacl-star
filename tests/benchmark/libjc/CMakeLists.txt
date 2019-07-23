cmake_minimum_required(VERSION 3.5)
project(jc LANGUAGES C ASM)

# Try to clone it at build time?
# include(ExternalProject)
# ExternalProject_Add(jc
#   PREFIX .
#   GIT_REPOSITORY https://github.com/tfaoliveira/libjc.git
#   GIT_TAG 6fc8b105c794c49dfac462b1c42f633f68743e0c
#   GIT_SUBMODULES src # Hack to avoid cloning any submodules
#   CONFIGURE_COMMAND ""
#   BUILD_COMMAND ""
#   INSTALL_COMMAND ""
# )


set(LIBJC_SRC_DIR ${CMAKE_CURRENT_SOURCE_DIR} CACHE PATH "Where to find the libjc sources.")
get_filename_component(LIBJC_SRC_DIR ${LIBJC_SRC_DIR} ABSOLUTE)
message("-- Using libjc at ${LIBJC_SRC_DIR}")

add_library(jc STATIC
  ${LIBJC_SRC_DIR}/src/crypto_onetimeauth/poly1305/ref3/poly1305.s
  ${LIBJC_SRC_DIR}/src/crypto_stream/chacha20/ref/chacha20.s
)
target_compile_options(jc PRIVATE -Wno-parentheses -std=gnu11 -Wno-attributes -Wno-implicit-function-declaration)
target_include_directories(jc PUBLIC ${LIBJC_SRC_DIR})



if ("${CMAKE_SYSTEM_NAME}" STREQUAL "CYGWIN")
else()
add_library(jc_chacha20_avx2 STATIC
  ${LIBJC_SRC_DIR}/src/crypto_stream/chacha20/avx2/chacha20.s
)

add_custom_command(TARGET jc_chacha20_avx2
  POST_BUILD
  COMMAND objcopy --prefix-symbols=libjc_avx2_ $<TARGET_FILE:jc_chacha20_avx2>
)

add_library(jc_poly1305_avx2 STATIC
  ${LIBJC_SRC_DIR}/src/crypto_onetimeauth/poly1305/avx2/poly1305.s
)

add_custom_command(TARGET jc_poly1305_avx2
  POST_BUILD
  COMMAND objcopy --prefix-symbols=libjc_avx2_ $<TARGET_FILE:jc_poly1305_avx2>
)

target_link_libraries(jc jc_chacha20_avx2 jc_poly1305_avx2)


add_library(jc_chacha20_avx STATIC
  ${LIBJC_SRC_DIR}/src/crypto_stream/chacha20/avx/chacha20.s
)

add_library(jc_poly1305_avx STATIC
  ${LIBJC_SRC_DIR}/src/crypto_onetimeauth/poly1305/avx/poly1305.s
)

add_custom_command(TARGET jc_chacha20_avx
  POST_BUILD
  COMMAND objcopy --prefix-symbols=libjc_avx_ $<TARGET_FILE:jc_chacha20_avx>
)

add_custom_command(TARGET jc_poly1305_avx
  POST_BUILD
  COMMAND objcopy --prefix-symbols=libjc_avx_ $<TARGET_FILE:jc_poly1305_avx>
)

target_link_libraries(jc jc_chacha20_avx jc_poly1305_avx)
endif()