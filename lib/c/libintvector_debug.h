#ifndef __LIBINTVECTOR_DEBUG_H_INCLUDED
#define __LIBINTVECTOR_DEBUG_H_INCLUDED

#include <sys/types.h>

// # DEBUGGING FLAGS
// =================
// It is possible to debug the trace of the primitives defined in
// libintvector.h by copying this file to dist/gcc-compatible and
// using the [DEBUG_VECTOR_TRACE] C flag.
//
// As we use the same vector types to manipulate blocks of uint32 and blocks
// of uint64, the log results will vary with the endianess, in particular for
// some generic operations like [and] or [xor]. By default, the printing is
// performed as if we were manipulating blocks of uint32. If you want to
// switch to blocks of uint64, use the flag: [DEBUG_VECTOR_TRACE_ELEMENTS_64].
// Note that if those flags are activated, it may be necessary to tweak a bit
// the compilation options to build HACL. More specifically, you may need to
// always activate the compiler options to use vector support (even for files
// which actually don't make use of vectors, if they have libintvector.h as
// a dependency). When comparing traces, note that some instructions are not
// compiled in the same order on the different platforms, but it doesn't lead
// to a lot of discrepancies in practice.

#if defined(DEBUG_VECTOR_TRACE)

#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

static inline void print_debug_uint32_t(const char *msg, uint32_t x) {
  printf(">> %s: %x08U\n", msg, x);
}

static inline void print_debug_uint64_t(const  char *msg, uint64_t x) {
  printf(">> %s: %lxUL\n", msg, x);
}

static inline void print_debug_buf8(const char *msg, const uint8_t *buf) {
  printf(">> %s: ", msg);
  printf("[0x%02x,0x%02x,0x%02x,0x%02x,0x%02x,0x%02x,0x%02x,0x%02x,0x%02x,0x%02x,0x%02x,0x%02x,0x%02x,0x%02x,0x%02x,0x%02x]\n",
         buf[0], buf[1], buf[2], buf[3],
         buf[4], buf[5], buf[6], buf[7],
         buf[8], buf[9], buf[10], buf[11],
         buf[12], buf[13], buf[14], buf[15]);
}

static inline void print_vector128_32(const char *msg, Lib_IntVector_Intrinsics_vec128 vec) {
  printf(">> %s: ", msg);
  printf("[0x%08x,0x%08x,0x%08x,0x%08x]\n",
         Lib_IntVector_Intrinsics_vec128_extract32(vec,0),
         Lib_IntVector_Intrinsics_vec128_extract32(vec,1),
         Lib_IntVector_Intrinsics_vec128_extract32(vec,2),
         Lib_IntVector_Intrinsics_vec128_extract32(vec,3));
}

static inline void print_vector128_64(const char *msg, Lib_IntVector_Intrinsics_vec128 vec) {
  printf(">> %s: ", msg);
  printf("[0x%lxUL,0x%lxUL]\n",
         (uint64_t) Lib_IntVector_Intrinsics_vec128_extract64(vec,0),
         (uint64_t) Lib_IntVector_Intrinsics_vec128_extract64(vec,1));
}

// Sometimes, we don't know which representation to use to display the vectors,
// so the user may need to indicate it with a flag.
#if defined(DEBUG_VECTOR_TRACE_ELEMENTS_64)
#define print_vector128_unkwn(msg, vec) print_vector128_64(msg, vec)
#else
#define print_vector128_unkwn(msg, vec) print_vector128_32(msg, vec)
#endif

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_load32_le_debug(const uint8_t *x0) {
  Lib_IntVector_Intrinsics_vec128 res;
  printf("[> vec128_load_le\n");
  print_debug_buf8("x0", x0);
  res = Lib_IntVector_Intrinsics_vec128_load32_le((uint8_t*) x0);
  print_vector128_32("res", res);
  return res;
}

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_load32_be_debug(const uint8_t *x0) {
  Lib_IntVector_Intrinsics_vec128 res;
  printf("[> vec128_load_be\n");
  print_debug_buf8("x0", x0);
  res = Lib_IntVector_Intrinsics_vec128_load32_be((uint8_t*) x0);
  print_vector128_32("res", res);
  return res;
}

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_load64_le_debug(const uint8_t *x0) {
  Lib_IntVector_Intrinsics_vec128 res;
  printf("[> vec128_load_le\n");
  print_debug_buf8("x0", x0);
  res = Lib_IntVector_Intrinsics_vec128_load64_le((uint8_t*) x0);
  print_vector128_64("res", res);
  return res;
}

static inline void
Lib_IntVector_Intrinsics_vec128_store32_le_debug(const uint8_t *x0,
                                                 Lib_IntVector_Intrinsics_vec128 x1) {
  printf("[> vec128_store_le\n");
  print_vector128_32("x1", x1);
  Lib_IntVector_Intrinsics_vec128_store32_le((uint8_t*) x0, x1);
  print_debug_buf8("res", x0);
}

static inline void
Lib_IntVector_Intrinsics_vec128_store32_be_debug(const uint8_t *x0,
                                                 Lib_IntVector_Intrinsics_vec128 x1) {
  printf("[> vec128_store_be\n");
  print_vector128_32("x1", x1);
  Lib_IntVector_Intrinsics_vec128_store32_be((uint8_t*) x0, x1);
  print_debug_buf8("res", x0);
}

static inline void
Lib_IntVector_Intrinsics_vec128_store64_le_debug(const uint8_t *x0,
                                                 Lib_IntVector_Intrinsics_vec128 x1) {
  printf("[> vec128_store_le\n");
  print_vector128_64("x1", x1);
  Lib_IntVector_Intrinsics_vec128_store64_le((uint8_t*) x0, x1);
  print_debug_buf8("res", x0);
}

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_add32_debug(Lib_IntVector_Intrinsics_vec128 x0,
                                            Lib_IntVector_Intrinsics_vec128 x1) {
  printf("[> vec128_add32\n");
  print_vector128_32("x0", x0);
  print_vector128_32("x1", x1);
  x0 = Lib_IntVector_Intrinsics_vec128_add32(x0, x1);
  print_vector128_32("res", x0);
  return x0;
}

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_add64_debug(Lib_IntVector_Intrinsics_vec128 x0,
                                            Lib_IntVector_Intrinsics_vec128 x1) {
  printf("[> vec128_add64\n");
  print_vector128_64("x0", x0);
  print_vector128_64("x1", x1);
  x0 = Lib_IntVector_Intrinsics_vec128_add64(x0, x1);
  print_vector128_64("res", x0);
  return x0;
}

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_xor_debug(Lib_IntVector_Intrinsics_vec128 x0,
                                          Lib_IntVector_Intrinsics_vec128 x1) {
  printf("[> vec128_xor\n");
  print_vector128_32("x0", x0);
  print_vector128_32("x1", x1);
  x0 = Lib_IntVector_Intrinsics_vec128_xor(x0, x1);
  print_vector128_32("res", x0);
  return x0;
}

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_and_debug(Lib_IntVector_Intrinsics_vec128 x0,
                                          Lib_IntVector_Intrinsics_vec128 x1) {
  printf("[> vec128_and\n");
  print_vector128_unkwn("x0", x0);
  print_vector128_unkwn("x1", x1);
  x0 = Lib_IntVector_Intrinsics_vec128_and(x0, x1);
  print_vector128_unkwn("res", x0);
  return x0;
}

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_eq32_debug(Lib_IntVector_Intrinsics_vec128 x0,
                                           Lib_IntVector_Intrinsics_vec128 x1) {
  printf("[> vec128_eq32\n");
  print_vector128_32("x0", x0);
  print_vector128_32("x1", x1);
  x0 = Lib_IntVector_Intrinsics_vec128_eq32(x0, x1);
  print_vector128_32("res", x0);
  return x0;
}

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_eq64_debug(Lib_IntVector_Intrinsics_vec128 x0,
                                           Lib_IntVector_Intrinsics_vec128 x1) {
  printf("[> vec128_eq64\n");
  print_vector128_64("x0", x0);
  print_vector128_64("x1", x1);
  x0 = Lib_IntVector_Intrinsics_vec128_eq64(x0, x1);
  print_vector128_64("res", x0);
  return x0;
}

static inline uint32_t
Lib_IntVector_Intrinsics_vec128_extract32_debug(Lib_IntVector_Intrinsics_vec128 x0,
                                                uint32_t x1) {
  uint32_t res;
  printf("[> vec128_extract32\n");
  print_vector128_32("x0", x0);
  print_debug_uint32_t("x1", x1);
  // The selector must be a constant
  switch (x1) {
  case 0U: res = Lib_IntVector_Intrinsics_vec128_extract32(x0, 0U); break;
  case 1U: res = Lib_IntVector_Intrinsics_vec128_extract32(x0, 1U); break;
  case 2U: res = Lib_IntVector_Intrinsics_vec128_extract32(x0, 2U); break;
  case 3U: res = Lib_IntVector_Intrinsics_vec128_extract32(x0, 3U); break;
  default:
    printf("**ERROR**: libintvector.h: Lib_IntVector_Intrinsics_vec128_extract32: debugging version: 'x1' must be in [0; 3]");
    abort();
  }
  print_debug_uint32_t("res", res);
  return res;
}

static inline uint64_t
Lib_IntVector_Intrinsics_vec128_extract64_debug(Lib_IntVector_Intrinsics_vec128 x0,
                                                uint32_t x1) {
  uint64_t res;
  printf("[> vec128_extract64\n");
  print_vector128_64("x0", x0);
  print_debug_uint32_t("x1", x1);
  // The selector must be a constant
  switch (x1) {
  case 0U: res = Lib_IntVector_Intrinsics_vec128_extract64(x0, 0U); break;
  case 1U: res = Lib_IntVector_Intrinsics_vec128_extract64(x0, 1U); break;
  default:
    printf("**ERROR**: libintvector.h: Lib_IntVector_Intrinsics_vec128_extract64: debugging version: 'x1' must be in [0; 1]");
    abort();
  }
  print_debug_uint64_t("res", res);
  return res;
}

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_gt32_debug(Lib_IntVector_Intrinsics_vec128 x0,
                                           Lib_IntVector_Intrinsics_vec128 x1) {
  printf("[> vec128_gt32\n");
  print_vector128_32("x0", x0);
  print_vector128_32("x1", x1);
  x0 = Lib_IntVector_Intrinsics_vec128_gt32(x0, x1);
  print_vector128_32("res", x0);
  return x0;
}

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_gt64_debug(Lib_IntVector_Intrinsics_vec128 x0,
                                           Lib_IntVector_Intrinsics_vec128 x1) {
  printf("[> vec128_gt64\n");
  print_vector128_64("x0", x0);
  print_vector128_64("x1", x1);
  x0 = Lib_IntVector_Intrinsics_vec128_gt64(x0, x1);
  print_vector128_64("res", x0);
  return x0;
}

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_insert32_debug(Lib_IntVector_Intrinsics_vec128 x0,
                                               uint32_t x1,
                                               uint32_t x2) {
  printf("[> vec128_eq32\n");
  print_vector128_32("x0", x0);
  print_debug_uint32_t("x1", x1);
  print_debug_uint32_t("x2", x2);
  // The selector must be a constant
  switch (x2) {
  case 0U: x0 = Lib_IntVector_Intrinsics_vec128_insert32(x0, x1, 0U); break;
  case 1U: x0 = Lib_IntVector_Intrinsics_vec128_insert32(x0, x1, 1U); break;
  case 2U: x0 = Lib_IntVector_Intrinsics_vec128_insert32(x0, x1, 2U); break;
  case 3U: x0 = Lib_IntVector_Intrinsics_vec128_insert32(x0, x1, 3U); break;
  default:
    printf("**ERROR**: libintvector.h: Lib_IntVector_Intrinsics_vec128_insert32: debugging version: 'x2' must be in [0; 3]");
    abort();
  }
  print_vector128_32("res", x0);
  return x0;
}

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_insert64_debug(Lib_IntVector_Intrinsics_vec128 x0,
                                               uint64_t x1,
                                               uint32_t x2) {
  printf("[> vec128_eq64\n");
  print_vector128_64("x0", x0);
  print_debug_uint64_t("x1", x1);
  print_debug_uint32_t("x2", x2);
  // The selector must be a constant
  switch (x2) {
  case 0U: x0 = Lib_IntVector_Intrinsics_vec128_insert64(x0, x1, 0U); break;
  case 1U: x0 = Lib_IntVector_Intrinsics_vec128_insert64(x0, x1, 1U); break;
  default:
    printf("**ERROR**: libintvector.h: Lib_IntVector_Intrinsics_vec128_insert64: debugging version: 'x2' must be in [0; 1]");
    abort();
  }
  print_vector128_64("res", x0);
  return x0;
}

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_interleave_high32_debug(Lib_IntVector_Intrinsics_vec128 x0,
                                                        Lib_IntVector_Intrinsics_vec128 x1) {
  printf("[> vec128_interleave_high32\n");
  print_vector128_32("x0", x0);
  print_vector128_32("x1", x1);
  x0 = Lib_IntVector_Intrinsics_vec128_interleave_high32(x0, x1);
  print_vector128_32("res", x0);
  return x0;
}

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_interleave_high64_debug(Lib_IntVector_Intrinsics_vec128 x0,
                                                        Lib_IntVector_Intrinsics_vec128 x1) {
  printf("[> vec128_interleave_high64\n");
  print_vector128_64("x0", x0);
  print_vector128_64("x1", x1);
  x0 = Lib_IntVector_Intrinsics_vec128_interleave_high64(x0, x1);
  print_vector128_64("res", x0);
  return x0;
}

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_interleave_low32_debug(Lib_IntVector_Intrinsics_vec128 x0,
                                                       Lib_IntVector_Intrinsics_vec128 x1) {
  printf("[> vec128_interleave_low32\n");
  print_vector128_32("x0", x0);
  print_vector128_32("x1", x1);
  x0 = Lib_IntVector_Intrinsics_vec128_interleave_low32(x0, x1);
  print_vector128_32("res", x0);
  return x0;
}

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_interleave_low64_debug(Lib_IntVector_Intrinsics_vec128 x0,
                                                       Lib_IntVector_Intrinsics_vec128 x1) {
  printf("[> vec128_interleave_low64\n");
  print_vector128_64("x0", x0);
  print_vector128_64("x1", x1);
  x0 = Lib_IntVector_Intrinsics_vec128_interleave_low64(x0, x1);
  print_vector128_64("res", x0);
  return x0;
}

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_load32_debug(uint32_t x0) {
  Lib_IntVector_Intrinsics_vec128 res;
  printf("[> vec128_load32\n");
  print_debug_uint32_t("x0", x0);
  res = Lib_IntVector_Intrinsics_vec128_load32(x0);
  print_vector128_32("res", res);
  return res;
}

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_load32s_debug(uint32_t x0, uint32_t x1,
                                              uint32_t x2, uint32_t x3) {
  Lib_IntVector_Intrinsics_vec128 res;
  printf("[> vec128_load32s\n");
  print_debug_uint32_t("x0", x0);
  print_debug_uint32_t("x1", x1);
  print_debug_uint32_t("x2", x2);
  print_debug_uint32_t("x3", x3);
  res = Lib_IntVector_Intrinsics_vec128_load32s(x0, x1, x2, x3);
  print_vector128_32("res", res);
  return res;
}

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_load64_debug(uint64_t x0) {
  Lib_IntVector_Intrinsics_vec128 res;
  printf("[> vec128_load64\n");
  print_debug_uint64_t("x0", x0);
  res = Lib_IntVector_Intrinsics_vec128_load64(x0);
  print_vector128_64("res", res);
  return res;
}

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_lognot_debug(Lib_IntVector_Intrinsics_vec128 x0) {
  printf("[> vec128_lognot\n");
  print_vector128_unkwn("x0", x0);
  x0 = Lib_IntVector_Intrinsics_vec128_lognot(x0);
  print_vector128_unkwn("res", x0);
  return x0;
}

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_mul64_debug(Lib_IntVector_Intrinsics_vec128 x0,
                                            Lib_IntVector_Intrinsics_vec128 x1) {
  printf("[> vec128_mul64\n");
  print_vector128_64("x0", x0);
  print_vector128_64("x1", x1);
  x0 = Lib_IntVector_Intrinsics_vec128_mul64(x0, x1);
  print_vector128_64("res", x0);
  return x0;
}

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_or_debug(Lib_IntVector_Intrinsics_vec128 x0,
                                         Lib_IntVector_Intrinsics_vec128 x1) {
  printf("[> vec128_or\n");
  print_vector128_unkwn("x0", x0);
  print_vector128_unkwn("x1", x1);
  x0 = Lib_IntVector_Intrinsics_vec128_or(x0, x1);
  print_vector128_unkwn("res", x0);
  return x0;
}

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_rotate_left32_debug(Lib_IntVector_Intrinsics_vec128 x0,
                                                    uint32_t x1) {
  printf("[> vec128_rotate_left32\n");
  print_vector128_32("x0", x0);
  print_debug_uint32_t("x1", x1);
  switch(x1) {
  case 0U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 0U); break;
  case 1U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 1U); break;
  case 2U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 2U); break;
  case 3U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 3U); break;
  case 4U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 4U); break;
  case 5U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 5U); break;
  case 6U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 6U); break;
  case 7U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 7U); break;
  case 8U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 8U); break;
  case 9U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 9U); break;
  case 10U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 10U); break;
  case 11U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 11U); break;
  case 12U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 12U); break;
  case 13U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 13U); break;
  case 14U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 14U); break;
  case 15U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 15U); break;
  case 16U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 16U); break;
  case 17U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 17U); break;
  case 18U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 18U); break;
  case 19U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 19U); break;
  case 20U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 20U); break;
  case 21U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 21U); break;
  case 22U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 22U); break;
  case 23U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 23U); break;
  case 24U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 24U); break;
  case 25U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 25U); break;
  case 26U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 26U); break;
  case 27U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 27U); break;
  case 28U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 28U); break;
  case 29U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 29U); break;
  case 30U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 30U); break;
  case 31U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 31U); break;
  case 32U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, 32U); break;
  default:
    printf("**ERROR**: libintvector.h: Lib_IntVector_Intrinsics_vec128_rotate_left32: debugging version: 'x1' must be in [0;32]");
    abort();
  }
  print_vector128_32("res", x0);
  return x0;
}

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_rotate_right32_debug(Lib_IntVector_Intrinsics_vec128 x0,
                                                     uint32_t x1) {
  printf("[> vec128_rotate_right32\n");
  print_vector128_32("x0", x0);
  print_debug_uint32_t("x1", x1);
  switch(x1) {
  case 0U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 0U); break;
  case 1U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 1U); break;
  case 2U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 2U); break;
  case 3U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 3U); break;
  case 4U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 4U); break;
  case 5U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 5U); break;
  case 6U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 6U); break;
  case 7U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 7U); break;
  case 8U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 8U); break;
  case 9U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 9U); break;
  case 10U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 10U); break;
  case 11U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 11U); break;
  case 12U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 12U); break;
  case 13U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 13U); break;
  case 14U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 14U); break;
  case 15U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 15U); break;
  case 16U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 16U); break;
  case 17U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 17U); break;
  case 18U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 18U); break;
  case 19U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 19U); break;
  case 20U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 20U); break;
  case 21U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 21U); break;
  case 22U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 22U); break;
  case 23U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 23U); break;
  case 24U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 24U); break;
  case 25U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 25U); break;
  case 26U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 26U); break;
  case 27U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 27U); break;
  case 28U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 28U); break;
  case 29U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 29U); break;
  case 30U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 30U); break;
  case 31U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 31U); break;
  case 32U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, 32U); break;
  default:
    printf("**ERROR**: libintvector.h: Lib_IntVector_Intrinsics_vec128_rotate_right32: debugging version: 'x1' must be in [0;32]");
    abort();
  }
  print_vector128_32("res", x0);
  return x0;
}

// The shift value must be a constant. In practice, is always 1, 2 or 3
static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32_debug(Lib_IntVector_Intrinsics_vec128 x0,
                                                           uint32_t x1) {
  printf("[> vec128_rotate_right_lanes32\n");
  print_vector128_32("x0", x0);
  print_debug_uint32_t("x1", x1);
  switch (x1) {
  case 0U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(x0, 0U); break; // Just for the testing file
  case 1U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(x0, 1U); break;
  case 2U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(x0, 2U); break;
  case 3U: x0 = Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(x0, 3U); break;
  default:
    printf("**ERROR**: libintvector.h: Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32: debugging version: 'x1' must be 0, 1, 2 or 3");
    abort();
  }
  print_vector128_32("res", x0);
  return x0;
}

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_shift_left64_debug(Lib_IntVector_Intrinsics_vec128 x0,
                                                   uint32_t x1) {
  printf("[> vec128_shift_left64\n");
  print_vector128_64("x0", x0);
  print_debug_uint32_t("x1", x1);
  x0 = Lib_IntVector_Intrinsics_vec128_shift_left64(x0, x1);
  print_vector128_64("res", x0);
  return x0;
}

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_shift_right64_debug(Lib_IntVector_Intrinsics_vec128 x0,
                                                    uint32_t x1) {
  printf("[> vec128_shift_right64\n");
  print_vector128_64("x0", x0);
  print_debug_uint32_t("x1", x1);
  x0 = Lib_IntVector_Intrinsics_vec128_shift_right64(x0, x1);
  print_vector128_64("res", x0);
  return x0;
}

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_shift_right32_debug(Lib_IntVector_Intrinsics_vec128 x0,
                                                    uint32_t x1) {
  printf("[> vec128_shift_right32\n");
  print_vector128_32("x0", x0);
  print_debug_uint32_t("x1", x1);
  x0 = Lib_IntVector_Intrinsics_vec128_shift_right32(x0, x1);
  print_vector128_32("res", x0);
  return x0;
}

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_smul64_debug(Lib_IntVector_Intrinsics_vec128 x0,
                                             uint64_t x1) {
  printf("[> vec128_smul64\n");
  print_vector128_64("x0", x0);
  print_debug_uint64_t("x1", x1);
  x0 = Lib_IntVector_Intrinsics_vec128_smul64(x0, x1);
  print_vector128_64("res", x0);
  return x0;
}

static inline Lib_IntVector_Intrinsics_vec128
Lib_IntVector_Intrinsics_vec128_sub64_debug(Lib_IntVector_Intrinsics_vec128 x0,
                                            Lib_IntVector_Intrinsics_vec128 x1) {
  printf("[> vec128_sub64\n");
  print_vector128_64("x0", x0);
  print_vector128_64("x1", x1);
  x0 = Lib_IntVector_Intrinsics_vec128_sub64(x0, x1);
  print_vector128_64("res", x0);
  return x0;
}

// Redefine the intrinsics macros to use the debugging functions
// instead.
// Note that we take care to redefine the macros at the
// very end, because some intrinsics definitions rely on
// other intrinsics definitions.
//
// Also, some intrinsics are defined with static inline
// functions rather than macros, so we sometimes need
// to check if the macro has been defined before undefining
// it.
// Note that it may be a good idea to redefine as
// many intrinsics as possible by using static inline
// functions rather than macros, because macros can
// be dangerous. Note that this is not possible for
// all the intrinsics, because some intrinsics require
// immediate values for their parameters.
// For a simple example of dangerous definitions which did happen:
// if [b] has type [uint8_t *] and you define the
// following macro:
// [> #define get(x) ((uint32_t*) x)[0]
// If you call: [get(b + 16)] then the coercion to
// [(uint32_t*)] precedes the address shift [+ 16],
// leading to an incorrect address computation.
// The solution is to define:
// [> #define get(x) ((uint32_t*)(x))[0]
// (with parentheses around [x]).
// This kind of problems wouldn't happen with static inline
// functions.

#ifdef Lib_IntVector_Intrinsics_vec128_load32_le
#undef Lib_IntVector_Intrinsics_vec128_load32_le
#endif
#define Lib_IntVector_Intrinsics_vec128_load32_le(x0) \
  Lib_IntVector_Intrinsics_vec128_load32_le_debug(x0)

#ifdef Lib_IntVector_Intrinsics_vec128_load32_be
#undef Lib_IntVector_Intrinsics_vec128_load32_be
#endif
#define Lib_IntVector_Intrinsics_vec128_load32_be(x0) \
  Lib_IntVector_Intrinsics_vec128_load32_be_debug(x0)

#ifdef Lib_IntVector_Intrinsics_vec128_load64_le
#undef Lib_IntVector_Intrinsics_vec128_load64_le
#endif
#define Lib_IntVector_Intrinsics_vec128_load64_le(x0) \
  Lib_IntVector_Intrinsics_vec128_load64_le_debug(x0)

#ifdef Lib_IntVector_Intrinsics_vec128_store32_le
#undef Lib_IntVector_Intrinsics_vec128_store32_le
#endif
#define Lib_IntVector_Intrinsics_vec128_store32_le(x0, x1) \
  Lib_IntVector_Intrinsics_vec128_store32_le_debug(x0, x1)

#ifdef Lib_IntVector_Intrinsics_vec128_store32_be
#undef Lib_IntVector_Intrinsics_vec128_store32_be
#endif
#define Lib_IntVector_Intrinsics_vec128_store32_be(x0, x1) \
  Lib_IntVector_Intrinsics_vec128_store32_be_debug(x0, x1)

#ifdef Lib_IntVector_Intrinsics_vec128_store64_le
#undef Lib_IntVector_Intrinsics_vec128_store64_le
#endif
#define Lib_IntVector_Intrinsics_vec128_store64_le(x0, x1) \
  Lib_IntVector_Intrinsics_vec128_store64_le_debug(x0, x1)

#undef Lib_IntVector_Intrinsics_vec128_add32
#define Lib_IntVector_Intrinsics_vec128_add32(x0, x1) \
  Lib_IntVector_Intrinsics_vec128_add32_debug(x0, x1)

#undef Lib_IntVector_Intrinsics_vec128_add64
#define Lib_IntVector_Intrinsics_vec128_add64(x0, x1) \
  Lib_IntVector_Intrinsics_vec128_add64_debug(x0, x1)

#undef Lib_IntVector_Intrinsics_vec128_xor
#define Lib_IntVector_Intrinsics_vec128_xor(x0, x1) \
  Lib_IntVector_Intrinsics_vec128_xor_debug(x0, x1)

#undef Lib_IntVector_Intrinsics_vec128_and
#define Lib_IntVector_Intrinsics_vec128_and(x0, x1) \
  Lib_IntVector_Intrinsics_vec128_and_debug(x0, x1)

#undef Lib_IntVector_Intrinsics_vec128_eq32
#define Lib_IntVector_Intrinsics_vec128_eq32(x0, x1) \
  Lib_IntVector_Intrinsics_vec128_eq32_debug(x0, x1)

#undef Lib_IntVector_Intrinsics_vec128_eq64
#define Lib_IntVector_Intrinsics_vec128_eq64(x0, x1) \
  Lib_IntVector_Intrinsics_vec128_eq64_debug(x0, x1)

#undef Lib_IntVector_Intrinsics_vec128_extract32
#define Lib_IntVector_Intrinsics_vec128_extract32(x0, x1) \
  Lib_IntVector_Intrinsics_vec128_extract32_debug(x0, x1)

#undef Lib_IntVector_Intrinsics_vec128_extract64
#define Lib_IntVector_Intrinsics_vec128_extract64(x0, x1) \
  Lib_IntVector_Intrinsics_vec128_extract64_debug(x0, x1)

#undef Lib_IntVector_Intrinsics_vec128_gt32
#define Lib_IntVector_Intrinsics_vec128_gt32(x0, x1) \
  Lib_IntVector_Intrinsics_vec128_gt32_debug(x0, x1)

#undef Lib_IntVector_Intrinsics_vec128_gt64
#define Lib_IntVector_Intrinsics_vec128_gt64(x0, x1) \
  Lib_IntVector_Intrinsics_vec128_gt64_debug(x0, x1)

#undef Lib_IntVector_Intrinsics_vec128_insert32
#define Lib_IntVector_Intrinsics_vec128_insert32(x0, x1, x2)       \
  Lib_IntVector_Intrinsics_vec128_insert32_debug(x0, x1, x2)

#undef Lib_IntVector_Intrinsics_vec128_insert64
#define Lib_IntVector_Intrinsics_vec128_insert64(x0, x1, x2)       \
  Lib_IntVector_Intrinsics_vec128_insert64_debug(x0, x1, x2)

#undef Lib_IntVector_Intrinsics_vec128_interleave_high32
#define Lib_IntVector_Intrinsics_vec128_interleave_high32(x0, x1)       \
  Lib_IntVector_Intrinsics_vec128_interleave_high32_debug(x0, x1)

#undef Lib_IntVector_Intrinsics_vec128_interleave_high64
#define Lib_IntVector_Intrinsics_vec128_interleave_high64(x0, x1)       \
  Lib_IntVector_Intrinsics_vec128_interleave_high64_debug(x0, x1)

#undef Lib_IntVector_Intrinsics_vec128_interleave_low32
#define Lib_IntVector_Intrinsics_vec128_interleave_low32(x0, x1)       \
  Lib_IntVector_Intrinsics_vec128_interleave_low32_debug(x0, x1)

#undef Lib_IntVector_Intrinsics_vec128_interleave_low64
#define Lib_IntVector_Intrinsics_vec128_interleave_low64(x0, x1)       \
  Lib_IntVector_Intrinsics_vec128_interleave_low64_debug(x0, x1)

#undef Lib_IntVector_Intrinsics_vec128_load32
#define Lib_IntVector_Intrinsics_vec128_load32(x0)      \
  Lib_IntVector_Intrinsics_vec128_load32_debug(x0)

#undef Lib_IntVector_Intrinsics_vec128_load32s
#define Lib_IntVector_Intrinsics_vec128_load32s(x0, x1, x2, x3)    \
  Lib_IntVector_Intrinsics_vec128_load32s_debug(x0, x1, x2, x3)

#undef Lib_IntVector_Intrinsics_vec128_load64
#define Lib_IntVector_Intrinsics_vec128_load64(x0)       \
  Lib_IntVector_Intrinsics_vec128_load64_debug(x0)

#undef Lib_IntVector_Intrinsics_vec128_lognot
#define Lib_IntVector_Intrinsics_vec128_lognot(x0)       \
  Lib_IntVector_Intrinsics_vec128_lognot_debug(x0)

#undef Lib_IntVector_Intrinsics_vec128_mul64
#define Lib_IntVector_Intrinsics_vec128_mul64(x0, x1)       \
  Lib_IntVector_Intrinsics_vec128_mul64_debug(x0, x1)

#undef Lib_IntVector_Intrinsics_vec128_or
#define Lib_IntVector_Intrinsics_vec128_or(x0, x1)       \
  Lib_IntVector_Intrinsics_vec128_or_debug(x0, x1)

#undef Lib_IntVector_Intrinsics_vec128_rotate_left32
#define Lib_IntVector_Intrinsics_vec128_rotate_left32(x0, x1)       \
  Lib_IntVector_Intrinsics_vec128_rotate_left32_debug(x0, x1)

#undef Lib_IntVector_Intrinsics_vec128_rotate_right32
#define Lib_IntVector_Intrinsics_vec128_rotate_right32(x0, x1)       \
  Lib_IntVector_Intrinsics_vec128_rotate_right32_debug(x0, x1)

#undef Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32
#define Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(x0, x1)       \
  Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32_debug(x0, x1)

#undef Lib_IntVector_Intrinsics_vec128_shift_left64
#define Lib_IntVector_Intrinsics_vec128_shift_left64(x0, x1)       \
  Lib_IntVector_Intrinsics_vec128_shift_left64_debug(x0, x1)

#undef Lib_IntVector_Intrinsics_vec128_shift_right64
#define Lib_IntVector_Intrinsics_vec128_shift_right64(x0, x1)       \
  Lib_IntVector_Intrinsics_vec128_shift_right64_debug(x0, x1)

#undef Lib_IntVector_Intrinsics_vec128_shift_right32
#define Lib_IntVector_Intrinsics_vec128_shift_right32(x0, x1)       \
  Lib_IntVector_Intrinsics_vec128_shift_right32_debug(x0, x1)

#undef Lib_IntVector_Intrinsics_vec128_smul64
#define Lib_IntVector_Intrinsics_vec128_smul64(x0, x1)       \
  Lib_IntVector_Intrinsics_vec128_smul64_debug(x0, x1)

#undef Lib_IntVector_Intrinsics_vec128_sub64
#define Lib_IntVector_Intrinsics_vec128_sub64(x0, x1)       \
  Lib_IntVector_Intrinsics_vec128_sub64_debug(x0, x1)


#endif // DEBUG_VECTOR_TRACE

#endif // __LIBINTVECTOR_DEBUG_H_INCLUDED
