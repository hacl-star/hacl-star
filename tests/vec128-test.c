/* The following file defines tests for the vector128 functions.
 * It was mostly designed to help with the implementation of support
 * for new architectures.
 */

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdbool.h>
#include <time.h>

#include "libintvector.h"
#include "test_helpers.h"

typedef Lib_IntVector_Intrinsics_vec128 vec128;

static inline void print_buf(unsigned char *msg, uint8_t *buf) {
  printf("static uint8_t %s[16] = {\n  ", msg);
  for (size_t i = 0; i < 16; i++) {
    printf("0x%02xU",buf[i]);
    if (i == 7) { printf(",\n  "); }
    else if (i != 15) { printf(", "); }
  }
  printf("\n};\n\n");
}

static inline void print_vector(unsigned char *msg, vec128 *vec) {
  uint8_t tmp[16];
  Lib_IntVector_Intrinsics_vec128_store_le(tmp, vec);
  print_buf(msg, tmp);
}

void initialize_buf(uint8_t *buf) {
  unsigned int i = 0;
  for(; i < 16; i++) {
    buf[i] = i;
  }
}

void initialize_vector(vec128 *vec) {
  uint8_t tmp[16];
  initialize_buf(tmp);
  Lib_IntVector_Intrinsics_vec128_load_le(vec, tmp);
}

void initialize_buf8(uint8_t x0, uint8_t x1, uint8_t x2, uint8_t x3, uint8_t x4,
                     uint8_t x5, uint8_t x6, uint8_t x7, uint8_t x8, uint8_t x9,
                     uint8_t x10, uint8_t x11, uint8_t x12, uint8_t x13,
                     uint8_t x14, uint8_t x15, uint8_t buf[16]) {
  buf[0] = x0; buf[1] = x1; buf[2] = x2; buf[3] = x3;
  buf[4] = x4; buf[5] = x5; buf[6] = x6; buf[7] = x7;
  buf[8] = x8; buf[9] = x9; buf[10] = x10; buf[11] = x11;
  buf[12] = x12; buf[13] = x13; buf[14] = x14; buf[15] = x15;
}

vec128 initialize_vector8(uint8_t x0, uint8_t x1, uint8_t x2, uint8_t x3, uint8_t x4,
                          uint8_t x5, uint8_t x6, uint8_t x7, uint8_t x8, uint8_t x9,
                          uint8_t x10, uint8_t x11, uint8_t x12, uint8_t x13,
                          uint8_t x14, uint8_t x15) {
  uint8_t tmp[16]
  initialize_buf8(x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,tmp);
  vec128 vec;
  Lib_IntVector_Intrinsics_vec128_load_le(&vec, tmp);
  return vec;
}

void initialize_buf16(uint16_t x0, uint16_t x1, uint16_t x2, uint16_t x3,
                      uint16_t x4, uint16_t x5, uint16_t x6, uint16_t x7,
                      uint16_t buf[8]) {
  buf[0] = x0; buf[1] = x1; buf[2] = x2; buf[3] = x3;
  buf[4] = x4; buf[5] = x5; buf[6] = x6; buf[7] = x7;
}

vec128 initialize_vector16(uint16_t x0, uint16_t x1, uint16_t x2, uint16_t x3,
                          uint16_t x4, uint16_t x5, uint16_t x6, uint16_t x7) {
  uint32_t tmp[8]
  initialize_buf16(x0,x1,x2,x3,x4,x5,x6,x7,tmp);
  vec128 vec;
  Lib_IntVector_Intrinsics_vec128_load_le(&vec, tmp);
  return vec;
}

void initialize_buf32(uint32_t x0, uint32_t x1, uint32_t x2, uint32_t x3,
                      uint32_t buf[4]) {
  buf[0] = x0; buf[1] = x1; buf[2] = x2; buf[3] = x3;
}

vec128 initialize_vector32(uint32_t x0, uint32_t x1, uint32_t x2, uint32_t x3) {
  uint16_t tmp[8]
  initialize_buf32(x0,x1,x2,x3,tmp);
  vec128 vec;
  Lib_IntVector_Intrinsics_vec128_load_le(&vec, tmp);
  return vec;
}

static uint8_t bstore_le[16] = {
  0x00U, 0x01U, 0x02U, 0x03U, 0x04U, 0x05U, 0x06U, 0x07U,
  0x08U, 0x09U, 0x0aU, 0x0bU, 0x0cU, 0x0dU, 0x0eU, 0x0fU
};

static uint8_t bload_le[16] = {
  0x00U, 0x01U, 0x02U, 0x03U, 0x04U, 0x05U, 0x06U, 0x07U,
  0x08U, 0x09U, 0x0aU, 0x0bU, 0x0cU, 0x0dU, 0x0eU, 0x0fU
};

static uint8_t badd32[16] = {
  0x00U, 0x02U, 0x04U, 0x06U, 0x08U, 0x0aU, 0x0cU, 0x0eU,
  0x10U, 0x12U, 0x14U, 0x16U, 0x18U, 0x1aU, 0x1cU, 0x1eU
};

static uint8_t badd64[16] = {
  0x00U, 0x02U, 0x04U, 0x06U, 0x08U, 0x0aU, 0x0cU, 0x0eU,
  0x10U, 0x12U, 0x14U, 0x16U, 0x18U, 0x1aU, 0x1cU, 0x1eU
};

static uint8_t band[16] = {
  0x00U, 0x01U, 0x02U, 0x03U, 0x04U, 0x05U, 0x06U, 0x07U,
  0x08U, 0x09U, 0x0aU, 0x0bU, 0x0cU, 0x0dU, 0x0eU, 0x0fU
};

static uint8_t beq32[16] = {
  0xffU, 0xffU, 0xffU, 0xffU, 0x00U, 0x00U, 0x00U, 0x00U,
  0xffU, 0xffU, 0xffU, 0xffU, 0xffU, 0xffU, 0xffU, 0xffU
};

static uint8_t beq64[16] = {
  0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U,
  0xffU, 0xffU, 0xffU, 0xffU, 0xffU, 0xffU, 0xffU, 0xffU
};

static uint8_t bgt32[16] = {
  0x00U, 0x00U, 0x00U, 0x00U, 0xffU, 0xffU, 0xffU, 0xffU,
  0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U
};

static uint8_t bgt64[16] = {
  0xffU, 0xffU, 0xffU, 0xffU, 0xffU, 0xffU, 0xffU, 0xffU,
  0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U
};

static uint8_t binsert32[16] = {
  0x00U, 0x01U, 0x02U, 0x03U, 0x04U, 0x05U, 0x06U, 0x07U,
  0x08U, 0x09U, 0x0aU, 0x0bU, 0x11U, 0x00U, 0x00U, 0x00U
};

static uint8_t binsert64[16] = {
  0x00U, 0x01U, 0x02U, 0x03U, 0x04U, 0x05U, 0x06U, 0x07U,
  0x17U, 0x17U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U
};

static uint8_t binterleave_high32[16] = {
  0x08U, 0x09U, 0x0aU, 0x0bU, 0x07U, 0x06U, 0x05U, 0x04U,
  0x0cU, 0x0dU, 0x0eU, 0x0fU, 0x03U, 0x02U, 0x01U, 0x00U
};

static uint8_t binterleave_high64[16] = {
  0x08U, 0x09U, 0x0aU, 0x0bU, 0x0cU, 0x0dU, 0x0eU, 0x0fU,
  0x07U, 0x06U, 0x05U, 0x04U, 0x03U, 0x02U, 0x01U, 0x00U
};

static uint8_t binterleave_low32[16] = {
  0x00U, 0x01U, 0x02U, 0x03U, 0x0fU, 0x0eU, 0x0dU, 0x0cU,
  0x04U, 0x05U, 0x06U, 0x07U, 0x0bU, 0x0aU, 0x09U, 0x08U
};

static uint8_t binterleave_low64[16] = {
  0x00U, 0x01U, 0x02U, 0x03U, 0x04U, 0x05U, 0x06U, 0x07U,
  0x0fU, 0x0eU, 0x0dU, 0x0cU, 0x0bU, 0x0aU, 0x09U, 0x08U
};

static uint8_t bload32[16] = {
  0xffU, 0xffU, 0x01U, 0x00U, 0xffU, 0xffU, 0x01U, 0x00U,
  0xffU, 0xffU, 0x01U, 0x00U, 0xffU, 0xffU, 0x01U, 0x00U
};

static uint8_t bload32s[16] = {
  0x00U, 0x00U, 0x00U, 0x00U, 0x01U, 0x00U, 0x00U, 0x00U,
  0x02U, 0x00U, 0x00U, 0x00U, 0x03U, 0x00U, 0x00U, 0x00U
};

static uint8_t bload64[16] = {
  0x07U, 0x06U, 0x05U, 0x04U, 0x03U, 0x02U, 0x01U, 0x00U,
  0x07U, 0x06U, 0x05U, 0x04U, 0x03U, 0x02U, 0x01U, 0x00U
};

static uint8_t blognot[16] = {
  0xffU, 0xfeU, 0xfdU, 0xfcU, 0xfbU, 0xfaU, 0xf9U, 0xf8U,
  0xf7U, 0xf6U, 0xf5U, 0xf4U, 0xf3U, 0xf2U, 0xf1U, 0xf0U
};

static uint8_t bmul64[16] = {
  0x00U, 0x0fU, 0x2cU, 0x56U, 0x50U, 0x3fU, 0x24U, 0x00U,
  0x38U, 0x6fU, 0xa4U, 0xd6U, 0x98U, 0x5fU, 0x2cU, 0x00U
};

static uint8_t bor[16] = {
  0x0fU, 0x0fU, 0x0fU, 0x0fU, 0x0fU, 0x0fU, 0x0fU, 0x0fU,
  0x0fU, 0x0fU, 0x0fU, 0x0fU, 0x0fU, 0x0fU, 0x0fU, 0x0fU
};

static uint8_t brotate_left32_0[16] = {
  0x00U, 0x01U, 0x02U, 0x03U, 0x04U, 0x05U, 0x06U, 0x07U,
  0x08U, 0x09U, 0x0aU, 0x0bU, 0x0cU, 0x0dU, 0x0eU, 0x0fU
};

static uint8_t brotate_left32_8[16] = {
  0x03U, 0x00U, 0x01U, 0x02U, 0x07U, 0x04U, 0x05U, 0x06U,
  0x0bU, 0x08U, 0x09U, 0x0aU, 0x0fU, 0x0cU, 0x0dU, 0x0eU
};

static uint8_t brotate_left32_16[16] = {
  0x02U, 0x03U, 0x00U, 0x01U, 0x06U, 0x07U, 0x04U, 0x05U,
  0x0aU, 0x0bU, 0x08U, 0x09U, 0x0eU, 0x0fU, 0x0cU, 0x0dU
};

static uint8_t brotate_left32_24[16] = {
  0x01U, 0x02U, 0x03U, 0x00U, 0x05U, 0x06U, 0x07U, 0x04U,
  0x09U, 0x0aU, 0x0bU, 0x08U, 0x0dU, 0x0eU, 0x0fU, 0x0cU
};

static uint8_t brotate_left32_3[16] = {
  0x00U, 0x08U, 0x10U, 0x18U, 0x20U, 0x28U, 0x30U, 0x38U,
  0x40U, 0x48U, 0x50U, 0x58U, 0x60U, 0x68U, 0x70U, 0x78U
};

static uint8_t brotate_left32_7[16] = {
  0x01U, 0x80U, 0x00U, 0x81U, 0x03U, 0x82U, 0x02U, 0x83U,
  0x05U, 0x84U, 0x04U, 0x85U, 0x07U, 0x86U, 0x06U, 0x87U
};

static uint8_t brotate_left32_12[16] = {
  0x30U, 0x00U, 0x10U, 0x20U, 0x70U, 0x40U, 0x50U, 0x60U,
  0xb0U, 0x80U, 0x90U, 0xa0U, 0xf0U, 0xc0U, 0xd0U, 0xe0U
};

static uint8_t brotate_left32_21[16] = {
  0x40U, 0x60U, 0x00U, 0x20U, 0xc0U, 0xe0U, 0x80U, 0xa0U,
  0x41U, 0x61U, 0x01U, 0x21U, 0xc1U, 0xe1U, 0x81U, 0xa1U
};

static uint8_t brotate_right_lanes32_0[16] = {
  0x00U, 0x01U, 0x02U, 0x03U, 0x04U, 0x05U, 0x06U, 0x07U,
  0x08U, 0x09U, 0x0aU, 0x0bU, 0x0cU, 0x0dU, 0x0eU, 0x0fU
};

static uint8_t brotate_right_lanes32_1[16] = {
  0x04U, 0x05U, 0x06U, 0x07U, 0x08U, 0x09U, 0x0aU, 0x0bU,
  0x0cU, 0x0dU, 0x0eU, 0x0fU, 0x00U, 0x01U, 0x02U, 0x03U
};

static uint8_t brotate_right_lanes32_2[16] = {
  0x08U, 0x09U, 0x0aU, 0x0bU, 0x0cU, 0x0dU, 0x0eU, 0x0fU,
  0x00U, 0x01U, 0x02U, 0x03U, 0x04U, 0x05U, 0x06U, 0x07U
};

static uint8_t brotate_right_lanes32_3[16] = {
  0x0cU, 0x0dU, 0x0eU, 0x0fU, 0x00U, 0x01U, 0x02U, 0x03U,
  0x04U, 0x05U, 0x06U, 0x07U, 0x08U, 0x09U, 0x0aU, 0x0bU
};

static uint8_t bshift_left64_0[16] = {
  0x00U, 0x01U, 0x02U, 0x03U, 0x04U, 0x05U, 0x06U, 0x07U,
  0x08U, 0x09U, 0x0aU, 0x0bU, 0x0cU, 0x0dU, 0x0eU, 0x0fU
};

static uint8_t bshift_left64_8[16] = {
  0x00U, 0x00U, 0x01U, 0x02U, 0x03U, 0x04U, 0x05U, 0x06U,
  0x00U, 0x08U, 0x09U, 0x0aU, 0x0bU, 0x0cU, 0x0dU, 0x0eU
};

static uint8_t bshift_left64_16[16] = {
  0x00U, 0x00U, 0x00U, 0x01U, 0x02U, 0x03U, 0x04U, 0x05U,
  0x00U, 0x00U, 0x08U, 0x09U, 0x0aU, 0x0bU, 0x0cU, 0x0dU
};

static uint8_t bshift_left64_9[16] = {
  0x00U, 0x00U, 0x02U, 0x04U, 0x06U, 0x08U, 0x0aU, 0x0cU,
  0x00U, 0x10U, 0x12U, 0x14U, 0x16U, 0x18U, 0x1aU, 0x1cU
};

static uint8_t bshift_right64_0[16] = {
  0x00U, 0x01U, 0x02U, 0x03U, 0x04U, 0x05U, 0x06U, 0x07U,
  0x08U, 0x09U, 0x0aU, 0x0bU, 0x0cU, 0x0dU, 0x0eU, 0x0fU
};

static uint8_t bshift_right64_8[16] = {
  0x01U, 0x02U, 0x03U, 0x04U, 0x05U, 0x06U, 0x07U, 0x00U,
  0x09U, 0x0aU, 0x0bU, 0x0cU, 0x0dU, 0x0eU, 0x0fU, 0x00U
};

static uint8_t bshift_right64_16[16] = {
  0x02U, 0x03U, 0x04U, 0x05U, 0x06U, 0x07U, 0x00U, 0x00U,
  0x0aU, 0x0bU, 0x0cU, 0x0dU, 0x0eU, 0x0fU, 0x00U, 0x00U
};

static uint8_t bshift_right64_9[16] = {
  0x00U, 0x81U, 0x01U, 0x82U, 0x02U, 0x83U, 0x03U, 0x00U,
  0x04U, 0x85U, 0x05U, 0x86U, 0x06U, 0x87U, 0x07U, 0x00U
};

static uint8_t bsmul64[16] = {
  0x00U, 0x07U, 0x14U, 0x26U, 0x20U, 0x17U, 0x0cU, 0x00U,
  0x38U, 0x6fU, 0xa4U, 0xd6U, 0x98U, 0x5fU, 0x2cU, 0x00U
};

static uint8_t bsub64[16] = {
  0xf1U, 0xf2U, 0xf4U, 0xf6U, 0xf8U, 0xfaU, 0xfcU, 0xfeU,
  0x01U, 0x03U, 0x05U, 0x07U, 0x09U, 0x0bU, 0x0dU, 0x0fU
};

static uint8_t bxor[16] = {
  0x0fU, 0x0fU, 0x0fU, 0x0fU, 0x0fU, 0x0fU, 0x0fU, 0x0fU,
  0x0fU, 0x0fU, 0x0fU, 0x0fU, 0x0fU, 0x0fU, 0x0fU, 0x0fU
};

static uint8_t bvec0[16] = {
  0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U,
  0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U
};

#define compare_and_print_vec(msg, vec0, vec1)                           \
  printf("%s:\n", msg);                                                  \
  if (!compare_and_print(16, (uint8_t*) &vec0, (uint8_t*) &vec1)) { ok = false; }

int main() {
  bool ok = true;

  vec128 vec0, vec1;
  uint32_t x32;
  uint64_t x64;
  uint8_t tmp[16];
  
  /*  initialize_vector(&vec0);
  Lib_IntVector_Intrinsics_vec128_store_le(tmp, vec0);
  printf("store_le:\n");
  ok = ok && compare_and_print(16, tmp, (uint8_t*) &bstore_le);
  //  print_buf("bstore_le", tmp);

  initialize_buf(tmp);
  vec0 = Lib_IntVector_Intrinsics_vec128_load_le(tmp);
  compare_and_print_vec("load_le", vec0, bload_le);
  //  print_vector("bload_le", &vec0); */
  
  initialize_vector(&vec0);
  initialize_vector(&vec1);
  vec0 = Lib_IntVector_Intrinsics_vec128_add32(vec0, vec1);
  compare_and_print_vec("add32", vec0, badd32);
  //  print_vector("badd32", &vec0);

  initialize_vector(&vec0);
  initialize_vector(&vec1);
  vec0 = Lib_IntVector_Intrinsics_vec128_add64(vec0, vec1);
  compare_and_print_vec("add64", vec0, badd64);
  //  print_vector("badd64", &vec0);

  initialize_vector(&vec0);
  initialize_vector(&vec1);
  vec0 = Lib_IntVector_Intrinsics_vec128_and(vec0, vec1);
  compare_and_print_vec("and", vec0, band);
  //  print_vector("band", &vec0);

  initialize_vector(&vec0);
  vec1 = initialize_vector8(0,1,2,3,4,0,6,7,8,9,10,11,12,13,14,15);
  vec0 = Lib_IntVector_Intrinsics_vec128_eq32(vec0, vec1);
  compare_and_print_vec("eq32", vec0, beq32);
  //  print_vector("beq32", &vec0);

  initialize_vector(&vec0);
  vec1 = initialize_vector8(0,1,2,3,4,0,6,7,8,9,10,11,12,13,14,15);
  vec0 = Lib_IntVector_Intrinsics_vec128_eq64(vec0, vec1);
  compare_and_print_vec("eq64", vec0, beq64);
  //  print_vector("beq64", &vec0);

  initialize_vector(&vec0);
  x32 = Lib_IntVector_Intrinsics_vec128_extract32(vec0, 3);
  printf("extract32:\n");
  printf("computed:%08x\n", x32);
  printf("expected:%08x\n", 0x0f0e0d0c);
  if (x32 == 0x0f0e0d0c) { printf("Success!\n"); } else { ok = false; printf("**FAILED**\n"); }

  initialize_vector(&vec0);
  x64 = Lib_IntVector_Intrinsics_vec128_extract64(vec0, 1);
  printf("extract64:\n");
  printf("computed:%lx\n", x64);
  printf("expected:%lx\n", 0xf0e0d0c0b0a0908);
  if (x64 == 0xf0e0d0c0b0a0908) { printf("Success!\n"); } else { ok = false; printf("**FAILED**\n"); }

  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec1 = initialize_vector8(0,1,2,3,4,6,4,7,8,9,10,11,12,13,14,15);
  vec0 = Lib_IntVector_Intrinsics_vec128_gt32(vec0, vec1);
  compare_and_print_vec("gt32", vec0, bgt32);
  //print_vector("bgt32", &vec0);

  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec1 = initialize_vector8(0,1,2,3,4,6,4,7,8,9,10,11,12,13,14,15);
  vec0 = Lib_IntVector_Intrinsics_vec128_gt64(vec0, vec1);
  compare_and_print_vec("gt64", vec0, bgt64);
  //print_vector("bgt64", &vec0);

  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec0 = Lib_IntVector_Intrinsics_vec128_insert32(vec0, 17, 3);
  compare_and_print_vec("insert32", vec0, binsert32);
  //  print_vector("binsert32", &vec0);

  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec0 = Lib_IntVector_Intrinsics_vec128_insert64(vec0, 0x1717, 1);
  compare_and_print_vec("insert64", vec0, binsert64);
  //  print_vector("binsert64", &vec0);

  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec1 = initialize_vector8(15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0);
  vec0 = Lib_IntVector_Intrinsics_vec128_interleave_high32(vec0, vec1);
  compare_and_print_vec("interlave_high32", vec0, binterleave_high32);
  //  print_vector("interleave_high32", &vec0);

  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec1 = initialize_vector8(15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0);
  vec0 = Lib_IntVector_Intrinsics_vec128_interleave_high64(vec0, vec1);
  compare_and_print_vec("interlave_high64", vec0, binterleave_high64);
  //  print_vector("interleave_high64", &vec0);

  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec1 = initialize_vector8(15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0);
  vec0 = Lib_IntVector_Intrinsics_vec128_interleave_low32(vec0, vec1);
  compare_and_print_vec("interlave_low32", vec0, binterleave_low32);
  //  print_vector("interleave_low32", &vec0);

  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec1 = initialize_vector8(15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0);
  vec0 = Lib_IntVector_Intrinsics_vec128_interleave_low64(vec0, vec1);
  compare_and_print_vec("interlave_low64", vec0, binterleave_low64);
  //  print_vector("interleave_low64", &vec0);

  vec0 = Lib_IntVector_Intrinsics_vec128_load32(0x01ffff);
  compare_and_print_vec("load32", vec0, bload32);
  //  print_vector("bload32", &vec0);

  vec0 = Lib_IntVector_Intrinsics_vec128_load32s(0,1,2,3);
  compare_and_print_vec("load32s", vec0, bload32s);
  //  print_vector("bload32s", &vec0);

  vec0 = Lib_IntVector_Intrinsics_vec128_load64(0x0001020304050607);
  compare_and_print_vec("load64", vec0, bload64);
  //  print_vector("bload64", &vec0);

  initialize_vector(&vec0);
  vec0 = Lib_IntVector_Intrinsics_vec128_lognot(vec0);
  compare_and_print_vec("lognot", vec0, blognot);
  //  print_vector("blognot", &vec0);

  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec1 = initialize_vector8(15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0);
  vec0 = Lib_IntVector_Intrinsics_vec128_mul64(vec0, vec1);
  compare_and_print_vec("mul64", vec0, bmul64);
  //  print_vector("bmul64", &vec0);

  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec1 = initialize_vector8(15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0);
  vec0 = Lib_IntVector_Intrinsics_vec128_or(vec0, vec1);
  compare_and_print_vec("or", vec0, bor);
  //  print_vector("bor", &vec0);

  // Rotate left 32
  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(vec0, 0);
  compare_and_print_vec("rotate_left32(0)", vec0, brotate_left32_0);
  //  print_vector("brotate_left32_0", &vec0);

  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(vec0, 8);
  compare_and_print_vec("rotate_left32(8)", vec0, brotate_left32_8);
  //  print_vector("brotate_left32_8", &vec0);

  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(vec0, 16);
  compare_and_print_vec("rotate_left32(16)", vec0, brotate_left32_16);
  //  print_vector("brotate_left32_16", &vec0);

  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(vec0, 24);
  compare_and_print_vec("rotate_left32(24)", vec0, brotate_left32_24);
  //  print_vector("brotate_left32_24", &vec0);

  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(vec0, 3);
  compare_and_print_vec("rotate_left32(3)", vec0, brotate_left32_3);
  //  print_vector("brotate_left32_3", &vec0);

  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(vec0, 7);
  compare_and_print_vec("rotate_left32(7)", vec0, brotate_left32_7);
  //  print_vector("brotate_left32_7", &vec0);

  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(vec0, 12);
  compare_and_print_vec("rotate_left32(12)", vec0, brotate_left32_12);
  //  print_vector("brotate_left32_12", &vec0);

  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(vec0, 21);
  compare_and_print_vec("rotate_left32(21)", vec0, brotate_left32_21);
  //  print_vector("brotate_left32_21", &vec0);

  // Rotate right lanes 32
  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(vec0, 0);
  compare_and_print_vec("rotate_right_lanes32(0)", vec0, brotate_right_lanes32_0);
//  print_vector("brotate_right_lanes32_0", &vec0);

  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(vec0, 1);
  compare_and_print_vec("rotate_right_lanes32(1)", vec0, brotate_right_lanes32_1);
//  print_vector("brotate_right_lanes32_1", &vec0);

  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(vec0, 2);
  compare_and_print_vec("rotate_right_lanes32(2)", vec0, brotate_right_lanes32_2);
//  print_vector("brotate_right_lanes32_2", &vec0);

  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(vec0, 3);
  compare_and_print_vec("rotate_right_lanes32(3)", vec0, brotate_right_lanes32_3);
//  print_vector("brotate_right_lanes32_3", &vec0);

  // Shift left
  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec0 = Lib_IntVector_Intrinsics_vec128_shift_left64(vec0, 0);
  compare_and_print_vec("shift_left64(0)", vec0, bshift_left64_0);
//  print_vector("bshift_left64_0", &vec0);

  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec0 = Lib_IntVector_Intrinsics_vec128_shift_left64(vec0, 8);
  compare_and_print_vec("shift_left64(8)", vec0, bshift_left64_8);
//  print_vector("bshift_left64_8", &vec0);

  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec0 = Lib_IntVector_Intrinsics_vec128_shift_left64(vec0, 16);
  compare_and_print_vec("shift_left(16)", vec0, bshift_left64_16);
//  print_vector("bshift_left64_16", &vec0);
  
  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec0 = Lib_IntVector_Intrinsics_vec128_shift_left64(vec0, 9);
  compare_and_print_vec("shift_left(9)", vec0, bshift_left64_9);
//  print_vector("bshift_left64_9", &vec0);

  // Shift right
  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec0 = Lib_IntVector_Intrinsics_vec128_shift_right64(vec0, 0);
  compare_and_print_vec("shift_right64(0)", vec0, bshift_right64_0);
//  print_vector("bshift_right64_0", &vec0);

  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec0 = Lib_IntVector_Intrinsics_vec128_shift_right64(vec0, 8);
  compare_and_print_vec("shift_right64(8)", vec0, bshift_right64_8);
//  print_vector("bshift_right64_8", &vec0);

  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec0 = Lib_IntVector_Intrinsics_vec128_shift_right64(vec0, 16);
  compare_and_print_vec("shift_right64(16)", vec0, bshift_right64_16);
//  print_vector("bshift_right64_16", &vec0);

  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec0 = Lib_IntVector_Intrinsics_vec128_shift_right64(vec0, 9);
  compare_and_print_vec("shift_right64(9)", vec0, bshift_right64_9);
//  print_vector("bshift_right64_9", &vec0);
 
  // Misc remaining
  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec0 = Lib_IntVector_Intrinsics_vec128_smul64(vec0, 0x0001020304050607);
  compare_and_print_vec("smul64", vec0, bsmul64);
//  print_vector("bsmul64", &vec0);

  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec1 = initialize_vector8(15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0);
  vec0 = Lib_IntVector_Intrinsics_vec128_sub64(vec0, vec1);
  compare_and_print_vec("sub64", vec0, bsub64);
//  print_vector("bsub64", &vec0);

  vec0 = initialize_vector8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  vec1 = initialize_vector8(15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0);
  vec0 = Lib_IntVector_Intrinsics_vec128_xor(vec0, vec1);
  compare_and_print_vec("xor", vec0, bxor);
//  print_vector("bxor", &vec0);

  vec0 = Lib_IntVector_Intrinsics_vec128_zero;
  compare_and_print_vec("zero", vec0, bvec0);
//  print_vector("bvec0", &vec0);

  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}
