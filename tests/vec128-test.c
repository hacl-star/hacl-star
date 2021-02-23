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

static inline void print_buf8(unsigned char *msg, uint8_t *buf) {
  /*  printf("static uint8_t %s[16] = {\n  ", msg);
  for (size_t i = 0; i < 16; i++) {
    printf("0x%02xU",buf[i]);
    if (i == 7) { printf(",\n  "); }
    else if (i != 15) { printf(", "); }
  }
  printf("\n};\n\n"); */
  printf("[> %s:\n", msg);
  printf("initialize_vector8(");
  for (size_t i = 0; i < 16; i++) {
    printf("0x%02xU",buf[i]);
    if(i < 15) { printf(","); }
  }
  printf(");\n");
}

static inline void print_vector8(unsigned char *msg, vec128 vec) {
  uint8_t tmp[16];
  Lib_IntVector_Intrinsics_vec128_store_le(tmp, vec);
  print_buf8(msg, tmp);
}

static inline void print_vector32(unsigned char *msg, vec128 vec) {
  //  printf("static uint32_t %s[4] = {\n  ", msg);
  //  printf("  0x%08xU, 0x%08xU,\n  0x%08xU, 0x%08xU",
  //         Lib_IntVector_Intrinsics_vec128_extract32(vec,0),
  //         Lib_IntVector_Intrinsics_vec128_extract32(vec,1),
  //         Lib_IntVector_Intrinsics_vec128_extract32(vec,2),
  //         Lib_IntVector_Intrinsics_vec128_extract32(vec,3));
  //  printf("\n};\n\n");
  printf("[> %s:\n", msg);
  printf("initialize_vector32(0x%08x,0x%08x,0x%08x,0x%08x);\n",
         Lib_IntVector_Intrinsics_vec128_extract32(vec,0),
         Lib_IntVector_Intrinsics_vec128_extract32(vec,1),
         Lib_IntVector_Intrinsics_vec128_extract32(vec,2),
         Lib_IntVector_Intrinsics_vec128_extract32(vec,3));
}

static inline void print_vector64(unsigned char *msg, vec128 vec) {
  //  printf("static uint64_t %s[2] = {\n  ", msg);
  //  printf("  0x%lxxU,\n  0x%lxxU",
  //         Lib_IntVector_Intrinsics_vec128_extract64(vec,0),
  //         Lib_IntVector_Intrinsics_vec128_extract64(vec,1));
  //  printf("\n};\n\n");
  printf("[> %s:\n", msg);
  printf("initialize_vector64(0x%lxUL,0x%lxUL);\n",
         (uint64_t) Lib_IntVector_Intrinsics_vec128_extract64(vec,0),
         (uint64_t) Lib_IntVector_Intrinsics_vec128_extract64(vec,1));
}

// Initilization of a vector as 0u, 1u, 2u, etc.
void initialize_buf(uint8_t *buf) {
  unsigned int i = 0;
  for(; i < 16; i++) {
    buf[i] = i;
  }
}

vec128 initialize_vector() {
  uint8_t tmp[16];
  initialize_buf(tmp);
  return Lib_IntVector_Intrinsics_vec128_load_le(tmp);
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
  uint8_t tmp[16];
  initialize_buf8(x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,tmp);
  return Lib_IntVector_Intrinsics_vec128_load_le(tmp);
}

/*void initialize_buf16(uint16_t x0, uint16_t x1, uint16_t x2, uint16_t x3,
                      uint16_t x4, uint16_t x5, uint16_t x6, uint16_t x7,
                      uint16_t buf[8]) {
  buf[0] = x0; buf[1] = x1; buf[2] = x2; buf[3] = x3;
  buf[4] = x4; buf[5] = x5; buf[6] = x6; buf[7] = x7;
}

vec128 initialize_vector16(uint16_t x0, uint16_t x1, uint16_t x2, uint16_t x3,
                          uint16_t x4, uint16_t x5, uint16_t x6, uint16_t x7) {
  uint16_t tmp[8];
  vec128 vec = 
  initialize_buf16(x0,x1,x2,x3,x4,x5,x6,x7,tmp);
  return Lib_IntVector_Intrinsics_vec128_load_le(tmp);
  }*/

/*void initialize_buf32(uint32_t x0, uint32_t x1, uint32_t x2, uint32_t x3,
                      uint32_t buf[4]) {
  buf[0] = x0; buf[1] = x1; buf[2] = x2; buf[3] = x3;
  }*/

vec128 initialize_vector32(uint32_t x0, uint32_t x1, uint32_t x2, uint32_t x3) {
  vec128 vec;
  vec = Lib_IntVector_Intrinsics_vec128_load32(x0);
  vec = Lib_IntVector_Intrinsics_vec128_insert32(vec, x1, 1);
  vec = Lib_IntVector_Intrinsics_vec128_insert32(vec, x2, 2);
  vec = Lib_IntVector_Intrinsics_vec128_insert32(vec, x3, 3);
  return vec;
  //  uint32_t tmp[4];
  //  initialize_buf32(x0,x1,x2,x3,tmp);
  //  return Lib_IntVector_Intrinsics_vec128_load_le(tmp);
}

//void initialize_buf64(uint64_t x0, uint64_t x1, uint64_t buf[4]) {
//  buf[0] = x0; buf[1] = x1;
//}

vec128 initialize_vector64(uint64_t x0, uint64_t x1) {
  //  uint64_t tmp[2];
  //  initialize_buf64(x0,x1, tmp);
  //  return Lib_IntVector_Intrinsics_vec128_load_le(tmp);
  vec128 vec;
  vec = Lib_IntVector_Intrinsics_vec128_load64(x0);
  vec = Lib_IntVector_Intrinsics_vec128_insert64(vec, x1, 1);
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
  0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U,
  0xffU, 0xffU, 0xffU, 0xffU, 0xffU, 0xffU, 0xffU, 0xffU
};

static uint8_t bgt64[16] = {
  0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U,
  0xffU, 0xffU, 0xffU, 0xffU, 0xffU, 0xffU, 0xffU, 0xffU
};

static uint8_t binsert32[16] = {
  0x00U, 0x00U, 0x00U, 0x00U, 0x01U, 0x00U, 0x00U, 0x00U,
  0x02U, 0x00U, 0x00U, 0x00U, 0x04U, 0x00U, 0x00U, 0x00U
};

static uint8_t binsert64[16] = {
  0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U,
  0x02U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U, 0x00U
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
  0x1fU, 0x95U, 0x8fU, 0x96U, 0x74U, 0x21U, 0x28U, 0x00U,
  0x38U, 0x8eU, 0x24U, 0x83U, 0x4aU, 0x17U, 0x82U, 0x02U
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

static inline bool compare_and_print_vec8_(vec128 comp, vec128 exp) {
  return compare_and_print(16, (uint8_t*) &comp, (uint8_t*) &exp);
}

static inline bool compare_and_print_vec32_(vec128 comp, vec128 exp) {
  printf("computed: ");
  printf("[%08x], ",Lib_IntVector_Intrinsics_vec128_extract32(comp,0));
  printf("[%08x], ",Lib_IntVector_Intrinsics_vec128_extract32(comp,1));
  printf("[%08x], ",Lib_IntVector_Intrinsics_vec128_extract32(comp,2));
  printf("[%08x]",Lib_IntVector_Intrinsics_vec128_extract32(comp,3));
  printf("\n");
  printf("expected: ");
  printf("[%08x], ",Lib_IntVector_Intrinsics_vec128_extract32(exp,0));
  printf("[%08x], ",Lib_IntVector_Intrinsics_vec128_extract32(exp,1));
  printf("[%08x], ",Lib_IntVector_Intrinsics_vec128_extract32(exp,2));
  printf("[%08x]",Lib_IntVector_Intrinsics_vec128_extract32(exp,3));
  printf("\n");
  bool ok = true;
  ok = ok & (Lib_IntVector_Intrinsics_vec128_extract32(comp,0) == Lib_IntVector_Intrinsics_vec128_extract32(exp,0));
  ok = ok & (Lib_IntVector_Intrinsics_vec128_extract32(comp,1) == Lib_IntVector_Intrinsics_vec128_extract32(exp,1));
  ok = ok & (Lib_IntVector_Intrinsics_vec128_extract32(comp,2) == Lib_IntVector_Intrinsics_vec128_extract32(exp,2));
  ok = ok & (Lib_IntVector_Intrinsics_vec128_extract32(comp,3) == Lib_IntVector_Intrinsics_vec128_extract32(exp,3));
  if (ok)
    printf("Success!\n");
  else
    printf("**FAILED**\n");
  return ok;
}

static inline bool compare_and_print_vec64_(vec128 comp, vec128 exp) {
  unsigned int len = 2;
  printf("computed: ");
  printf("[%lx], ",(uint64_t)Lib_IntVector_Intrinsics_vec128_extract64(comp,0));
  printf("[%lx]",(uint64_t)Lib_IntVector_Intrinsics_vec128_extract64(comp,1));
  printf("\n");
  printf("expected: ");
  printf("[%lx], ",(uint64_t)Lib_IntVector_Intrinsics_vec128_extract64(exp,0));
  printf("[%lx]",(uint64_t)Lib_IntVector_Intrinsics_vec128_extract64(exp,1));
  printf("\n");
  bool ok = true;
  ok = ok & (Lib_IntVector_Intrinsics_vec128_extract64(comp,0) == Lib_IntVector_Intrinsics_vec128_extract64(exp,0));
  ok = ok & (Lib_IntVector_Intrinsics_vec128_extract64(comp,1) == Lib_IntVector_Intrinsics_vec128_extract64(exp,1));
  if (ok)
    printf("Success!\n");
  else
    printf("**FAILED**\n");
  return ok;
}

#define compare_and_print_vec8(msg, vec0, vec1)                          \
  printf("%s:\n", msg);                                                  \
  if (!compare_and_print_vec8_(vec0, vec1)) { ok = false; }

#define compare_and_print_vec32(msg, vec0, vec1)                          \
  printf("%s:\n", msg);                                                   \
  if (!compare_and_print_vec32_(vec0, vec1)) { ok = false; }

#define compare_and_print_vec64(msg, vec0, vec1)                          \
  printf("%s:\n", msg);                                                   \
  if (!compare_and_print_vec64_(vec0, vec1)) { ok = false; }

int main() {
  bool ok = true;

  vec128 vec0, vec1;
  vec128 exp;
  uint32_t x32;
  uint64_t x64;
  uint8_t tmp[16];
  
  vec0 = initialize_vector32(0x0, 0x1, 0x2, 0x3);
  vec1 = initialize_vector32(0x10, 0x11, 0x12, 0x13);
  vec0 = Lib_IntVector_Intrinsics_vec128_add32(vec0, vec1);
  exp = initialize_vector32(0x00000010,0x00000012,0x00000014,0x00000016);
  compare_and_print_vec32("add32", vec0, exp);
  // print_vector32("add32", vec0);

  vec0 = initialize_vector64(0x1, 0x100);
  vec1 = initialize_vector64(0x10, 0x1000);
  vec0 = Lib_IntVector_Intrinsics_vec128_add64(vec0, vec1);
  exp = initialize_vector64(0x11UL,0x1100UL);
  compare_and_print_vec32("add64", vec0, exp);
  // print_vector64("add64", vec0);

  vec0 = initialize_vector32(0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f);
  vec1 = initialize_vector32(0x0c0d0e0f, 0x00010203, 0x04050607, 0x08090a0b);
  vec0 = Lib_IntVector_Intrinsics_vec128_and(vec0, vec1);
  exp = initialize_vector32(0x00010203,0x00010203,0x00010203,0x08090a0b);
  compare_and_print_vec8("and", vec0, exp);
  //print_vector32("and", vec0);

  vec0 = initialize_vector32(0x0, 0x1, 0x2, 0x3);
  vec1 = initialize_vector32(0x10, 0x1, 0x2, 0x13);
  vec0 = Lib_IntVector_Intrinsics_vec128_eq32(vec0, vec1);
  exp = initialize_vector32(0x00000000,0xffffffff,0xffffffff,0x00000000);
  compare_and_print_vec32("eq32", vec0, exp);
  //  print_vector32("eq32", vec0);

  vec0 = initialize_vector64(0x0, 0x1);
  vec1 = initialize_vector64(0x2, 0x1);
  vec0 = Lib_IntVector_Intrinsics_vec128_eq64(vec0, vec1);
  exp = initialize_vector64(0x0UL,0xffffffffffffffffUL);
  compare_and_print_vec32("eq64", vec0, exp);
  //  print_vector64("eq64", vec0);

  //vec0 = initialize_vector();
  vec0 = initialize_vector32(0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f);
  x32 = Lib_IntVector_Intrinsics_vec128_extract32(vec0, 3);
  printf("extract32:\n");
  printf("computed:%08x\n", x32);
  printf("expected:%08x\n", 0x0c0d0e0f);
  if (x32 == 0x0c0d0e0f) { printf("Success!\n"); } else { ok = false; printf("**FAILED**\n"); }

  //vec0 = initialize_vector();
  vec0 = initialize_vector64(0x00010203004050607, 0x08090a0b0c0d0e0f);
  x64 = Lib_IntVector_Intrinsics_vec128_extract64(vec0, 1);
  printf("extract64:\n");
  printf("computed:%lx\n", x64);
  printf("expected:%lx\n", 0x08090a0b0c0d0e0f);
  if (x64 == 0x08090a0b0c0d0e0f) { printf("Success!\n"); } else { ok = false; printf("**FAILED**\n"); }

  vec0 = initialize_vector32(0x0, 0x1, 0x0, 0x3);
  vec1 = initialize_vector32(0x0, 0x0, 0x1, 0x2);
  vec0 = Lib_IntVector_Intrinsics_vec128_gt32(vec0, vec1);
  exp = initialize_vector32(0x00000000,0xffffffff,0x00000000,0xffffffff);
  compare_and_print_vec32("gt32", vec0, exp);
  //  print_vector32("gt32", vec0);

  vec0 = initialize_vector64(0, 1);
  vec1 = initialize_vector64(1, 0);
  vec0 = Lib_IntVector_Intrinsics_vec128_gt64(vec0, vec1);
  exp = initialize_vector64(0x0UL,0xffffffffffffffffUL);
  compare_and_print_vec64("gt64", vec0, exp);
  //  print_vector64("gt64", vec0);

  vec0 = initialize_vector32(0, 1, 2, 3);
  vec0 = Lib_IntVector_Intrinsics_vec128_insert32(vec0, 4, 3);
  exp = initialize_vector32(0x00000000,0x00000001,0x00000002,0x00000004);
  compare_and_print_vec32("insert32", vec0, exp);
  //  print_vector32("insert32", vec0);

  vec0 = initialize_vector64(0, 1);
  vec0 = Lib_IntVector_Intrinsics_vec128_insert64(vec0, 2, 1);
  exp = initialize_vector64(0x0UL,0x2UL);
  compare_and_print_vec64("insert64", vec0, exp);
  //  print_vector64("insert64", vec0);

  vec0 = initialize_vector32(0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f);
  vec1 = initialize_vector32(0x0c0d0e0f, 0x00010203, 0x04050607, 0x08090a0b);
  vec0 = Lib_IntVector_Intrinsics_vec128_interleave_high32(vec0, vec1);
  exp = initialize_vector32(0x08090a0b,0x04050607,0x0c0d0e0f,0x08090a0b);
  compare_and_print_vec32("interlave_high32", vec0, exp);
  //  print_vector32("interleave_high32", vec0);

  vec0 = initialize_vector64(0x0001020304050607, 0x08090a0b0c0d0e0f);
  vec1 = initialize_vector64(0x0c0d0e0f00010203, 0x0405060708090a0b);
  vec0 = Lib_IntVector_Intrinsics_vec128_interleave_high64(vec0, vec1);
  exp = initialize_vector64(0x8090a0b0c0d0e0fUL,0x405060708090a0bUL);
  compare_and_print_vec64("interlave_high64", vec0, exp);
  //  print_vector64("interleave_high64", vec0);

  vec0 = initialize_vector32(0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f);
  vec1 = initialize_vector32(0x0c0d0e0f, 0x00010203, 0x04050607, 0x08090a0b);
  vec0 = Lib_IntVector_Intrinsics_vec128_interleave_low32(vec0, vec1);
  exp = initialize_vector32(0x00010203,0x0c0d0e0f,0x04050607,0x00010203);
  compare_and_print_vec32("interlave_low32", vec0, exp);
  //  print_vector32("interleave_low32", vec0);

  vec0 = initialize_vector64(0x0001020304050607, 0x08090a0b0c0d0e0f);
  vec1 = initialize_vector64(0x0c0d0e0f00010203, 0x0405060708090a0b);
  vec0 = Lib_IntVector_Intrinsics_vec128_interleave_low64(vec0, vec1);
  exp = initialize_vector64(0x1020304050607UL,0xc0d0e0f00010203UL);
  compare_and_print_vec64("interlave_low64", vec0, exp);
  //  print_vector64("interleave_low64", vec0);

  vec0 = Lib_IntVector_Intrinsics_vec128_load32(0x1);
  exp = initialize_vector32(0x00000001,0x00000001,0x00000001,0x00000001);
  compare_and_print_vec32("load32", vec0, exp);
  //  print_vector32("load32", vec0);

  vec0 = Lib_IntVector_Intrinsics_vec128_load32s(0x0, 0x1, 0x2, 0x3);
  exp = initialize_vector32(0x00000000,0x00000001,0x00000002,0x00000003);
  compare_and_print_vec32("load32s", vec0, exp);
  //  print_vector32("load32s", vec0);

  vec0 = Lib_IntVector_Intrinsics_vec128_load64(0x0001020304050607);
  exp = initialize_vector64(0x1020304050607UL,0x1020304050607UL);
  compare_and_print_vec64("load64", vec0, exp);
  //  print_vector64("load64", vec0);

  vec0 = initialize_vector32(0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f);
  vec0 = Lib_IntVector_Intrinsics_vec128_lognot(vec0);
  exp = initialize_vector32(0xfffefdfc,0xfbfaf9f8,0xf7f6f5f4,0xf3f2f1f0);
  compare_and_print_vec32("lognot", vec0, exp);
  //  print_vector32("lognot", vec0);

  vec0 = initialize_vector32(0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f);
  vec1 = initialize_vector32(0x0c0d0e0f, 0x00010203, 0x04050607, 0x08090a0b);
  vec0 = Lib_IntVector_Intrinsics_vec128_or(vec0, vec1);
  exp = initialize_vector32(0x0c0d0e0f,0x04050607,0x0c0d0e0f,0x0c0d0e0f);
  compare_and_print_vec32("or", vec0, exp);
  //  print_vector32("or", vec0);

  vec0 = initialize_vector64(0x0000000100000002UL, 0x0000000300000004UL);
  vec1 = initialize_vector64(0x0000000500000006UL, 0x0000000700000008UL);
  //  print_vector32("mul64", vec0);
  //  print_vector64("mul64", vec0);
  vec0 = Lib_IntVector_Intrinsics_vec128_mul64(vec0, vec1);
  exp = initialize_vector64(0xcUL,0x20UL);
  compare_and_print_vec64("mul64 (#0)", vec0, exp);
  //  print_vector32("mul64", vec0);
  //  print_vector64("mul64", vec0);

  vec0 = initialize_vector64(0x1111222233334444UL, 0x5555666677778888UL);
  vec1 = initialize_vector64(0x9999aaaabbbbccccUL, 0xddddeeeeffff0101UL);
  vec0 = Lib_IntVector_Intrinsics_vec128_mul64(vec0, vec1);
  exp = initialize_vector64(0x258c024630ec9630UL,0x7777118866781088UL);
  compare_and_print_vec64("mul64 (#1)", vec0, exp);
  //  print_vector64("mul64", vec0);

  /** Rotate left 32 ========================================================**/
  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(vec0, 0);
  exp = initialize_vector32(0x00112233,0x44556677,0x8899aabb,0xccddeeff);
  compare_and_print_vec32("rotate_left32 (0)", vec0, exp);
  //  print_vector32("rotate_left32 (0)", vec0);

  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(vec0, 8);
  exp = initialize_vector32(0x11223300,0x55667744,0x99aabb88,0xddeeffcc);
  compare_and_print_vec32("rotate_left32 (8)", vec0, exp);
  //  print_vector32("rotate_left32 (8)", vec0);

  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(vec0, 12);
  exp = initialize_vector32(0x12233001,0x56677445,0x9aabb889,0xdeeffccd);
  compare_and_print_vec32("rotate_left32 (12)", vec0, exp);
  // print_vector32("rotate_left32 (12)", vec0);

  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(vec0, 16);
  exp = initialize_vector32(0x22330011,0x66774455,0xaabb8899,0xeeffccdd);
  compare_and_print_vec32("rotate_left32 (16)", vec0, exp);
  //  print_vector32("rotate_left32 (16)", vec0);

  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(vec0, 24);
  exp = initialize_vector32(0x33001122,0x77445566,0xbb8899aa,0xffccddee);
  compare_and_print_vec32("rotate_left32(24)", vec0, exp);
  //  print_vector32("rotate_left32 (24)", vec0);

  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(vec0, 3);
  exp = initialize_vector32(0x00891198,0x22ab33ba,0x44cd55dc,0x66ef77fe);
  compare_and_print_vec32("rotate_left32 (3)", vec0, exp);
  //  print_vector32("rotate_left32 (3)", vec0);

  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(vec0, 7);
  exp = initialize_vector32(0x08911980,0x2ab33ba2,0x4cd55dc4,0x6ef77fe6);
  compare_and_print_vec32("rotate_left32 (7)", vec0, exp);
  //  print_vector32("rotate_left32 (7)", vec0);

  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_left32(vec0, 21);
  exp = initialize_vector32(0x46600224,0xcee88aac,0x57711335,0xdff99bbd);
  compare_and_print_vec32("rotate_left32 (21)", vec0, exp);
  //  print_vector32("rotate_left32 (21)", vec0);

  /** Rotate right 32 ========================================================**/
  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(vec0, 0);
  exp = initialize_vector32(0x00112233,0x44556677,0x8899aabb,0xccddeeff);
  compare_and_print_vec32("rotate_right32 (0)", vec0, exp);
  //  print_vector32("rotate_right32 (0)", vec0);

  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(vec0, 8);
  exp = initialize_vector32(0x33001122,0x77445566,0xbb8899aa,0xffccddee);
  compare_and_print_vec32("rotate_right32 (8)", vec0, exp);
  //  print_vector32("rotate_right32 (8)", vec0);

  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(vec0, 12);
  exp = initialize_vector32(0x23300112,0x67744556,0xabb8899a,0xeffccdde);
  compare_and_print_vec32("rotate_right32 (12)", vec0, exp);
  //  print_vector32("rotate_right32 (12)", vec0);

  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(vec0, 16);
  exp = initialize_vector32(0x22330011,0x66774455,0xaabb8899,0xeeffccdd);
  compare_and_print_vec32("rotate_right32 (16)", vec0, exp);
  //  print_vector32("rotate_right32 (16)", vec0);

  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(vec0, 24);
  exp = initialize_vector32(0x11223300,0x55667744,0x99aabb88,0xddeeffcc);
  compare_and_print_vec32("rotate_right32(24)", vec0, exp);
  //  print_vector32("rotate_right32 (24)", vec0);

  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(vec0, 3);
  exp = initialize_vector32(0x60022446,0xe88aacce,0x71133557,0xf99bbddf);
  compare_and_print_vec32("rotate_right32 (3)", vec0, exp);
  //  print_vector32("rotate_right32 (3)", vec0);

  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(vec0, 7);
  exp = initialize_vector32(0x66002244,0xee88aacc,0x77113355,0xff99bbdd);
  compare_and_print_vec32("rotate_right32 (7)", vec0, exp);
  //  print_vector32("rotate_right32 (7)", vec0);

  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_right32(vec0, 21);
  exp = initialize_vector32(0x89119800,0xab33ba22,0xcd55dc44,0xef77fe66);
  compare_and_print_vec32("rotate_right32 (21)", vec0, exp);
  //  print_vector32("rotate_right32 (21)", vec0);

  // Rotate right lanes 32
  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(vec0, 0);
  exp = initialize_vector32(0x00112233,0x44556677,0x8899aabb,0xccddeeff);
  compare_and_print_vec32("rotate_right_lanes32 (0)", vec0, exp);
  //  print_vector32("rotate_right_lanes32 (0)", vec0);

  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(vec0, 1);
  exp = initialize_vector32(0x44556677,0x8899aabb,0xccddeeff,0x00112233);
  compare_and_print_vec32("rotate_right_lanes32 (1)", vec0, exp);
  //  print_vector32("rotate_right_lanes32 (1)", vec0);

  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(vec0, 2);
  exp = initialize_vector32(0x8899aabb,0xccddeeff,0x00112233,0x44556677);
  compare_and_print_vec32("rotate_right_lanes32 (2)", vec0, exp);
  //  print_vector32("rotate_right_lanes32 (2)", vec0);

  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec0 = Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(vec0, 3);
  exp = initialize_vector32(0xccddeeff,0x00112233,0x44556677,0x8899aabb);
  compare_and_print_vec32("rotate_right_lanes32(3)", vec0, exp);
  //  print_vector32("rotate_right_lanes32 (3)", vec0);

/*
  // Shift left
  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec0 = Lib_IntVector_Intrinsics_vec128_shift_left64(vec0, 0);
  //  compare_and_print_vec32("shift_left64(0)", vec0, bshift_left64_0);
print_vector32("shift_left64_0", vec0);

  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec0 = Lib_IntVector_Intrinsics_vec128_shift_left64(vec0, 8);
  //  compare_and_print_vec32("shift_left64(8)", vec0, bshift_left64_8);
print_vector32("shift_left64_8", vec0);

  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec0 = Lib_IntVector_Intrinsics_vec128_shift_left64(vec0, 16);
  //  compare_and_print_vec32("shift_left(16)", vec0, bshift_left64_16);
print_vector32("shift_left64_16", vec0);
  
  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec0 = Lib_IntVector_Intrinsics_vec128_shift_left64(vec0, 9);
  //  compare_and_print_vec32("shift_left(9)", vec0, bshift_left64_9);
print_vector32("shift_left64_9", vec0);

  // Shift right
  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec0 = Lib_IntVector_Intrinsics_vec128_shift_right64(vec0, 0);
  //  compare_and_print_vec32("shift_right64(0)", vec0, bshift_right64_0);
print_vector32("shift_right64_0", vec0);

  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec0 = Lib_IntVector_Intrinsics_vec128_shift_right64(vec0, 8);
  //  compare_and_print_vec32("shift_right64(8)", vec0, bshift_right64_8);
print_vector32("shift_right64_8", vec0);

  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec0 = Lib_IntVector_Intrinsics_vec128_shift_right64(vec0, 16);
  //  compare_and_print_vec32("shift_right64(16)", vec0, bshift_right64_16);
print_vector32("shift_right64_16", vec0);

  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec0 = Lib_IntVector_Intrinsics_vec128_shift_right64(vec0, 9);
  //  compare_and_print_vec32("shift_right64(9)", vec0, bshift_right64_9);
print_vector32("shift_right64_9", vec0);

/* 
  // Misc remaining
  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec0 = Lib_IntVector_Intrinsics_vec128_smul64(vec0, 0x0001020304050607);
  //  compare_and_print_vec32("smul64", vec0, bsmul64);
print_vector32("smul64", vec0);

  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec1 = initialize_vector8(15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0);
  vec0 = Lib_IntVector_Intrinsics_vec128_sub64(vec0, vec1);
  //  compare_and_print_vec32("sub64", vec0, bsub64);
print_vector32("sub64", vec0);

  vec0 = initialize_vector32(0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff);
  vec1 = initialize_vector8(15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0);
  vec0 = Lib_IntVector_Intrinsics_vec128_xor(vec0, vec1);
  //  compare_and_print_vec32("xor", vec0, bxor);
print_vector32("xor", vec0);

  vec0 = Lib_IntVector_Intrinsics_vec128_zero;
  //  compare_and_print_vec32("zero", vec0, bvec0);
print_vector32("vec0", vec0);
  */

  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}
