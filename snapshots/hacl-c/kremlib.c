#include "kremlib.h"
#include <stdlib.h>

int exit_success = EXIT_SUCCESS;
int exit_failure = EXIT_FAILURE;

void print_string(const char *s) {
  printf("%s", s);
}

void print_bytes(uint8_t *b, uint32_t len) {
  for (uint32_t i = 0; i < len; i++){
    printf("%02x", b[i]);
  }
  printf("\n");
}

// Constant time comparisons
uint8_t FStar_UInt8_eq_mask(uint8_t x, uint8_t y) {
  x = ~(x ^ y);
  x &= x << 4;
  x &= x << 2;
  x &= x << 1;
  return (int8_t)x >> 7;
}

uint8_t FStar_UInt8_gte_mask(uint8_t x, uint8_t y) {
  return ~(uint8_t)(((int32_t)x - y) >> 31);
}

uint16_t FStar_UInt16_eq_mask(uint16_t x, uint16_t y) {
  x = ~(x ^ y);
  x &= x << 8;
  x &= x << 4;
  x &= x << 2;
  x &= x << 1;
  return (int16_t)x >> 15;
}

uint16_t FStar_UInt16_gte_mask(uint16_t x, uint16_t y) {
  return ~(uint16_t)(((int32_t)x - y) >> 31);
}

uint32_t FStar_UInt32_eq_mask(uint32_t x, uint32_t y) {
  x = ~(x ^ y);
  x &= x << 16;
  x &= x << 8;
  x &= x << 4;
  x &= x << 2;
  x &= x << 1;
  return ((int32_t)x) >> 31;
}

uint32_t FStar_UInt32_gte_mask(uint32_t x, uint32_t y) {
  return ~((uint32_t)(((int64_t)x - y) >> 63));
}

uint64_t FStar_UInt64_eq_mask(uint64_t x, uint64_t y) {
  x = ~(x ^ y);
  x &= x << 32;
  x &= x << 16;
  x &= x << 8;
  x &= x << 4;
  x &= x << 2;
  x &= x << 1;
  return ((int64_t)x) >> 63;
}

uint64_t FStar_UInt64_gte_mask(uint64_t x, uint64_t y) {
  uint64_t low63 =
      ~((uint64_t)((int64_t)((int64_t)(x & UINT64_C(0x7fffffffffffffff)) -
                             (int64_t)(y & UINT64_C(0x7fffffffffffffff))) >>
                   63));
  uint64_t high_bit =
      ~((uint64_t)((int64_t)((int64_t)(x & UINT64_C(0x8000000000000000)) -
                             (int64_t)(y & UINT64_C(0x8000000000000000))) >>
                   63));
  return low63 & high_bit;
}

// 128-bit arithmetic
#if defined(__GNUC__) && defined(__SIZEOF_INT128__)
#include "native128.c"
#else
#include "custom128.c"
#endif

void FStar_Buffer_recall(void *x) {}

bool Prims_op_GreaterThanOrEqual(Prims_int x, Prims_int y) { KRML_EXIT; }
bool Prims_op_LessThanOrEqual(Prims_int x, Prims_int y) { KRML_EXIT; }
bool Prims_op_GreaterThan(Prims_int x, Prims_int y) { KRML_EXIT; }
bool Prims_op_LessThan(Prims_int x, Prims_int y) { KRML_EXIT; }
Prims_int Prims_pow2(Prims_int x) { KRML_EXIT; }
Prims_int Prims_op_Multiply(Prims_int x, Prims_int y) { KRML_EXIT; }
Prims_int Prims_op_Addition(Prims_int x, Prims_int y) { KRML_EXIT; }
Prims_int Prims_op_Subtraction(Prims_int x, Prims_int y) { KRML_EXIT; }
Prims_int Prims_op_Division(Prims_int x, Prims_int y) { KRML_EXIT; }
Prims_int Prims_op_Modulus(Prims_int x, Prims_int y) { KRML_EXIT; }
void *Prims_magic(void *_) { KRML_EXIT; }
void *Prims_admit(void *_) { KRML_EXIT; }
void *Prims____Cons___tl(void *_) { KRML_EXIT; }

bool FStar_HyperStack_is_eternal_color(Prims_int x0) { KRML_EXIT; }

Prims_int FStar_UInt32_v(uint32_t x) { return (void *)0; }
FStar_Seq_Base_seq FStar_Seq_Base_append(FStar_Seq_Base_seq x, FStar_Seq_Base_seq y) { KRML_EXIT; }
FStar_Seq_Base_seq FStar_Seq_Base_slice(FStar_Seq_Base_seq x, FStar_Seq_Base_seq y, Prims_nat z) {
  KRML_EXIT;
}
FStar_UInt32_t FStar_UInt32_uint_to_t(Prims_nat x) { KRML_EXIT; }
