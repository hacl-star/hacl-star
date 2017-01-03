#include "kremlib.h"
#include "testlib.h"

#undef force_inline
#define force_inline __attribute__((always_inline))


Prims_int Hacl_Bignum_Constants_prime;

Prims_int Hacl_Bignum_Constants_word_size;

Prims_int Hacl_Bignum_Constants_len;

Prims_int Hacl_Bignum_Constants_limb_size;

Prims_int Hacl_Bignum_Constants_keylen;

uint64_t Hacl_Bignum_Constants_a24 = (uint64_t )121665;

Prims_int Hacl_Bignum_Parameters_prime;

Prims_int Hacl_Bignum_Parameters_word_size;

Prims_int Hacl_Bignum_Parameters_len;

uint32_t Hacl_Bignum_Parameters_clen = (uint32_t )5;

uint32_t Hacl_Bignum_Parameters_climb_size = (uint32_t )51;

static inline force_inline void Hacl_Bignum_Parameters_lemma_prime_limb_size()
{
  return;
}

Prims_int Hacl_Bignum_Parameters_limb_n;

Prims_int Hacl_Bignum_Parameters_v(uint64_t x)
{
  return (Prims_int )(uint8_t )0;
}

static inline force_inline void Hacl_Bignum_Parameters_lemma_limb_injectivity(uint64_t a, uint64_t b)
{
  return;
}

uint64_t Hacl_Bignum_Parameters_limb_zero = (uint64_t )0;

uint64_t Hacl_Bignum_Parameters_limb_one = (uint64_t )1;

uint64_t Hacl_Bignum_Parameters_limb_add(uint64_t a, uint64_t b)
{
  return a + b;
}

uint64_t Hacl_Bignum_Parameters_limb_add_mod(uint64_t a, uint64_t b)
{
  return a + b;
}

uint64_t Hacl_Bignum_Parameters_limb_sub(uint64_t a, uint64_t b)
{
  return a - b;
}

uint64_t Hacl_Bignum_Parameters_limb_sub_mod(uint64_t a, uint64_t b)
{
  return a - b;
}

uint64_t Hacl_Bignum_Parameters_limb_mul(uint64_t a, uint64_t b)
{
  return a * b;
}

uint64_t Hacl_Bignum_Parameters_limb_mul_mod(uint64_t a, uint64_t b)
{
  return a * b;
}

uint64_t Hacl_Bignum_Parameters_limb_logand(uint64_t a, uint64_t b)
{
  return a & b;
}

uint64_t Hacl_Bignum_Parameters_limb_logxor(uint64_t a, uint64_t b)
{
  return a ^ b;
}

uint64_t Hacl_Bignum_Parameters_limb_logor(uint64_t a, uint64_t b)
{
  return a | b;
}

uint64_t Hacl_Bignum_Parameters_limb_lognot(uint64_t a)
{
  return ~a;
}

uint64_t Hacl_Bignum_Parameters_limb_shift_right(uint64_t a, uint32_t s)
{
  return a >> s;
}

uint64_t Hacl_Bignum_Parameters_limb_shift_left(uint64_t a, uint32_t s)
{
  return a << s;
}

uint64_t Hacl_Bignum_Parameters_limb_eq_mask(uint64_t a, uint64_t b)
{
  return FStar_UInt64_eq_mask(a, b);
}

uint64_t Hacl_Bignum_Parameters_limb_gte_mask(uint64_t a, uint64_t b)
{
  return FStar_UInt64_gte_mask(a, b);
}

uint64_t Hacl_Bignum_Parameters_limb_gt_mask(uint64_t a, uint64_t b)
{
  return ~FStar_UInt64_gte_mask(b, a);
}

uint64_t Hacl_Bignum_Parameters_limb_lt_mask(uint64_t a, uint64_t b)
{
  return ~FStar_UInt64_gte_mask(a, b);
}

uint64_t Hacl_Bignum_Parameters_limb_lte_mask(uint64_t a, uint64_t b)
{
  return ~~FStar_UInt64_gte_mask(b, a);
}

uint8_t Hacl_Bignum_Parameters_limb_to_byte(uint64_t x)
{
  return (uint8_t )x;
}

uint64_t Hacl_Bignum_Parameters_byte_to_limb(uint8_t x)
{
  return (uint64_t )x;
}

Prims_int Hacl_Bignum_Parameters_wide_n;

Prims_int Hacl_Bignum_Parameters_w(FStar_UInt128_t x)
{
  return (Prims_int )(uint8_t )0;
}

static inline force_inline void Hacl_Bignum_Parameters_lemma_wide_injectivity(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return;
}

FStar_UInt128_t
Hacl_Bignum_Parameters_wide_zero = FStar_Int_Cast_uint64_to_uint128((uint64_t )0);

FStar_UInt128_t
Hacl_Bignum_Parameters_wide_one = FStar_Int_Cast_uint64_to_uint128((uint64_t )1);

FStar_UInt128_t Hacl_Bignum_Parameters_wide_add(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_add(a, b);
}

FStar_UInt128_t Hacl_Bignum_Parameters_wide_add_mod(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_add_mod(a, b);
}

FStar_UInt128_t Hacl_Bignum_Parameters_wide_sub(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_sub(a, b);
}

FStar_UInt128_t Hacl_Bignum_Parameters_wide_sub_mod(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_sub_mod(a, b);
}

FStar_UInt128_t Hacl_Bignum_Parameters_wide_logand(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_logand(a, b);
}

FStar_UInt128_t Hacl_Bignum_Parameters_wide_logxor(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_logxor(a, b);
}

FStar_UInt128_t Hacl_Bignum_Parameters_wide_logor(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_logor(a, b);
}

FStar_UInt128_t Hacl_Bignum_Parameters_wide_lognot(FStar_UInt128_t a)
{
  return FStar_UInt128_lognot(a);
}

FStar_UInt128_t Hacl_Bignum_Parameters_wide_shift_right(FStar_UInt128_t a, uint32_t s)
{
  return FStar_UInt128_shift_right(a, s);
}

FStar_UInt128_t Hacl_Bignum_Parameters_wide_shift_left(FStar_UInt128_t a, uint32_t s)
{
  return FStar_UInt128_shift_left(a, s);
}

FStar_UInt128_t Hacl_Bignum_Parameters_wide_eq_mask(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_eq_mask(a, b);
}

FStar_UInt128_t Hacl_Bignum_Parameters_wide_gte_mask(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_gte_mask(a, b);
}

FStar_UInt128_t Hacl_Bignum_Parameters_wide_gt_mask(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_lognot(FStar_UInt128_gte_mask(b, a));
}

FStar_UInt128_t Hacl_Bignum_Parameters_wide_lt_mask(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_lognot(FStar_UInt128_gte_mask(a, b));
}

FStar_UInt128_t Hacl_Bignum_Parameters_wide_lte_mask(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_lognot(FStar_UInt128_lognot(FStar_UInt128_gte_mask(b, a)));
}

FStar_UInt128_t Hacl_Bignum_Parameters_mul_wide(uint64_t x, uint64_t y)
{
  return FStar_UInt128_mul_wide(x, y);
}

FStar_UInt128_t Hacl_Bignum_Parameters_limb_to_wide(uint64_t x)
{
  return FStar_Int_Cast_uint64_to_uint128(x);
}

uint64_t Hacl_Bignum_Parameters_wide_to_limb(FStar_UInt128_t x)
{
  return FStar_Int_Cast_uint128_to_uint64(x);
}

uint64_t Hacl_Bignum_Parameters_uint64_to_limb(uint64_t x)
{
  return x;
}

Prims_int Hacl_Bignum_Limb_n;

Prims_int Hacl_Bignum_Limb_v(uint64_t x)
{
  return (Prims_int )(uint8_t )0;
}

uint64_t Hacl_Bignum_Limb_add(uint64_t a, uint64_t b)
{
  return a + b;
}

uint64_t Hacl_Bignum_Limb_add_mod(uint64_t a, uint64_t b)
{
  return a + b;
}

uint64_t Hacl_Bignum_Limb_sub(uint64_t a, uint64_t b)
{
  return a - b;
}

uint64_t Hacl_Bignum_Limb_sub_mod(uint64_t a, uint64_t b)
{
  return a - b;
}

uint64_t Hacl_Bignum_Limb_mul(uint64_t a, uint64_t b)
{
  return a * b;
}

uint64_t Hacl_Bignum_Limb_mul_mod(uint64_t a, uint64_t b)
{
  return a * b;
}

uint64_t Hacl_Bignum_Limb_logand(uint64_t a, uint64_t b)
{
  return a & b;
}

uint64_t Hacl_Bignum_Limb_logxor(uint64_t a, uint64_t b)
{
  return a ^ b;
}

uint64_t Hacl_Bignum_Limb_logor(uint64_t a, uint64_t b)
{
  return a | b;
}

uint64_t Hacl_Bignum_Limb_lognot(uint64_t a)
{
  return ~a;
}

uint64_t Hacl_Bignum_Limb_shift_right(uint64_t a, uint32_t s)
{
  return a >> s;
}

uint64_t Hacl_Bignum_Limb_shift_left(uint64_t a, uint32_t s)
{
  return a << s;
}

uint64_t Hacl_Bignum_Limb_eq_mask(uint64_t a, uint64_t b)
{
  return FStar_UInt64_eq_mask(a, b);
}

uint64_t Hacl_Bignum_Limb_gte_mask(uint64_t a, uint64_t b)
{
  return FStar_UInt64_gte_mask(a, b);
}

uint64_t Hacl_Bignum_Limb_gt_mask(uint64_t a, uint64_t b)
{
  return ~FStar_UInt64_gte_mask(b, a);
}

uint64_t Hacl_Bignum_Limb_lt_mask(uint64_t a, uint64_t b)
{
  return ~FStar_UInt64_gte_mask(a, b);
}

uint64_t Hacl_Bignum_Limb_lte_mask(uint64_t a, uint64_t b)
{
  return ~~FStar_UInt64_gte_mask(b, a);
}

uint64_t Hacl_Bignum_Limb_op_Plus_Hat(uint64_t a, uint64_t b)
{
  return a + b;
}

uint64_t Hacl_Bignum_Limb_op_Plus_Percent_Hat(uint64_t a, uint64_t b)
{
  return a + b;
}

uint64_t Hacl_Bignum_Limb_op_Subtraction_Hat(uint64_t a, uint64_t b)
{
  return a - b;
}

uint64_t Hacl_Bignum_Limb_op_Subtraction_Percent_Hat(uint64_t a, uint64_t b)
{
  return a - b;
}

uint64_t Hacl_Bignum_Limb_op_Star_Hat(uint64_t a, uint64_t b)
{
  return a * b;
}

uint64_t Hacl_Bignum_Limb_op_Star_Percent_Hat(uint64_t a, uint64_t b)
{
  return a * b;
}

uint64_t Hacl_Bignum_Limb_op_Amp_Hat(uint64_t a, uint64_t b)
{
  return a & b;
}

uint64_t Hacl_Bignum_Limb_op_Hat_Hat(uint64_t a, uint64_t b)
{
  return a ^ b;
}

uint64_t Hacl_Bignum_Limb_op_Bar_Hat(uint64_t a, uint64_t b)
{
  return a | b;
}

uint64_t Hacl_Bignum_Limb_op_Greater_Greater_Hat(uint64_t a, uint32_t s)
{
  return a >> s;
}

uint64_t Hacl_Bignum_Limb_op_Less_Less_Hat(uint64_t a, uint32_t s)
{
  return a << s;
}


Prims_int Hacl_Bignum_Wide_n;

Prims_int Hacl_Bignum_Wide_v(FStar_UInt128_t x)
{
  return (Prims_int )(uint8_t )0;
}

FStar_UInt128_t Hacl_Bignum_Wide_add(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_add(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_add_mod(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_add_mod(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_sub(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_sub(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_sub_mod(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_sub_mod(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_logand(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_logand(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_logxor(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_logxor(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_logor(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_logor(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_lognot(FStar_UInt128_t a)
{
  return FStar_UInt128_lognot(a);
}

FStar_UInt128_t Hacl_Bignum_Wide_shift_right(FStar_UInt128_t a, uint32_t s)
{
  return FStar_UInt128_shift_right(a, s);
}

FStar_UInt128_t Hacl_Bignum_Wide_shift_left(FStar_UInt128_t a, uint32_t s)
{
  return FStar_UInt128_shift_left(a, s);
}

FStar_UInt128_t Hacl_Bignum_Wide_eq_mask(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_eq_mask(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_gte_mask(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_gte_mask(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_gt_mask(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_lognot(FStar_UInt128_gte_mask(b, a));
}

FStar_UInt128_t Hacl_Bignum_Wide_lt_mask(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_lognot(FStar_UInt128_gte_mask(a, b));
}

FStar_UInt128_t Hacl_Bignum_Wide_lte_mask(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_lognot(FStar_UInt128_lognot(FStar_UInt128_gte_mask(b, a)));
}

FStar_UInt128_t Hacl_Bignum_Wide_op_Plus_Hat(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_add(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_op_Plus_Percent_Hat(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_add_mod(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_op_Subtraction_Hat(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_sub(a, b);
}

FStar_UInt128_t
Hacl_Bignum_Wide_op_Subtraction_Percent_Hat(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_sub_mod(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_op_Amp_Hat(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_logand(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_op_Hat_Hat(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_logxor(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_op_Bar_Hat(FStar_UInt128_t a, FStar_UInt128_t b)
{
  return FStar_UInt128_logor(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_op_Greater_Greater_Hat(FStar_UInt128_t a, uint32_t s)
{
  return FStar_UInt128_shift_right(a, s);
}

FStar_UInt128_t Hacl_Bignum_Wide_op_Less_Less_Hat(FStar_UInt128_t a, uint32_t s)
{
  return FStar_UInt128_shift_left(a, s);
}

FStar_UInt128_t Hacl_Bignum_Wide_mul_wide(uint64_t a, uint64_t b)
{
  return FStar_UInt128_mul_wide(a, b);
}

FStar_UInt128_t Hacl_Bignum_Wide_op_Star_Hat(uint64_t a, uint64_t b)
{
  return FStar_UInt128_mul_wide(a, b);
}


Prims_nat Hacl_Bignum_Bigint_bitweight(Prims_nat n)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

Prims_nat Hacl_Bignum_Bigint_eval_(FStar_HyperStack_mem h, uint64_t *b, Prims_nat i)
{
  return (Prims_nat )(uint8_t )0;
}

Prims_nat Hacl_Bignum_Bigint_eval(FStar_HyperStack_mem h, uint64_t *b)
{
  return (Prims_nat )(uint8_t )0;
}

Prims_nat
Hacl_Bignum_Bigint_eval_wide_(FStar_HyperStack_mem h, FStar_UInt128_t *b, Prims_nat i)
{
  return (Prims_nat )(uint8_t )0;
}

Prims_nat Hacl_Bignum_Bigint_eval_wide(FStar_HyperStack_mem h, FStar_UInt128_t *b)
{
  return (Prims_nat )(uint8_t )0;
}


static inline force_inline void Hacl_Bignum_Fsum_fsum_(uint64_t *a, uint64_t *b, uint32_t i)
{
  if (i == (uint32_t )0)
    return;
  else
  {
    uint32_t i0 = i - (uint32_t )1;
    uint64_t ai = a[i0];
    uint64_t bi = b[i0];
    a[i0] = ai + bi;
    Hacl_Bignum_Fsum_fsum_(a, b, i0);
    return;
  }
}



static inline force_inline void Hacl_Bignum_Fdifference_fdifference_(uint64_t *a, uint64_t *b, uint32_t i)
{
  if (i == (uint32_t )0)
    return;
  else
  {
    uint32_t i0 = i - (uint32_t )1;
    uint64_t ai = a[i0];
    uint64_t bi = b[i0];
    a[i0] = bi - ai;
    Hacl_Bignum_Fdifference_fdifference_(a, b, i0);
    return;
  }
}



uint64_t Hacl_Bignum_Modulo_two54m152 = (uint64_t )0x3fffffffffff68;

uint64_t Hacl_Bignum_Modulo_two54m8 = (uint64_t )0x3ffffffffffff8;

uint64_t Hacl_Bignum_Modulo_nineteen = (uint64_t )19;

uint64_t Hacl_Bignum_Modulo_mask_51 = (uint64_t )0x7ffffffffffff;

static inline force_inline void *Hacl_Bignum_Modulo_add_zero_spec(void *s)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

static inline force_inline void Hacl_Bignum_Modulo_add_zero(uint64_t *b)
{
  uint64_t b0 = b[(uint32_t )0];
  uint64_t b1 = b[(uint32_t )1];
  uint64_t b2 = b[(uint32_t )2];
  uint64_t b3 = b[(uint32_t )3];
  uint64_t b4 = b[(uint32_t )4];
  b[(uint32_t )0] = b0 + (uint64_t )0x3fffffffffff68;
  b[(uint32_t )1] = b1 + (uint64_t )0x3ffffffffffff8;
  b[(uint32_t )2] = b2 + (uint64_t )0x3ffffffffffff8;
  b[(uint32_t )3] = b3 + (uint64_t )0x3ffffffffffff8;
  b[(uint32_t )4] = b4 + (uint64_t )0x3ffffffffffff8;
}

static inline force_inline void *Hacl_Bignum_Modulo_carry_top_spec(void *s)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

static inline force_inline void Hacl_Bignum_Modulo_carry_top(uint64_t *b)
{
  uint64_t b4 = b[(uint32_t )4];
  uint64_t b0 = b[(uint32_t )0];
  uint64_t mask = ((uint64_t )1 << (uint32_t )51) - (uint64_t )1;
  uint64_t
  nineteen = ((uint64_t )1 << (uint32_t )4) + ((uint64_t )1 << (uint32_t )1) + (uint64_t )1;
  uint64_t b4_ = b4 & mask;
  uint64_t b0_ = b0 + nineteen * (b4 >> (uint32_t )51);
  b[(uint32_t )4] = b4_;
  b[(uint32_t )0] = b0_;
}

static inline force_inline void *Hacl_Bignum_Modulo_reduce_spec(void *s)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

static inline force_inline void Hacl_Bignum_Modulo_reduce(uint64_t *b)
{
  uint64_t
  nineteen = ((uint64_t )1 << (uint32_t )4) + ((uint64_t )1 << (uint32_t )1) + (uint64_t )1;
  uint64_t b0 = b[(uint32_t )0];
  b[(uint32_t )0] = nineteen * b0;
}

static inline force_inline void *Hacl_Bignum_Modulo_carry_top_wide_spec(void *s)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

static inline force_inline void Hacl_Bignum_Modulo_carry_top_wide(FStar_UInt128_t *b)
{
  FStar_UInt128_t b4 = b[(uint32_t )4];
  FStar_UInt128_t b0 = b[(uint32_t )0];
  uint64_t
  nineteen = ((uint64_t )1 << (uint32_t )4) + ((uint64_t )1 << (uint32_t )1) + (uint64_t )1;
  FStar_UInt128_t
  mask =
    FStar_UInt128_sub(FStar_UInt128_shift_left(FStar_Int_Cast_uint64_to_uint128((uint64_t )1),
        (uint32_t )51),
      FStar_Int_Cast_uint64_to_uint128((uint64_t )1));
  FStar_UInt128_t b4_ = FStar_UInt128_logand(b4, mask);
  FStar_UInt128_t
  b0_ =
    FStar_UInt128_add(b0,
      FStar_UInt128_mul_wide(nineteen,
        FStar_Int_Cast_uint128_to_uint64(FStar_UInt128_shift_right(b4, (uint32_t )51))));
  b[(uint32_t )4] = b4_;
  b[(uint32_t )0] = b0_;
}



static inline force_inline void
Hacl_Bignum_Fproduct_copy_from_wide_(uint64_t *output, FStar_UInt128_t *input, uint32_t ctr)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    uint32_t i = ctr - (uint32_t )1;
    FStar_UInt128_t inputi = input[i];
    output[i] = FStar_Int_Cast_uint128_to_uint64(inputi);
    Hacl_Bignum_Fproduct_copy_from_wide_(output, input, i);
    return;
  }
}

static inline force_inline void Hacl_Bignum_Fproduct_shift_(uint64_t *output, uint32_t ctr)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    uint64_t z = output[ctr - (uint32_t )1];
    output[ctr] = z;
    Hacl_Bignum_Fproduct_shift_(output, ctr - (uint32_t )1);
    return;
  }
}

static inline force_inline void Hacl_Bignum_Fproduct_shift(uint64_t *output)
{
  uint64_t tmp = output[(uint32_t )4];
  Hacl_Bignum_Fproduct_shift_(output, (uint32_t )4);
  output[(uint32_t )0] = tmp;
}

static inline force_inline void
Hacl_Bignum_Fproduct_sum_scalar_multiplication_(
  FStar_UInt128_t *output,
  uint64_t *input,
  uint64_t s,
  uint32_t ctr
)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    uint32_t i = ctr - (uint32_t )1;
    FStar_UInt128_t oi = output[i];
    uint64_t ii = input[i];
    output[i] = FStar_UInt128_add(oi, FStar_UInt128_mul_wide(ii, s));
    Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, s, i);
    return;
  }
}

static inline force_inline void Hacl_Bignum_Fproduct_shift_reduce(uint64_t *output)
{
  Hacl_Bignum_Fproduct_shift(output);
  Hacl_Bignum_Modulo_reduce(output);
  return;
}

static inline force_inline void
Hacl_Bignum_Fproduct_mul_shift_reduce_(
  FStar_UInt128_t *output,
  uint64_t *input,
  uint64_t *input2,
  uint32_t ctr
)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    uint32_t i = ctr - (uint32_t )1;
    uint32_t j = (uint32_t )4 - i;
    uint64_t input2i = input2[j];
    Hacl_Bignum_Fproduct_sum_scalar_multiplication_(output, input, input2i, (uint32_t )5);
    if (ctr > (uint32_t )1)
      Hacl_Bignum_Fproduct_shift_reduce(input);
    Hacl_Bignum_Fproduct_mul_shift_reduce_(output, input, input2, i);
    return;
  }
}

static inline force_inline void Hacl_Bignum_Fproduct_carry_wide_(FStar_UInt128_t *tmp, uint32_t ctr)
{
  if (ctr == (uint32_t )4)
    return;
  else
  {
    FStar_UInt128_t tctr = tmp[ctr];
    FStar_UInt128_t tctrp1 = tmp[ctr + (uint32_t )1];
    uint64_t
    r0 = FStar_Int_Cast_uint128_to_uint64(tctr) & ((uint64_t )1 << (uint32_t )51) - (uint64_t )1;
    FStar_UInt128_t c = FStar_UInt128_shift_right(tctr, (uint32_t )51);
    tmp[ctr] = FStar_Int_Cast_uint64_to_uint128(r0);
    tmp[ctr + (uint32_t )1] = FStar_UInt128_add(tctrp1, c);
    Hacl_Bignum_Fproduct_carry_wide_(tmp, ctr + (uint32_t )1);
    return;
  }
}

static inline force_inline void Hacl_Bignum_Fproduct_carry_0_to_1(uint64_t *output)
{
  uint64_t i0 = output[(uint32_t )0];
  uint64_t i1 = output[(uint32_t )1];
  uint64_t i0_ = i0 & ((uint64_t )1 << (uint32_t )51) - (uint64_t )1;
  uint64_t i1_ = i1 + (i0 >> (uint32_t )51);
  output[(uint32_t )0] = i0_;
  output[(uint32_t )1] = i1_;
}

static inline force_inline void Hacl_Bignum_Fproduct_fmul_(uint64_t *output, uint64_t *input, uint64_t *input2)
{
  FStar_UInt128_t t[5];
  for (uintmax_t i = 0; i < (uint32_t )5; ++i)
    t[i] = FStar_Int_Cast_uint64_to_uint128((uint64_t )0);
  Hacl_Bignum_Fproduct_mul_shift_reduce_(t, input, input2, (uint32_t )5);
  Hacl_Bignum_Fproduct_carry_wide_(t, (uint32_t )0);
  Hacl_Bignum_Modulo_carry_top_wide(t);
  Hacl_Bignum_Fproduct_copy_from_wide_(output, t, (uint32_t )5);
  Hacl_Bignum_Fproduct_carry_0_to_1(output);
}

static inline force_inline void Hacl_Bignum_Fproduct_fmul(uint64_t *output, uint64_t *input, uint64_t *input2)
{
  uint64_t tmp[5] = { 0 };
  memcpy(tmp, input, (uint32_t )5 * sizeof input[0]);
  Hacl_Bignum_Fproduct_fmul_(output, tmp, input2);
}

static inline force_inline void Hacl_Bignum_Fproduct_fsquare_times_(uint64_t *tmp, uint32_t count)
{
  if (count == (uint32_t )0)
    return;
  else
  {
    Hacl_Bignum_Fproduct_fmul(tmp, tmp, tmp);
    Hacl_Bignum_Fproduct_fsquare_times_(tmp, count - (uint32_t )1);
    return;
  }
}

static inline force_inline void Hacl_Bignum_Fproduct_fsquare_times_rec(uint64_t *output, uint64_t *input, uint32_t count)
{
  uint64_t tmp[5] = { 0 };
  memcpy(tmp, input, (uint32_t )5 * sizeof input[0]);
  Hacl_Bignum_Fproduct_fsquare_times_(tmp, count);
  memcpy(output, tmp, (uint32_t )5 * sizeof tmp[0]);
}

static inline void force_inline
Hacl_Bignum_Fproduct_fsquare_times(uint64_t* output, uint64_t* in, uint64_t count) {
  FStar_UInt128_t t[5];
  uint64_t r0,r1,r2,r3,r4,c;
  uint64_t d0,d1,d2,d4,d419;

  r0 = in[0];
  r1 = in[1];
  r2 = in[2];
  r3 = in[3];
  r4 = in[4];

  do {
    d0 = r0 * 2;
    d1 = r1 * 2;
    d2 = r2 * 2 * 19;
    d419 = r4 * 19;
    d4 = d419 * 2;

    t[0] = ((FStar_UInt128_t) r0) * r0 + ((FStar_UInt128_t) d4) * r1 + (((FStar_UInt128_t) d2) * (r3     ));
    t[1] = ((FStar_UInt128_t) d0) * r1 + ((FStar_UInt128_t) d4) * r2 + (((FStar_UInt128_t) r3) * (r3 * 19));
    t[2] = ((FStar_UInt128_t) d0) * r2 + ((FStar_UInt128_t) r1) * r1 + (((FStar_UInt128_t) d4) * (r3     ));
    t[3] = ((FStar_UInt128_t) d0) * r3 + ((FStar_UInt128_t) d1) * r2 + (((FStar_UInt128_t) r4) * (d419   ));
    t[4] = ((FStar_UInt128_t) d0) * r4 + ((FStar_UInt128_t) d1) * r3 + (((FStar_UInt128_t) r2) * (r2     ));

                    r0 = (uint64_t)t[0] & 0x7ffffffffffff; c = (uint64_t)(t[0] >> 51);
    t[1] += c;      r1 = (uint64_t)t[1] & 0x7ffffffffffff; c = (uint64_t)(t[1] >> 51);
    t[2] += c;      r2 = (uint64_t)t[2] & 0x7ffffffffffff; c = (uint64_t)(t[2] >> 51);
    t[3] += c;      r3 = (uint64_t)t[3] & 0x7ffffffffffff; c = (uint64_t)(t[3] >> 51);
    t[4] += c;      r4 = (uint64_t)t[4] & 0x7ffffffffffff; c = (uint64_t)(t[4] >> 51);
    r0 +=   c * 19; c = r0 >> 51; r0 = r0 & 0x7ffffffffffff;
    r1 +=   c;      c = r1 >> 51; r1 = r1 & 0x7ffffffffffff;
    r2 +=   c;
  } while(--count);

  output[0] = r0;
  output[1] = r1;
  output[2] = r2;
  output[3] = r3;
  output[4] = r4;
}



static inline force_inline void Hacl_Bignum_Fscalar_fscalar_(FStar_UInt128_t *output, uint64_t *b, uint64_t s, uint32_t i)
{
  if (i == (uint32_t )0)
    return;
  else
  {
    uint32_t i0 = i - (uint32_t )1;
    uint64_t bi = b[i0];
    output[i0] = FStar_UInt128_mul_wide(bi, s);
    Hacl_Bignum_Fscalar_fscalar_(output, b, s, i0);
    return;
  }
}

static inline force_inline void Hacl_Bignum_Fscalar_fscalar(FStar_UInt128_t *output, uint64_t *b, uint64_t s)
{
  Hacl_Bignum_Fscalar_fscalar_(output, b, s, (uint32_t )5);
  return;
}

static inline force_inline void Hacl_Bignum_Crecip_crecip(uint64_t *out, uint64_t *z)
{
  uint64_t buf[20] = { 0 };
  uint64_t *a = buf + (uint32_t )0;
  uint64_t *t0 = buf + (uint32_t )5;
  uint64_t *b = buf + (uint32_t )10;
  uint64_t *c = buf + (uint32_t )15;
  Hacl_Bignum_Fproduct_fsquare_times(a, z, (uint32_t )1);
  Hacl_Bignum_Fproduct_fsquare_times(t0, a, (uint32_t )2);
  Hacl_Bignum_Fproduct_fmul(b, t0, z);
  Hacl_Bignum_Fproduct_fmul(a, b, a);
  Hacl_Bignum_Fproduct_fsquare_times(t0, a, (uint32_t )1);
  Hacl_Bignum_Fproduct_fmul(b, t0, b);
  Hacl_Bignum_Fproduct_fsquare_times(t0, b, (uint32_t )5);
  Hacl_Bignum_Fproduct_fmul(b, t0, b);
  Hacl_Bignum_Fproduct_fsquare_times(t0, b, (uint32_t )10);
  Hacl_Bignum_Fproduct_fmul(c, t0, b);
  Hacl_Bignum_Fproduct_fsquare_times(t0, c, (uint32_t )20);
  Hacl_Bignum_Fproduct_fmul(t0, t0, c);
  Hacl_Bignum_Fproduct_fsquare_times(t0, t0, (uint32_t )10);
  Hacl_Bignum_Fproduct_fmul(b, t0, b);
  Hacl_Bignum_Fproduct_fsquare_times(t0, b, (uint32_t )50);
  Hacl_Bignum_Fproduct_fmul(c, t0, b);
  Hacl_Bignum_Fproduct_fsquare_times(t0, c, (uint32_t )100);
  Hacl_Bignum_Fproduct_fmul(t0, t0, c);
  Hacl_Bignum_Fproduct_fsquare_times(t0, t0, (uint32_t )50);
  Hacl_Bignum_Fproduct_fmul(t0, t0, b);
  Hacl_Bignum_Fproduct_fsquare_times(t0, t0, (uint32_t )5);
  Hacl_Bignum_Fproduct_fmul(out, t0, a);
}


static inline force_inline void Hacl_Bignum_fsum(uint64_t *a, uint64_t *b)
{
  a[0] += b[0];
  a[1] += b[1];
  a[2] += b[2];
  a[3] += b[3];
  a[4] += b[4];
  return;
}

static inline force_inline void Hacl_Bignum_fdifference_rec(uint64_t *a, uint64_t *b)
{
  uint64_t tmp[5] = { 0 };
  memcpy(tmp, b, (uint32_t )5 * sizeof b[0]);
  Hacl_Bignum_Modulo_add_zero(tmp);
  Hacl_Bignum_Fdifference_fdifference_(a, tmp, (uint32_t )5);
}

static inline void force_inline
Hacl_Bignum_fdifference(uint64_t* out, const uint64_t* in) {
  /* 152 is 19 << 3 */
  static const uint64_t two54m152 = (((uint64_t)1) << 54) - 152;
  static const uint64_t two54m8 = (((uint64_t)1) << 54) - 8;

  out[0] = in[0] + two54m152 - out[0];
  out[1] = in[1] + two54m8 - out[1];
  out[2] = in[2] + two54m8 - out[2];
  out[3] = in[3] + two54m8 - out[3];
  out[4] = in[4] + two54m8 - out[4];
}


static inline force_inline void Hacl_Bignum_fscalar(uint64_t *output, uint64_t *b, uint64_t s)
{
  FStar_UInt128_t tmp[5];
  for (uintmax_t i = 0; i < (uint32_t )5; ++i)
    tmp[i] = FStar_Int_Cast_uint64_to_uint128((uint64_t )0);
  Hacl_Bignum_Fscalar_fscalar(tmp, b, s);
  Hacl_Bignum_Fproduct_carry_wide_(tmp, (uint32_t )0);
  Hacl_Bignum_Modulo_carry_top_wide(tmp);
  Hacl_Bignum_Fproduct_copy_from_wide_(output, tmp, (uint32_t )5);
}

static inline force_inline void Hacl_Bignum_fmul(uint64_t *output, uint64_t *a, uint64_t *b)
{
  Hacl_Bignum_Fproduct_fmul(output, a, b);
  return;
}

static inline force_inline void Hacl_Bignum_fsquare_times(uint64_t *output, uint64_t *input, uint32_t count)
{
  Hacl_Bignum_Fproduct_fsquare_times(output, input, count);
  return;
}

static inline force_inline void Hacl_Bignum_crecip(uint64_t *output, uint64_t *input)
{
  Hacl_Bignum_Crecip_crecip(output, input);
  return;
}


uint64_t *Hacl_EC_Point_getx(uint64_t *p)
{
  return p + (uint32_t )0;
}

uint64_t *Hacl_EC_Point_gety(uint64_t *p)
{
  return p + (uint32_t )0;
}

uint64_t *Hacl_EC_Point_getz(uint64_t *p)
{
  return p + (uint32_t )5;
}

uint64_t *Hacl_EC_Point_make(uint64_t *x, uint64_t *y, uint64_t *z)
{
  return x;
}

bool Hacl_EC_Point_valid(FStar_HyperStack_mem h, uint64_t *p)
{
  return (bool )(uint8_t )0;
}

void Hacl_EC_Point_swap_conditional_(uint64_t *a, uint64_t *b, uint64_t swap, uint32_t ctr)
{
  if (ctr == (uint32_t )0)
    return;
  else
  {
    uint32_t i = ctr - (uint32_t )1;
    uint64_t ai0 = a[i];
    uint64_t bi0 = b[i];
    uint64_t x = swap & (ai0 ^ bi0);
    uint64_t ai = ai0 ^ x;
    uint64_t bi = bi0 ^ x;
    a[i] = ai;
    b[i] = bi;
    Hacl_EC_Point_swap_conditional_(a, b, swap, i);
    return;
  }
}

void Hacl_EC_Point_swap_conditional(uint64_t *a, uint64_t *b, uint64_t iswap)
{
  uint64_t swap = (uint64_t )0 - iswap;
  Hacl_EC_Point_swap_conditional_(Hacl_EC_Point_getx(a),
    Hacl_EC_Point_getx(b),
    swap,
    (uint32_t )5);
  Hacl_EC_Point_swap_conditional_(Hacl_EC_Point_getz(a),
    Hacl_EC_Point_getz(b),
    swap,
    (uint32_t )5);
  return;
}

void Hacl_EC_Point_copy(uint64_t *output, uint64_t *input)
{
  memcpy(Hacl_EC_Point_getx(output),
    Hacl_EC_Point_getx(input),
    (uint32_t )5 * sizeof Hacl_EC_Point_getx(input)[0]);
  memcpy(Hacl_EC_Point_getz(output),
    Hacl_EC_Point_getz(input),
    (uint32_t )5 * sizeof Hacl_EC_Point_getz(input)[0]);
}


uint8_t Hacl_EC_Format_zero_8 = (uint8_t )0;

uint64_t Hacl_EC_Format_load64_le(uint8_t *b)
{
  uint8_t b0 = b[(uint32_t )0];
  uint8_t b1 = b[(uint32_t )1];
  uint8_t b2 = b[(uint32_t )2];
  uint8_t b3 = b[(uint32_t )3];
  uint8_t b4 = b[(uint32_t )4];
  uint8_t b5 = b[(uint32_t )5];
  uint8_t b6 = b[(uint32_t )6];
  uint8_t b7 = b[(uint32_t )7];
  return
    (uint64_t )b0
    | (uint64_t )b1 << (uint32_t )8
    | (uint64_t )b2 << (uint32_t )16
    | (uint64_t )b3 << (uint32_t )24
    | (uint64_t )b4 << (uint32_t )32
    | (uint64_t )b5 << (uint32_t )40
    | (uint64_t )b6 << (uint32_t )48
    | (uint64_t )b7 << (uint32_t )56;
}

void Hacl_EC_Format_store64_le(uint8_t *b, uint64_t z)
{
  b[(uint32_t )0] = (uint8_t )z;
  b[(uint32_t )1] = (uint8_t )(z >> (uint32_t )8);
  b[(uint32_t )2] = (uint8_t )(z >> (uint32_t )16);
  b[(uint32_t )3] = (uint8_t )(z >> (uint32_t )24);
  b[(uint32_t )4] = (uint8_t )(z >> (uint32_t )32);
  b[(uint32_t )5] = (uint8_t )(z >> (uint32_t )40);
  b[(uint32_t )6] = (uint8_t )(z >> (uint32_t )48);
  b[(uint32_t )7] = (uint8_t )(z >> (uint32_t )56);
}

void Hacl_EC_Format_fexpand(uint64_t *output, uint8_t *input)
{
  uint64_t mask_51 = (uint64_t )0x7ffffffffffff;
  uint64_t i0 = Hacl_EC_Format_load64_le(input + (uint32_t )0);
  uint64_t i1 = Hacl_EC_Format_load64_le(input + (uint32_t )6);
  uint64_t i2 = Hacl_EC_Format_load64_le(input + (uint32_t )12);
  uint64_t i3 = Hacl_EC_Format_load64_le(input + (uint32_t )19);
  uint64_t i4 = Hacl_EC_Format_load64_le(input + (uint32_t )24);
  uint64_t output0 = i0 & mask_51;
  uint64_t output1 = i1 >> (uint32_t )3 & mask_51;
  uint64_t output2 = i2 >> (uint32_t )6 & mask_51;
  uint64_t output3 = i3 >> (uint32_t )1 & mask_51;
  uint64_t output4 = i4 >> (uint32_t )12 & mask_51;
  output[(uint32_t )0] = output0;
  output[(uint32_t )1] = output1;
  output[(uint32_t )2] = output2;
  output[(uint32_t )3] = output3;
  output[(uint32_t )4] = output4;
}

void Hacl_EC_Format_fcontract(uint8_t *output, uint64_t *input)
{
  uint64_t mask_51 = (uint64_t )0x7ffffffffffff;
  uint64_t nineteen = (uint64_t )19;
  uint64_t t00 = input[(uint32_t )0];
  uint64_t t10 = input[(uint32_t )1];
  uint64_t t20 = input[(uint32_t )2];
  uint64_t t30 = input[(uint32_t )3];
  uint64_t t40 = input[(uint32_t )4];
  uint64_t t11 = t10 + (t00 >> (uint32_t )51);
  uint64_t t01 = t00 & mask_51;
  uint64_t t21 = t20 + (t11 >> (uint32_t )51);
  uint64_t t12 = t11 & mask_51;
  uint64_t t31 = t30 + (t21 >> (uint32_t )51);
  uint64_t t22 = t21 & mask_51;
  uint64_t t41 = t40 + (t31 >> (uint32_t )51);
  uint64_t t32 = t31 & mask_51;
  uint64_t t02 = t01 + nineteen * (t41 >> (uint32_t )51);
  uint64_t t42 = t41 & mask_51;
  uint64_t t13 = t12 + (t02 >> (uint32_t )51);
  uint64_t t03 = t02 & mask_51;
  uint64_t t23 = t22 + (t13 >> (uint32_t )51);
  uint64_t t14 = t13 & mask_51;
  uint64_t t33 = t32 + (t23 >> (uint32_t )51);
  uint64_t t24 = t23 & mask_51;
  uint64_t t43 = t42 + (t33 >> (uint32_t )51);
  uint64_t t34 = t33 & mask_51;
  uint64_t t04 = t03 + nineteen * (t43 >> (uint32_t )51);
  uint64_t t44 = t43 & mask_51;
  uint64_t t05 = t04 + nineteen;
  uint64_t t15 = t14 + (t05 >> (uint32_t )51);
  uint64_t t06 = t05 & mask_51;
  uint64_t t25 = t24 + (t15 >> (uint32_t )51);
  uint64_t t16 = t15 & mask_51;
  uint64_t t35 = t34 + (t25 >> (uint32_t )51);
  uint64_t t26 = t25 & mask_51;
  uint64_t t45 = t44 + (t35 >> (uint32_t )51);
  uint64_t t36 = t35 & mask_51;
  uint64_t t07 = t06 + nineteen * (t45 >> (uint32_t )51);
  uint64_t t46 = t45 & mask_51;
  uint64_t two52 = (uint64_t )0x8000000000000;
  uint64_t t08 = t07 + two52 - nineteen;
  uint64_t t17 = t16 + two52 - (uint64_t )1;
  uint64_t t27 = t26 + two52 - (uint64_t )1;
  uint64_t t37 = t36 + two52 - (uint64_t )1;
  uint64_t t47 = t46 + two52 - (uint64_t )1;
  uint64_t t18 = t17 + (t08 >> (uint32_t )51);
  uint64_t t0 = t08 & mask_51;
  uint64_t t28 = t27 + (t18 >> (uint32_t )51);
  uint64_t t1 = t18 & mask_51;
  uint64_t t38 = t37 + (t28 >> (uint32_t )51);
  uint64_t t2 = t28 & mask_51;
  uint64_t t48 = t47 + (t38 >> (uint32_t )51);
  uint64_t t3 = t38 & mask_51;
  uint64_t t4 = t48 & mask_51;
  uint64_t o0 = t0 | t1 << (uint32_t )51;
  uint64_t o1 = t1 >> (uint32_t )13 | t2 << (uint32_t )38;
  uint64_t o2 = t2 >> (uint32_t )26 | t3 << (uint32_t )25;
  uint64_t o3 = t3 >> (uint32_t )39 | t4 << (uint32_t )12;
  Hacl_EC_Format_store64_le(output + (uint32_t )0, o0);
  Hacl_EC_Format_store64_le(output + (uint32_t )8, o1);
  Hacl_EC_Format_store64_le(output + (uint32_t )16, o2);
  Hacl_EC_Format_store64_le(output + (uint32_t )24, o3);
  return;
}

void Hacl_EC_Format_scalar_of_point(uint8_t *scalar, uint64_t *point)
{
  uint64_t *x = Hacl_EC_Point_getx(point);
  uint64_t *z = Hacl_EC_Point_getz(point);
  uint64_t zmone[5] = { 0 };
  Hacl_Bignum_crecip(zmone, z);
  Hacl_Bignum_fmul(z, x, zmone);
  Hacl_EC_Format_fcontract(scalar, z);
}


void
Hacl_EC_AddAndDouble_fmonty(
  uint64_t *pp,
  uint64_t *ppq,
  uint64_t *p,
  uint64_t *pq,
  uint64_t *qmqp
)
{
  uint64_t *qx = Hacl_EC_Point_getx(qmqp);
  uint64_t *x2 = Hacl_EC_Point_getx(pp);
  uint64_t *z2 = Hacl_EC_Point_getz(pp);
  uint64_t *x3 = Hacl_EC_Point_getx(ppq);
  uint64_t *z3 = Hacl_EC_Point_getz(ppq);
  uint64_t *x = Hacl_EC_Point_getx(p);
  uint64_t *z = Hacl_EC_Point_getz(p);
  uint64_t *xprime = Hacl_EC_Point_getx(pq);
  uint64_t *zprime = Hacl_EC_Point_getz(pq);
  uint64_t buf[40] = { 0 };
  uint64_t *origx = buf + (uint32_t )0;
  uint64_t *origxprime = buf + (uint32_t )5;
  uint64_t *zzz = buf + (uint32_t )10;
  uint64_t *xx = buf + (uint32_t )15;
  uint64_t *zz = buf + (uint32_t )20;
  uint64_t *xxprime = buf + (uint32_t )25;
  uint64_t *zzprime = buf + (uint32_t )30;
  uint64_t *zzzprime = buf + (uint32_t )35;
  memcpy(origx, x, (uint32_t )5 * sizeof x[0]);
  Hacl_Bignum_fsum(x, z);
  Hacl_Bignum_fdifference(z, origx);
  memcpy(origxprime, xprime, (uint32_t )5 * sizeof xprime[0]);
  Hacl_Bignum_fsum(xprime, zprime);
  Hacl_Bignum_fdifference(zprime, origxprime);
  Hacl_Bignum_fmul(xxprime, xprime, z);
  Hacl_Bignum_fmul(zzprime, x, zprime);
  memcpy(origxprime, xxprime, (uint32_t )5 * sizeof xxprime[0]);
  Hacl_Bignum_fsum(xxprime, zzprime);
  Hacl_Bignum_fdifference(zzprime, origxprime);
  Hacl_Bignum_fsquare_times(x3, xxprime, (uint32_t )1);
  Hacl_Bignum_fsquare_times(zzzprime, zzprime, (uint32_t )1);
  Hacl_Bignum_fmul(z3, zzzprime, qx);
  Hacl_Bignum_fsquare_times(xx, x, (uint32_t )1);
  Hacl_Bignum_fsquare_times(zz, z, (uint32_t )1);
  Hacl_Bignum_fmul(x2, xx, zz);
  Hacl_Bignum_fdifference(zz, xx);
  Hacl_Bignum_fscalar(zzz, zz, (uint64_t )121665);
  Hacl_Bignum_fsum(zzz, xx);
  Hacl_Bignum_fmul(z2, zz, zzz);
}


void
Hacl_EC_Ladder_cmult_small_loop(
  uint64_t *nq,
  uint64_t *nqpq,
  uint64_t *nq2,
  uint64_t *nqpq2,
  uint64_t *q,
  uint8_t byt,
  uint32_t i
)
{
  uint64_t *nqx = Hacl_EC_Point_getx(nq);
  uint64_t *nqz = Hacl_EC_Point_getz(nq);
  uint64_t *nqpqx = Hacl_EC_Point_getx(nqpq);
  uint64_t *nqpqz = Hacl_EC_Point_getz(nqpq);
  uint64_t *nqx2 = Hacl_EC_Point_getx(nq2);
  uint64_t *nqz2 = Hacl_EC_Point_getz(nq2);
  uint64_t *nqpqx2 = Hacl_EC_Point_getx(nqpq2);
  uint64_t *nqpqz2 = Hacl_EC_Point_getz(nqpq2);
  if (i == (uint32_t )0)
    return;
  else
  {
    uint64_t bit = (uint64_t )(byt >> (uint32_t )7);
    Hacl_EC_Point_swap_conditional(nq, nqpq, bit);
    Hacl_EC_AddAndDouble_fmonty(nq2, nqpq2, nq, nqpq, q);
    Hacl_EC_Point_swap_conditional(nq2, nqpq2, bit);
    uint64_t *t0 = nq;
    uint64_t *nq = nq2;
    uint64_t *nq2 = t0;
    uint64_t *t = nqpq;
    uint64_t *nqpq = nqpq2;
    uint64_t *nqpq2 = t;
    uint8_t byt0 = byt << (uint32_t )1;
    Hacl_EC_Ladder_cmult_small_loop(nq, nqpq, nq2, nqpq2, q, byt0, i - (uint32_t )1);
    return;
  }
}

void
Hacl_EC_Ladder_cmult_big_loop(
  uint8_t *n,
  uint64_t *nq,
  uint64_t *nqpq,
  uint64_t *nq2,
  uint64_t *nqpq2,
  uint64_t *q,
  uint32_t i
)
{
  if (i == (uint32_t )0)
    return;
  else
  {
    uint32_t i0 = i - (uint32_t )1;
    uint8_t byte = n[i0];
    Hacl_EC_Ladder_cmult_small_loop(nq, nqpq, nq2, nqpq2, q, byte, (uint32_t )8);
    Hacl_EC_Ladder_cmult_big_loop(n, nq, nqpq, nq2, nqpq2, q, i0);
    return;
  }
}

void Hacl_EC_Ladder_cmult(uint64_t *result, uint8_t *n, uint64_t *q)
{
  uint64_t *nq = result;
  uint64_t buf0[10] = { 0 };
  uint64_t
  *nqpq = Hacl_EC_Point_make(buf0 + (uint32_t )0, buf0 + (uint32_t )0, buf0 + (uint32_t )5);
  uint64_t buf1[10] = { 0 };
  uint64_t
  *nqpq2 = Hacl_EC_Point_make(buf1 + (uint32_t )0, buf1 + (uint32_t )0, buf1 + (uint32_t )5);
  uint64_t buf[10] = { 0 };
  uint64_t *nq2 = Hacl_EC_Point_make(buf + (uint32_t )0, buf + (uint32_t )0, buf + (uint32_t )5);
  Hacl_EC_Point_copy(nqpq, q);
  Hacl_EC_Ladder_cmult_big_loop(n, nq, nqpq, nq2, nqpq2, q, (uint32_t )32);
  Hacl_EC_Point_copy(result, nq);
}


void Hacl_EC_crypto_scalarmult(uint8_t *mypublic, uint8_t *secret, uint8_t *basepoint)
{
  uint64_t buf0[10] = { 0 };
  uint64_t *x0 = buf0 + (uint32_t )0;
  uint64_t *y0 = buf0 + (uint32_t )0;
  uint64_t *z0 = buf0 + (uint32_t )5;
  uint64_t *p = Hacl_EC_Point_make(x0, y0, z0);
  Hacl_EC_Format_fexpand(x0, basepoint);
  z0[(uint32_t )0] = (uint64_t )1;
  uint64_t *q = p;
  uint64_t buf[10] = { 0 };
  uint64_t *x1 = buf + (uint32_t )0;
  uint64_t *y = buf + (uint32_t )0;
  uint64_t *z = buf + (uint32_t )5;
  x1[(uint32_t )0] = (uint64_t )1;
  uint64_t *p0 = Hacl_EC_Point_make(x1, y, z);
  uint64_t *nq = p0;
  uint64_t *x = Hacl_EC_Point_getx(nq);
  uint64_t *z1 = Hacl_EC_Point_getz(nq);
  uint64_t zmone[5] = { 0 };
  uint8_t e[32] = { 0 };
  memcpy(e, secret, (uint32_t )32 * sizeof secret[0]);
  uint8_t e00 = e[(uint32_t )0];
  uint8_t e310 = e[(uint32_t )31];
  uint8_t e0 = e00 & (uint8_t )248;
  uint8_t e31 = e310 & (uint8_t )127;
  uint8_t e311 = e31 | (uint8_t )64;
  e[(uint32_t )0] = e0;
  e[(uint32_t )31] = e311;
  uint8_t *scalar = e;
  Hacl_EC_Ladder_cmult(nq, scalar, q);
  Hacl_EC_Format_scalar_of_point(mypublic, nq);
}

