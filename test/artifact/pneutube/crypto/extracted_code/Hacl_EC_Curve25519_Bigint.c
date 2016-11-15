#include "Hacl_EC_Curve25519_Bigint.h"

Prims_pos Hacl_EC_Curve25519_Bigint_byte_templ(Prims_nat x)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

Prims_nat Hacl_EC_Curve25519_Bigint_bitweight(Prims_pos (*t)(Prims_nat x0), Prims_nat n)
{
  return (Prims_nat )(uint8_t )0;
}

void Hacl_EC_Curve25519_Bigint_bitweight_def(Prims_pos (*t)(Prims_nat x0), Prims_int n)
{
  return;
}

Prims_nat Hacl_EC_Curve25519_Bigint_eval(FStar_HyperStack_mem h, uint64_t *b, Prims_nat n)
{
  return (Prims_nat )(uint8_t )0;
}

Prims_nat
Hacl_EC_Curve25519_Bigint_eval_wide(FStar_HyperStack_mem h, FStar_UInt128_t *b, Prims_nat n)
{
  return (Prims_nat )(uint8_t )0;
}

void Hacl_EC_Curve25519_Bigint_eval_def(FStar_HyperStack_mem h, uint64_t *b, Prims_nat n)
{
  return;
}

void
Hacl_EC_Curve25519_Bigint_eval_wide_def(
  FStar_HyperStack_mem h,
  FStar_UInt128_t *b,
  Prims_nat n
)
{
  return;
}

Prims_nat Hacl_EC_Curve25519_Bigint_eval_bytes(FStar_HyperStack_mem h, uint8_t *b, Prims_nat n)
{
  return (Prims_nat )(uint8_t )0;
}

Prims_nat Hacl_EC_Curve25519_Bigint_maxValue(FStar_HyperStack_mem h, uint64_t *b, Prims_pos l)
{
  return (Prims_nat )(uint8_t )0;
}

Prims_nat
Hacl_EC_Curve25519_Bigint_maxValue_wide(
  FStar_HyperStack_mem h,
  FStar_UInt128_t *b,
  Prims_pos l
)
{
  return (Prims_nat )(uint8_t )0;
}

void
Hacl_EC_Curve25519_Bigint_maxValue_lemma_aux(FStar_HyperStack_mem h, uint64_t *b, Prims_pos l)
{
  return;
}

void Hacl_EC_Curve25519_Bigint_maxValue_lemma(FStar_HyperStack_mem h, uint64_t *b)
{
  return;
}

void
Hacl_EC_Curve25519_Bigint_maxValue_bound_lemma_aux(
  FStar_HyperStack_mem h,
  uint64_t *b,
  Prims_pos l,
  Prims_nat bound
)
{
  return;
}

void
Hacl_EC_Curve25519_Bigint_maxValue_bound_lemma(
  FStar_HyperStack_mem h,
  uint64_t *b,
  Prims_nat bound
)
{
  return;
}

Prims_nat Hacl_EC_Curve25519_Bigint_maxValueNorm(FStar_HyperStack_mem h, uint64_t *b)
{
  return (Prims_nat )(uint8_t )0;
}

Prims_nat
Hacl_EC_Curve25519_Bigint_maxValueIdx(FStar_HyperStack_mem h, uint64_t *b, Prims_pos l)
{
  return (Prims_nat )(uint8_t )0;
}

void
Hacl_EC_Curve25519_Bigint_maxValue_eq_lemma(
  FStar_HyperStack_mem ha,
  FStar_HyperStack_mem hb,
  uint64_t *a,
  uint64_t *b,
  Prims_pos l
)
{
  return;
}

void
Hacl_EC_Curve25519_Bigint_maxValueNorm_eq_lemma(
  FStar_HyperStack_mem ha,
  FStar_HyperStack_mem hb,
  uint64_t *a,
  uint64_t *b
)
{
  return;
}

void
Hacl_EC_Curve25519_Bigint_maxValue_wide_lemma_aux(
  FStar_HyperStack_mem h,
  FStar_UInt128_t *b,
  Prims_pos l
)
{
  return;
}

void Hacl_EC_Curve25519_Bigint_maxValue_wide_lemma(FStar_HyperStack_mem h, FStar_UInt128_t *b)
{
  return;
}

void
Hacl_EC_Curve25519_Bigint_maxValue_wide_bound_lemma_aux(
  FStar_HyperStack_mem h,
  FStar_UInt128_t *b,
  Prims_pos l,
  Prims_nat bound
)
{
  return;
}

void
Hacl_EC_Curve25519_Bigint_maxValue_wide_bound_lemma(
  FStar_HyperStack_mem h,
  FStar_UInt128_t *b,
  Prims_nat bound
)
{
  return;
}

Prims_nat
Hacl_EC_Curve25519_Bigint_maxValueNorm_wide(FStar_HyperStack_mem h, FStar_UInt128_t *b)
{
  return (Prims_nat )(uint8_t )0;
}

Prims_nat
Hacl_EC_Curve25519_Bigint_maxValueIdx_wide(
  FStar_HyperStack_mem h,
  FStar_UInt128_t *b,
  Prims_pos l
)
{
  return (Prims_nat )(uint8_t )0;
}

void
Hacl_EC_Curve25519_Bigint_maxValue_wide_eq_lemma(
  FStar_HyperStack_mem ha,
  FStar_HyperStack_mem hb,
  FStar_UInt128_t *a,
  FStar_UInt128_t *b,
  Prims_pos l
)
{
  return;
}

void
Hacl_EC_Curve25519_Bigint_maxValueNorm_wide_eq_lemma(
  FStar_HyperStack_mem ha,
  FStar_HyperStack_mem hb,
  FStar_UInt128_t *a,
  FStar_UInt128_t *b
)
{
  return;
}

void
Hacl_EC_Curve25519_Bigint_eval_eq_lemma(
  FStar_HyperStack_mem ha,
  FStar_HyperStack_mem hb,
  uint64_t *a,
  uint64_t *b,
  Prims_nat len
)
{
  return;
}

void
Hacl_EC_Curve25519_Bigint_eval_partial_eq_lemma(
  FStar_HyperStack_mem ha,
  FStar_HyperStack_mem hb,
  uint64_t *a,
  uint64_t *b,
  Prims_nat ctr,
  Prims_nat len
)
{
  return;
}

void Hacl_EC_Curve25519_Bigint_eval_null(FStar_HyperStack_mem h, uint64_t *b, Prims_nat len)
{
  return;
}

void
Hacl_EC_Curve25519_Bigint_max_value_of_null_lemma(
  FStar_HyperStack_mem h,
  uint64_t *b,
  Prims_pos l
)
{
  return;
}

