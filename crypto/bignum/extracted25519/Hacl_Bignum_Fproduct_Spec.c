#include "Hacl_Bignum_Fproduct_Spec.h"

void *Hacl_Bignum_Fproduct_Spec_copy_from_wide_spec_(void *s, Prims_nat i, void *tmp)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void *Hacl_Bignum_Fproduct_Spec_copy_from_wide_spec(void *s)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void *Hacl_Bignum_Fproduct_Spec_shift_spec(void *s)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void
*Hacl_Bignum_Fproduct_Spec_sum_scalar_multiplication_spec(
  void *sw,
  void *s,
  uint64_t scalar,
  Prims_nat i
)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void *Hacl_Bignum_Fproduct_Spec_shift_reduce_spec(void *s)
{
  return Hacl_Bignum_Modulo_reduce_spec(Hacl_Bignum_Fproduct_Spec_shift_spec(s));
}

void
Hacl_Bignum_Fproduct_Spec_mul_shift_reduce_pre(
  void *output,
  void *input,
  void *input2,
  Prims_nat ctr
)
{
  return;
}

void
*Hacl_Bignum_Fproduct_Spec_mul_shift_reduce_spec(
  void *output,
  void *input,
  void *input2,
  Prims_nat ctr
)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void *Hacl_Bignum_Fproduct_Spec_carry_wide_spec(void *s, Prims_nat i)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void *Hacl_Bignum_Fproduct_Spec_carry_0_to_1_spec(void *input)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void *Hacl_Bignum_Fproduct_Spec_fmul_spec(void *input, void *input2)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

