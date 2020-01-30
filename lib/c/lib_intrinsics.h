#ifndef __Int_Intrin_H
#define __Int_Intrin_H

#include <sys/types.h>
#include <immintrin.h>
#include <x86intrin.h>

#define Lib_IntTypes_Intrinsics_add_carry_u64(x1, x2, x3, x4) \
  (_addcarry_u64(x1, x2, x3, (long long unsigned int *) x4))

#define Lib_IntTypes_Intrinsics_sub_borrow_u64(x1, x2, x3, x4) \
  (_subborrow_u64(x1, x2, x3, (long long unsigned int *) x4))

#endif
