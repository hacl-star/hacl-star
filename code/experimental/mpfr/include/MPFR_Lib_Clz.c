#include "MPFR_Lib_Clz.h"

uint32_t MPFR_Lib_Clz_count_leading_zeros (uint64_t a) {
  return __builtin_clzll(a);
}

