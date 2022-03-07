#include <string.h>
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include "kremlin/internal/target.h"

#include "Hacl_Spec.h"
#include "Hacl_Kremlib.h"
#include "lib_intrinsics.h"

void bench_bignum_mul(uint64_t *a, uint64_t *b, uint64_t *res);

void bench_multiplication_buffer(uint64_t *a, uint64_t *b, uint64_t *t);
