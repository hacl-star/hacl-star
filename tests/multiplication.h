#include <string.h>
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include "kremlin/internal/target.h"

#include "Hacl_Spec.h"
#include "Hacl_Kremlib.h"
#include "lib_intrinsics.h"

void bench_unroll1_bignum_mul(uint64_t *a, uint64_t *b, uint64_t *res);

void bench_bignum_mul(uint64_t *a, uint64_t *b, uint64_t *res);

void bench_multiplication_buffer(uint64_t *a, uint64_t *b, uint64_t *t);

void bench_montgomery_reduction_buffer(uint64_t* t, uint64_t* result);

void bench_bignum_reduction(uint64_t *c, uint64_t *res);

void bench_bignum_sqr(uint64_t *a, uint64_t *res);

void bench_sq(uint64_t *f, uint64_t *out);

void bench_mont_sqr_u64_p256(uint64_t *aM, uint64_t *resM);

void bench_bignum_mont_sqr_u64_p256(uint64_t *aM, uint64_t *resM);

void bench_bignum_mont_sqr_u64(uint64_t *aM, uint64_t *resM);

void bench_mul_red_p256(uint64_t *aM, uint64_t *resM);

void bench_bignum_mul_red_p256(uint64_t *aM, uint64_t *resM);

void bench_bignum_mul_red(uint64_t *aM, uint64_t *resM);
