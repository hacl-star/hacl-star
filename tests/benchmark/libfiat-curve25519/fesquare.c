#include <stdint.h>
#include <stdbool.h>
#include <x86intrin.h>
#include "liblow.h"

#include "fesquare.h"

typedef unsigned int uint128_t __attribute__((mode(TI)));

#if (defined(__GNUC__) || defined(__GNUG__)) && !(defined(__clang__)||defined(__INTEL_COMPILER))
// https://gcc.gnu.org/bugzilla/show_bug.cgi?id=81294
#define _subborrow_u32 __builtin_ia32_sbb_u32
#define _subborrow_u64 __builtin_ia32_sbb_u64
#endif

#undef force_inline
#define force_inline __attribute__((always_inline))

void force_inline fesquare(uint64_t* out, uint64_t x7, uint64_t x8, uint64_t x6, uint64_t x4, uint64_t x2)
{  uint64_t x9 = (x2 * 0x2);
{  uint64_t x10 = (x4 * 0x2);
{  uint64_t x11 = ((x6 * 0x2) * 0x13);
{  uint64_t x12 = (x7 * 0x13);
{  uint64_t x13 = (x12 * 0x2);
{  uint128_t x14 = ((((uint128_t)x2 * x2) + ((uint128_t)x13 * x4)) + ((uint128_t)x11 * x8));
{  uint128_t x15 = ((((uint128_t)x9 * x4) + ((uint128_t)x13 * x6)) + ((uint128_t)x8 * (x8 * 0x13)));
{  uint128_t x16 = ((((uint128_t)x9 * x6) + ((uint128_t)x4 * x4)) + ((uint128_t)x13 * x8));
{  uint128_t x17 = ((((uint128_t)x9 * x8) + ((uint128_t)x10 * x6)) + ((uint128_t)x7 * x12));
{  uint128_t x18 = ((((uint128_t)x9 * x7) + ((uint128_t)x10 * x8)) + ((uint128_t)x6 * x6));
{  uint64_t x19 = (uint64_t) (x14 >> 0x33);
{  uint64_t x20 = ((uint64_t)x14 & 0x7ffffffffffff);
{  uint128_t x21 = (x19 + x15);
{  uint64_t x22 = (uint64_t) (x21 >> 0x33);
{  uint64_t x23 = ((uint64_t)x21 & 0x7ffffffffffff);
{  uint128_t x24 = (x22 + x16);
{  uint64_t x25 = (uint64_t) (x24 >> 0x33);
{  uint64_t x26 = ((uint64_t)x24 & 0x7ffffffffffff);
{  uint128_t x27 = (x25 + x17);
{  uint64_t x28 = (uint64_t) (x27 >> 0x33);
{  uint64_t x29 = ((uint64_t)x27 & 0x7ffffffffffff);
{  uint128_t x30 = (x28 + x18);
{  uint64_t x31 = (uint64_t) (x30 >> 0x33);
{  uint64_t x32 = ((uint64_t)x30 & 0x7ffffffffffff);
{  uint64_t x33 = (x20 + (0x13 * x31));
{  uint64_t x34 = (x33 >> 0x33);
{  uint64_t x35 = (x33 & 0x7ffffffffffff);
{  uint64_t x36 = (x34 + x23);
{  uint64_t x37 = (x36 >> 0x33);
{  uint64_t x38 = (x36 & 0x7ffffffffffff);
out[0] = x32;
out[1] = x29;
out[2] = x37 + x26;
out[3] = x38;
out[4] = x35;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[5];
