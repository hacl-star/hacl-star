#include <stdint.h>
#include <stdbool.h>
#include <x86intrin.h>
//#include "liblow.h"

#include "femul.h"

typedef unsigned int uint128_t __attribute__((mode(TI)));

#if (defined(__GNUC__) || defined(__GNUG__)) && !(defined(__clang__)||defined(__INTEL_COMPILER))
// https://gcc.gnu.org/bugzilla/show_bug.cgi?id=81294
#define _subborrow_u32 __builtin_ia32_sbb_u32
#define _subborrow_u64 __builtin_ia32_sbb_u64
#endif

#undef force_inline
#define force_inline __attribute__((always_inline))

void force_inline femul(uint64_t* out, uint64_t x10, uint64_t x11, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x18, uint64_t x19, uint64_t x17, uint64_t x15, uint64_t x13)
{  uint128_t x20 = ((uint128_t)x5 * x13);
{  uint128_t x21 = (((uint128_t)x5 * x15) + ((uint128_t)x7 * x13));
{  uint128_t x22 = ((((uint128_t)x5 * x17) + ((uint128_t)x9 * x13)) + ((uint128_t)x7 * x15));
{  uint128_t x23 = (((((uint128_t)x5 * x19) + ((uint128_t)x11 * x13)) + ((uint128_t)x7 * x17)) + ((uint128_t)x9 * x15));
{  uint128_t x24 = ((((((uint128_t)x5 * x18) + ((uint128_t)x10 * x13)) + ((uint128_t)x11 * x15)) + ((uint128_t)x7 * x19)) + ((uint128_t)x9 * x17));
{  uint64_t x25 = (x10 * 0x13);
{  uint64_t x26 = (x7 * 0x13);
{  uint64_t x27 = (x9 * 0x13);
{  uint64_t x28 = (x11 * 0x13);
{  uint128_t x29 = ((((x20 + ((uint128_t)x25 * x15)) + ((uint128_t)x26 * x18)) + ((uint128_t)x27 * x19)) + ((uint128_t)x28 * x17));
{  uint128_t x30 = (((x21 + ((uint128_t)x25 * x17)) + ((uint128_t)x27 * x18)) + ((uint128_t)x28 * x19));
{  uint128_t x31 = ((x22 + ((uint128_t)x25 * x19)) + ((uint128_t)x28 * x18));
{  uint128_t x32 = (x23 + ((uint128_t)x25 * x18));
{  uint64_t x33 = (uint64_t) (x29 >> 0x33);
{  uint64_t x34 = ((uint64_t)x29 & 0x7ffffffffffff);
{  uint128_t x35 = (x33 + x30);
{  uint64_t x36 = (uint64_t) (x35 >> 0x33);
{  uint64_t x37 = ((uint64_t)x35 & 0x7ffffffffffff);
{  uint128_t x38 = (x36 + x31);
{  uint64_t x39 = (uint64_t) (x38 >> 0x33);
{  uint64_t x40 = ((uint64_t)x38 & 0x7ffffffffffff);
{  uint128_t x41 = (x39 + x32);
{  uint64_t x42 = (uint64_t) (x41 >> 0x33);
{  uint64_t x43 = ((uint64_t)x41 & 0x7ffffffffffff);
{  uint128_t x44 = (x42 + x24);
{  uint64_t x45 = (uint64_t) (x44 >> 0x33);
{  uint64_t x46 = ((uint64_t)x44 & 0x7ffffffffffff);
{  uint64_t x47 = (x34 + (0x13 * x45));
{  uint64_t x48 = (x47 >> 0x33);
{  uint64_t x49 = (x47 & 0x7ffffffffffff);
{  uint64_t x50 = (x48 + x37);
{  uint64_t x51 = (x50 >> 0x33);
{  uint64_t x52 = (x50 & 0x7ffffffffffff);
out[0] = x46;
out[1] = x43;
out[2] = x51 + x40;
out[3] = x52;
out[4] = x49;
}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[5];
