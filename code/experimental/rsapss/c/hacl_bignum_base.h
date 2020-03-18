#include <stdint.h>
#include <immintrin.h>
#include <x86intrin.h>


/*
unsigned char _addcarry_u64 (unsigned char c_in, unsigned __int64 a, unsigned __int64 b, unsigned __int64 * out)

Description
Add unsigned 64-bit integers a and b with unsigned 8-bit carry-in c_in (carry flag),
and store the unsigned 64-bit result in out, and the carry-out in dst (carry or overflow flag).
*/

#define Hacl_Bignum_Base_addcarry_u64_st(c_in, a, b, out) \
  (_addcarry_u64(c_in, a, b, (long long unsigned int *) out))


/*
unsigned char _subborrow_u64 (unsigned char b_in, unsigned __int64 a, unsigned __int64 b, unsigned __int64 * out)

Description
Add unsigned 8-bit borrow b_in (carry flag) to unsigned 64-bit integer b, and subtract the result from
unsigned 64-bit integer a. Store the unsigned 64-bit result in out, and the carry-out in dst (carry or overflow flag).
*/

#define Hacl_Bignum_Base_subborrow_u64_st(b_in, a, b, out)  \
  (_subborrow_u64(b_in, a, b, (long long unsigned int *) out))

