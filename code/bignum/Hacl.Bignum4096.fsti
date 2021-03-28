module Hacl.Bignum4096

open FStar.Mul

module BN = Hacl.Bignum
module BS = Hacl.Bignum.SafeAPI
module MA = Hacl.Bignum.MontArithmetic
module GF = Hacl.GenericField64

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let t_limbs: Hacl.Bignum.Definitions.limb_t = Lib.IntTypes.U64

inline_for_extraction noextract
let n_limbs: BN.meta_len t_limbs = 64ul

inline_for_extraction noextract
let n_bytes = n_limbs `FStar.UInt32.mul` 8ul

// A static assert that the number of bytes vs number of blocks matches. This is
// important for bn_to_bytes_be which takes a number of bytes, not a number of
// limbs. (It would be nice to fix this.)
let _ = assert_norm (Hacl.Bignum.Definitions.blocks n_bytes 8ul = n_limbs)

let _ = assert_norm (4096ul = Lib.IntTypes.(size (bits t_limbs)) `FStar.UInt32.mul` n_limbs)

inline_for_extraction noextract
let lbignum = Hacl.Bignum.Definitions.lbignum

[@@ CPrologue
"/*******************************************************************************

A verified 4096-bit bignum library.

This is a 64-bit optimized version, where bignums are represented as an array
of sixty four unsigned 64-bit integers, i.e. uint64_t[64]. Furthermore, the
limbs are stored in little-endian format, i.e. the least significant limb is at
index 0. Each limb is stored in native format in memory. Example:

  uint64_t sixteen[64] = { 0x10 }

  (relying on the fact that when an initializer-list is provided, the remainder
  of the object gets initialized as if it had static storage duration, i.e. with
  zeroes)

We strongly encourage users to go through the conversion functions, e.g.
bn_from_bytes_be, to i) not depend on internal representation choices and ii)
have the ability to switch easily to a 32-bit optimized version in the future.

*******************************************************************************/

/************************/
/* Arithmetic functions */
/************************/\n";
Comment
"Write `a + b mod 2^4096` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 4096-bit bignums, i.e. uint64_t[64]"]
val add: BN.bn_add_eq_len_st t_limbs n_limbs

[@@ Comment "Write `a - b mod 2^4096` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 4096-bit bignums, i.e. uint64_t[64]"]
val sub: BN.bn_sub_eq_len_st t_limbs n_limbs

[@@ Comment "Write `a * b` in `res`.

  The arguments a and b are meant to be 4096-bit bignums, i.e. uint64_t[64].
  The outparam res is meant to be a 8192-bit bignum, i.e. uint64_t[128]."]
val mul: a:lbignum t_limbs n_limbs -> BN.bn_karatsuba_mul_st t_limbs n_limbs a

[@@ Comment "Write `a * a` in `res`.

  The argument a is meant to be a 4096-bit bignum, i.e. uint64_t[64].
  The outparam res is meant to be a 8192-bit bignum, i.e. uint64_t[128]."]
val sqr: a:lbignum t_limbs n_limbs -> BN.bn_karatsuba_sqr_st t_limbs n_limbs a

[@@ Comment "Write `a mod n` in `res`.

  The argument a is meant to be a 8192-bit bignum, i.e. uint64_t[128].
  The argument n and the outparam res are meant to be 4096-bit bignums, i.e. uint64_t[64].

  The function returns false if any of the following preconditions are violated,
  true otherwise.
   • 1 < n
   • n % 2 = 1 "]
val mod: BS.bn_mod_slow_safe_st t_limbs n_limbs

[@@ Comment "Write `a ^ b mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 4096-bit bignums, i.e. uint64_t[64].

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

  The function is *NOT* constant-time on the argument b. See the
  mod_exp_consttime_* functions for constant-time variants.

  The function returns false if any of the following preconditions are violated,
  true otherwise.
   • n % 2 = 1
   • 1 < n
   • 0 < b
   • b < pow2 bBits
   • a < n "]
val mod_exp_vartime: BS.bn_mod_exp_safe_st t_limbs n_limbs

[@@ Comment "Write `a ^ b mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 4096-bit bignums, i.e. uint64_t[64].

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than mod_exp_vartime.

  The function returns false if any of the following preconditions are violated,
  true otherwise.
   • n % 2 = 1
   • 1 < n
   • 0 < b
   • b < pow2 bBits
   • a < n "]
val mod_exp_consttime: BS.bn_mod_exp_safe_st t_limbs n_limbs

[@@ Comment "Write `a ^ (-1) mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 4096-bit bignums, i.e. uint64_t[64].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n is a prime

  The function returns false if any of the following preconditions are violated, true otherwise.
  • n % 2 = 1
  • 1 < n
  • 0 < a
  • a < n "]
val mod_inv_prime_vartime: BS.bn_mod_inv_prime_safe_st t_limbs n_limbs

[@@ CPrologue
"\n/**********************************************/
/* Arithmetic functions with precomputations. */
/**********************************************/\n";

Comment "Write `a mod n` in `res`.

  The argument a is meant to be a 8192-bit bignum, i.e. uint64_t[128].
  The outparam res is meant to be a 4096-bit bignum, i.e. uint64_t[64].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init."]
val mod_precomp: BS.bn_mod_slow_ctx_st t_limbs n_limbs

[@@ Comment "Write `a ^ b mod n` in `res`.

  The arguments a and the outparam res are meant to be 4096-bit bignums, i.e. uint64_t[64].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

  The function is *NOT* constant-time on the argument b. See the
  mod_exp_consttime_* functions for constant-time variants.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • 0 < b
  • b < pow2 bBits
  • a < n "]
val mod_exp_vartime_precomp: BS.bn_mod_exp_ctx_st t_limbs n_limbs

[@@ Comment "Write `a ^ b mod n` in `res`.

  The arguments a and the outparam res are meant to be 4096-bit bignums, i.e. uint64_t[64].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than mod_exp_vartime_*.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • 0 < b
  • b < pow2 bBits
  • a < n "]
val mod_exp_consttime_precomp: BS.bn_mod_exp_ctx_st t_limbs n_limbs

[@@ Comment "Write `a ^ (-1) mod n` in `res`.

  The argument a and the outparam res are meant to be 4096-bit bignums, i.e. uint64_t[64].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n is a prime
  • 0 < a
  • a < n "]
val mod_inv_prime_vartime_precomp: BS.bn_mod_inv_prime_ctx_st t_limbs n_limbs

[@@ CPrologue
"\n/********************/
/* Loads and stores */
/********************/\n";
Comment
"Load a bid-endian bignum from memory.

  The argument b points to len bytes of valid memory.
  The function returns a heap-allocated bignum of size sufficient to hold the
   result of loading b, or NULL if either the allocation failed, or the amount of
    required memory would exceed 4GB.

  If the return value is non-null, clients must eventually call free(3) on it to
  avoid memory leaks."]
val new_bn_from_bytes_be: BS.new_bn_from_bytes_be_st t_limbs

[@@ Comment "Load a little-endian bignum from memory.

  The argument b points to len bytes of valid memory.
  The function returns a heap-allocated bignum of size sufficient to hold the
   result of loading b, or NULL if either the allocation failed, or the amount of
    required memory would exceed 4GB.

  If the return value is non-null, clients must eventually call free(3) on it to
  avoid memory leaks."]
val new_bn_from_bytes_le: BS.new_bn_from_bytes_le_st t_limbs

[@@ Comment "Serialize a bignum into big-endian memory.

  The argument b points to a 4096-bit bignum.
  The outparam res points to 512 bytes of valid memory."]
val bn_to_bytes_be: Hacl.Bignum.Convert.bn_to_bytes_be_st t_limbs n_bytes

[@@ Comment "Serialize a bignum into little-endian memory.

  The argument b points to a 4096-bit bignum.
  The outparam res points to 512 bytes of valid memory."]
val bn_to_bytes_le: Hacl.Bignum.Convert.bn_to_bytes_le_st t_limbs n_bytes

[@@ CPrologue
"\n/***************/
/* Comparisons */
/***************/\n";
Comment
"Returns 2 ^ 64 - 1 if and only if the argument a is strictly less than the argument b,
 otherwise returns 0."]
val lt_mask: BN.bn_lt_mask_st t_limbs n_limbs
