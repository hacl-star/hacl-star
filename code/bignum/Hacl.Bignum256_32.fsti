module Hacl.Bignum256_32

open FStar.Mul

module BN = Hacl.Bignum
module BS = Hacl.Bignum.SafeAPI
module MA = Hacl.Bignum.MontArithmetic

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let t_limbs: Hacl.Bignum.Definitions.limb_t = Lib.IntTypes.U32

inline_for_extraction noextract
let n_limbs: BN.meta_len t_limbs = 8ul

inline_for_extraction noextract
let n_bytes = n_limbs `FStar.UInt32.mul` 4ul

// A static assert that the number of bytes vs number of blocks matches. This is
// important for bn_to_bytes_be which takes a number of bytes, not a number of
// limbs. (It would be nice to fix this.)
let _ = assert_norm (Hacl.Bignum.Definitions.blocks n_bytes 4ul = n_limbs)

let _ = assert_norm (256ul = Lib.IntTypes.(size (bits t_limbs)) `FStar.UInt32.mul` n_limbs)

inline_for_extraction noextract
let lbignum = Hacl.Bignum.Definitions.lbignum

[@@ CPrologue
"/*******************************************************************************

A verified 256-bit bignum library.

This is a 32-bit optimized version, where bignums are represented as an array
of eight unsigned 32-bit integers, i.e. uint32_t[8]. Furthermore, the
limbs are stored in little-endian format, i.e. the least significant limb is at
index 0. Each limb is stored in native format in memory. Example:

  uint32_t sixteen[8] = { 0x10; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00 }

We strongly encourage users to go through the conversion functions, e.g.
bn_from_bytes_be, to i) not depend on internal representation choices and ii)
have the ability to switch easily to a 64-bit optimized version in the future.

*******************************************************************************/

/************************/
/* Arithmetic functions */
/************************/\n";
Comment
"Write `a + b mod 2^256` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 256-bit bignums, i.e. uint32_t[8]"]
val add: BN.bn_add_eq_len_st t_limbs n_limbs

[@@ Comment "Write `a - b mod 2^256` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 256-bit bignums, i.e. uint32_t[8]"]
val sub: BN.bn_sub_eq_len_st t_limbs n_limbs

[@@ Comment "Write `(a + b) mod n` in `res`.

  The arguments a, b, n and the outparam res are meant to be 256-bit bignums, i.e. uint32_t[8].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • a < n
  • b < n"]
val add_mod: BN.bn_add_mod_n_st t_limbs n_limbs

[@@ Comment "Write `(a - b) mod n` in `res`.

  The arguments a, b, n and the outparam res are meant to be 256-bit bignums, i.e. uint32_t[8].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • a < n
  • b < n"]
val sub_mod: BN.bn_sub_mod_n_st t_limbs n_limbs

[@@ Comment "Write `a * b` in `res`.

  The arguments a and b are meant to be 256-bit bignums, i.e. uint32_t[8].
  The outparam res is meant to be a 512-bit bignum, i.e. uint32_t[16]."]
val mul: a:lbignum t_limbs n_limbs -> BN.bn_karatsuba_mul_st t_limbs n_limbs a

[@@ Comment "Write `a * a` in `res`.

  The argument a is meant to be a 256-bit bignum, i.e. uint32_t[8].
  The outparam res is meant to be a 512-bit bignum, i.e. uint32_t[16]."]
val sqr: a:lbignum t_limbs n_limbs -> BN.bn_karatsuba_sqr_st t_limbs n_limbs a

[@@ Comment "Write `a mod n` in `res`.

  The argument a is meant to be a 512-bit bignum, i.e. uint32_t[16].
  The argument n and the outparam res are meant to be 256-bit bignums, i.e. uint32_t[8].

  The function returns false if any of the following preconditions are violated,
  true otherwise.
   • 1 < n
   • n % 2 = 1"]
val mod: BS.bn_mod_slow_safe_st t_limbs n_limbs

[@@ Comment "Write `a ^ b mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 256-bit bignums, i.e. uint32_t[8].

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  The function is *NOT* constant-time on the argument b. See the
  mod_exp_consttime_* functions for constant-time variants.

  The function returns false if any of the following preconditions are violated,
  true otherwise.
   • n % 2 = 1
   • 1 < n
   • b < pow2 bBits
   • a < n"]
val mod_exp_vartime: BS.bn_mod_exp_safe_st t_limbs n_limbs

[@@ Comment "Write `a ^ b mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 256-bit bignums, i.e. uint32_t[8].

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than mod_exp_vartime.

  The function returns false if any of the following preconditions are violated,
  true otherwise.
   • n % 2 = 1
   • 1 < n
   • b < pow2 bBits
   • a < n"]
val mod_exp_consttime: BS.bn_mod_exp_safe_st t_limbs n_limbs

[@@ Comment "Write `a ^ (-1) mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 256-bit bignums, i.e. uint32_t[8].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n is a prime

  The function returns false if any of the following preconditions are violated, true otherwise.
  • n % 2 = 1
  • 1 < n
  • 0 < a
  • a < n"]
val mod_inv_prime_vartime: BS.bn_mod_inv_prime_safe_st t_limbs n_limbs

[@@ CPrologue
"\n/**********************************************/
/* Arithmetic functions with precomputations. */
/**********************************************/\n";

Comment "Heap-allocate and initialize a montgomery context.

  The argument n is meant to be a 256-bit bignum, i.e. uint32_t[8].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n % 2 = 1
  • 1 < n

  The caller will need to call Hacl_Bignum256_mont_ctx_free on the return value
  to avoid memory leaks."]
val mont_ctx_init: MA.bn_field_init_st t_limbs n_limbs

[@@ Comment "Deallocate the memory previously allocated by Hacl_Bignum256_mont_ctx_init.

  The argument k is a montgomery context obtained through Hacl_Bignum256_mont_ctx_init."]
val mont_ctx_free: MA.bn_field_free_st t_limbs

[@@ Comment "Write `a mod n` in `res`.

  The argument a is meant to be a 512-bit bignum, i.e. uint32_t[16].
  The outparam res is meant to be a 256-bit bignum, i.e. uint32_t[8].
  The argument k is a montgomery context obtained through Hacl_Bignum256_mont_ctx_init."]
val mod_precomp: BS.bn_mod_slow_ctx_st t_limbs n_limbs

[@@ Comment "Write `a ^ b mod n` in `res`.

  The arguments a and the outparam res are meant to be 256-bit bignums, i.e. uint32_t[8].
  The argument k is a montgomery context obtained through Hacl_Bignum256_mont_ctx_init.

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  The function is *NOT* constant-time on the argument b. See the
  mod_exp_consttime_* functions for constant-time variants.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • b < pow2 bBits
  • a < n"]
val mod_exp_vartime_precomp: BS.bn_mod_exp_ctx_st t_limbs n_limbs

[@@ Comment "Write `a ^ b mod n` in `res`.

  The arguments a and the outparam res are meant to be 256-bit bignums, i.e. uint32_t[8].
  The argument k is a montgomery context obtained through Hacl_Bignum256_mont_ctx_init.

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than mod_exp_vartime_*.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • b < pow2 bBits
  • a < n"]
val mod_exp_consttime_precomp: BS.bn_mod_exp_ctx_st t_limbs n_limbs

[@@ Comment "Write `a ^ (-1) mod n` in `res`.

  The argument a and the outparam res are meant to be 256-bit bignums, i.e. uint32_t[8].
  The argument k is a montgomery context obtained through Hacl_Bignum256_mont_ctx_init.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n is a prime
  • 0 < a
  • a < n"]
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

  The argument b points to a 256-bit bignum.
  The outparam res points to 32 bytes of valid memory."]
val bn_to_bytes_be: Hacl.Bignum.Convert.bn_to_bytes_be_st t_limbs n_bytes

[@@ Comment "Serialize a bignum into little-endian memory.

  The argument b points to a 256-bit bignum.
  The outparam res points to 32 bytes of valid memory."]
val bn_to_bytes_le: Hacl.Bignum.Convert.bn_to_bytes_le_st t_limbs n_bytes

[@@ CPrologue
"\n/***************/
/* Comparisons */
/***************/\n";
Comment "Returns 2^32 - 1 if a < b, otherwise returns 0.

 The arguments a and b are meant to be 256-bit bignums, i.e. uint32_t[8]."]
val lt_mask: BN.bn_lt_mask_st t_limbs n_limbs

[@@ Comment "Returns 2^32 - 1 if a = b, otherwise returns 0.

 The arguments a and b are meant to be 256-bit bignums, i.e. uint32_t[8]."]
val eq_mask: BN.bn_eq_mask_st t_limbs n_limbs
