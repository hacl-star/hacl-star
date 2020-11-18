module Hacl.Bignum256

open FStar.Mul

module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery
module BE = Hacl.Bignum.Exponentiation
module BR = Hacl.Bignum.ModReduction
module BI = Hacl.Bignum.ModInv
module BS = Hacl.Bignum.SafeAPI

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let _ = assert_norm (256ul = 64ul `FStar.UInt32.mul` 4ul)

inline_for_extraction noextract
let t_limbs: Hacl.Bignum.Definitions.limb_t = Lib.IntTypes.U64

inline_for_extraction noextract
let n_limbs: BN.meta_len t_limbs = 4ul

inline_for_extraction noextract
let n_bytes = n_limbs `FStar.UInt32.mul` 8ul

// A static assert that the number of bytes vs number of blocks matches. This is
// important for bn_to_bytes_be which takes a number of bytes, not a number of
// limbs. (It would be nice to fix this.)
let _ = assert_norm (Hacl.Bignum.Definitions.blocks n_bytes 8ul = n_limbs)

inline_for_extraction noextract
let lbignum = Hacl.Bignum.Definitions.lbignum

[@@ CPrologue
"/*******************************************************************************

A verified 256-bit bignum library.

This is a 64-bit optimized version, where bignums are represented as an array
of four unsigned 64-bit integers, i.e. uint64_t[4]. Furthermore, the
limbs are stored in little-endian format, i.e. the least significant limb is at
index 0. Each limb is stored in native format in memory. Example:

  uint64_t sixteen[4] = { 0x10; 0x00; 0x00; 0x00 }

We strongly encourage users to go through the conversion functions, e.g.
bn_from_bytes_be, to i) not depend on internal representation choices and ii)
have the ability to switch easily to a 32-bit optimized version in the future.

*******************************************************************************/

/************************/
/* Arithmetic functions */
/************************/\n";
Comment
"Write `a + b mod 2^256` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 256-bit bignums, i.e. uint64_t[4]"]
val add: BN.bn_add_eq_len_st t_limbs n_limbs

[@@ Comment "Write `a - b mod 2^256` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 256-bit bignums, i.e. uint64_t[4]"]
val sub: BN.bn_sub_eq_len_st t_limbs n_limbs

[@@ Comment "Write `a * b` in `res`.

  The arguments a and b are meant to be 256-bit bignums, i.e. uint64_t[4].
  The outparam res is meant to be a 512-bit bignum, i.e. uint64_t[8]."]
val mul: a:lbignum t_limbs n_limbs -> BN.bn_karatsuba_mul_st t_limbs n_limbs a

[@@ Comment "Write `a mod n` in `res`

  The argument a is meant to be a 512-bit bignum, i.e. uint64_t[8].
  The argument n, r2 and the outparam res are meant to be 256-bit bignums, i.e. uint64_t[4].
  The argument r2 is a precomputed constant 2 ^ 512 mod n obtained through Hacl_Bignum256_new_precompr2.

  This function is *UNSAFE* and requires C clients to observe the precondition
  of bn_mod_slow_precompr2_lemma in Hacl.Spec.Bignum.ModReduction.fst, which
  amounts to:
  • 1 < n
  • n % 2 = 1
  • a < n * n

  Owing to the absence of run-time checks, and factoring out the precomputation
  r2, this function is notably faster than mod below."]
val mod_precompr2: BR.bn_mod_slow_precompr2_st t_limbs n_limbs

[@@ Comment "Write `a mod n` in `res`

  The argument a is meant to be a 512-bit bignum, i.e. uint64_t[8].
  The argument n and the outparam res are meant to be 256-bit bignums, i.e. uint64_t[4].

  The function returns false if any of the preconditions of mod_precompr2 above
  are violated, true otherwise."]
val mod: BS.bn_mod_slow_safe_st t_limbs n_limbs

[@@ Comment "Write `a ^ b mod n` in `res`.

  The arguments a, n, r2 and the outparam res are meant to be 256-bit bignums, i.e. uint64_t[4].
  The argument r2 is a precomputed constant 2 ^ 512 mod n obtained through Hacl_Bignum256_new_precompr2.
  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  The function is *NOT* constant-time on the argument b. See the
  mod_exp_mont_ladder_* functions for constant-time variants.

  This function is *UNSAFE* and requires C clients to observe bn_mod_exp_pre
  from Hacl.Spec.Bignum.Exponentiation.fsti, which amounts to:
  • n % 2 = 1
  • 1 < n
  • 0 < b
  • b < pow2 bBits
  • a < n

  Owing to the absence of run-time checks, and factoring out the precomputation
  r2, this function is notably faster than mod_exp below."]
val mod_exp_precompr2: BE.bn_mod_exp_precompr2_st t_limbs n_limbs

[@@ Comment "Write `a ^ b mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 256-bit bignums, i.e. uint64_t[4].
  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

  The function is *NOT* constant-time on the argument b. See the
  mod_exp_mont_ladder_* functions for constant-time variants.

  The function returns false if any of the preconditions of mod_exp_precompr2 are
  violated, true otherwise."]
val mod_exp: BS.bn_mod_exp_safe_st t_limbs n_limbs

[@@ Comment "Write `a ^ b mod n` in `res`.

  The arguments a, n, r2 and the outparam res are meant to be 256-bit bignums, i.e. uint64_t[4].
  The argument r2 is a precomputed constant 2 ^ 512 mod n.
  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than mod_exp_precompr2.

  This function is *UNSAFE* and requires C clients to observe bn_mod_exp_pre
  from Hacl.Spec.Bignum.Exponentiation.fsti, which amounts to:
  • n % 2 = 1
  • 1 < n
  • 0 < b
  • b < pow2 bBits
  • a < n

  Owing to the absence of run-time checks, and factoring out the precomputation
  r2, this function is notably faster than mod_exp_mont_ladder below."]
val mod_exp_mont_ladder_precompr2: BE.bn_mod_exp_mont_ladder_precompr2_st t_limbs n_limbs

[@@ Comment "Write `a ^ b mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 256-bit bignums, i.e. uint64_t[4].
  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than mod_exp.

  The function returns false if any of the preconditions of
  mod_exp_mont_ladder_precompr2 are violated, true otherwise."]
val mod_exp_mont_ladder: BS.bn_mod_exp_safe_st t_limbs n_limbs

[@@ Comment "Compute `2 ^ 512 mod n`.

  The argument n points to a 256-bit bignum of valid memory.
  The function returns a heap-allocated 256-bit bignum, or NULL if:
  • the allocation failed, or
  • n % 2 = 1 && 1 < n does not hold

  If the return value is non-null, clients must eventually call free(3) on it to
  avoid memory leaks."]
val new_precompr2: BS.new_bn_precomp_r2_mod_n_st t_limbs n_limbs

[@@ Comment "Write `a ^ (-1) mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 256-bit bignums, i.e. uint64_t[4].

  This function is *UNSAFE* and requires C clients to observe the precondition of
  bn_mod_inv_prime_lemma from Hacl.Spec.Bignum.ModInv.fst, which amounts to:
  • n is a prime

  The function returns false if any of the following preconditions are violated, true otherwise.
  • n % 2 = 1
  • 1 < n
  • 0 < a
  • a < n "]
val mod_inv_prime: BS.bn_mod_inv_prime_safe_st t_limbs n_limbs

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

[@@ Comment "Serialize a bignum into big-endian memory.

  The argument b points to a 256-bit bignum.
  The outparam res points to 32 bytes of valid memory."]
val bn_to_bytes_be: Hacl.Bignum.Convert.bn_to_bytes_be_st t_limbs n_bytes

[@@ CPrologue
"\n/***************/
/* Comparisons */
/***************/\n";
Comment
"Returns 2 ^ 64 - 1 if and only if argument a is strictly less than the argument b, otherwise returns 0."]
val lt_mask: BN.bn_lt_mask_st t_limbs n_limbs
