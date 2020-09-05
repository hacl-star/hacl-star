module Hacl.Bignum4096

open FStar.Mul

module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery
module BE = Hacl.Bignum.Exponentiation

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let _ = assert_norm (4096ul = 64ul `FStar.UInt32.mul` 64ul)

inline_for_extraction noextract
let n_limbs: BN.meta_len = 64ul

inline_for_extraction noextract
let n_bytes = n_limbs `FStar.UInt32.mul` 8ul

// A static assert that the number of bytes vs number of blocks matches. This is
// important for bn_to_bytes_be which takes a number of bytes, not a number of
// limbs. (It would be nice to fix this.)
let _ = assert_norm (Hacl.Bignum.Definitions.blocks n_bytes 8ul = n_limbs)

inline_for_extraction noextract
let lbignum = Hacl.Bignum.Definitions.lbignum

[@@ CPrologue
"/************************/
/* Arithmetic functions */
/************************/\n";
Comment
"Write `a + b mod 2^4096` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 4096-bit bignums, i.e. uint64_t[64]"]
val add: Hacl.Bignum.Addition.bn_add_eq_len_st n_limbs

[@@ Comment "Write `a - b mod 2^4096` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 4096-bit bignums, i.e. uint64_t[64]"]
val sub: Hacl.Bignum.Addition.bn_sub_eq_len_st n_limbs

[@@ Comment "Write `a * b` in `res`.

  The arguments a and b are meant to be 4096-bit bignums, i.e. uint64_t[64].
  The outparam res is meant to be a 8192-bit bignum, i.e. uint64_t[128]."]
val mul: a:lbignum n_limbs -> b:lbignum n_limbs -> BN.bn_karatsuba_mul_st a b


[@@ Comment "Write `a ^ b mod n` in `res`.

  The arguments a, n, r2 and the outparam res are meant to be 4096-bit bignums, i.e. uint64_t[64].
  The argument r2 is a precomputed constant 2 ^ 8192 mod n.
  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. For instance, if b is a 4096-bit bignum,
  bBits should be 4096. The function is *NOT* constant-time on the argument b."]
val mod_exp_precompr2: BE.bn_mod_exp_precompr2_st n_limbs

[@@ Comment "Write `a ^ b mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 4096-bit bignums, i.e. uint64_t[64].
  The argument nBits can be less or equal to the exact number of bits of n, but not equal to 0.
  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. For instance, if b is a 4096-bit bignum,
  bBits should be 4096. The function is *NOT* constant-time on the argument b."]
val mod_exp: nBits:_ -> BE.bn_mod_exp_st n_limbs nBits

[@@ Comment "Write `a ^ b mod n` in `res`.

  The arguments a, n, r2 and the outparam res are meant to be 4096-bit bignums, i.e. uint64_t[64].
  The argument r2 is a precomputed constant 2 ^ 8192 mod n.
  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. For instance, if b is a 4096-bit bignum,
  bBits should be 4096. The function is constant-time on the argument b."]
val mod_exp_mont_ladder_precompr2: BE.bn_mod_exp_mont_ladder_precompr2_st n_limbs

[@@ Comment "Write `a ^ b mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 4096-bit bignums, i.e. uint64_t[64].
  The argument nBits can be less or equal to the exact number of bits of n, but not equal to 0.
  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. For instance, if b is a 4096-bit bignum,
  bBits should be 4096. The function is constant-time on the argument b."]
val mod_exp_mont_ladder: nBits:_ -> BE.bn_mod_exp_mont_ladder_st n_limbs nBits

[@@ Comment "Compute `2 ^ (128 * nLen) mod n`.

  The argument n points to a bignum of size nLen of valid memory.
  The argument nBits can be less or equal to the exact number of bits of n.
  The function returns a heap-allocated bignum of size nLen or NULL if nBits is equal to 0.

  If the return value is non-null, clients must eventually call free(3) on it to
  avoid memory leaks."]
val new_precompr2: BM.new_precomp_r2_mod_n_st

[@@ CPrologue
"\n/********************/
/* Loads and stores */
/********************/\n";
Comment
"Load a bid-endian bignum from memory.

  The argument b points to len bytes of valid memory.
  The function returns a heap-allocated bignum of size sufficient to hold the
    result of loading b, or NULL if the amount of required memory would exceed 4GB.

  If the return value is non-null, clients must eventually call free(3) on it to
  avoid memory leaks."]
val new_bn_from_bytes_be: Hacl.Bignum.Convert.new_bn_from_bytes_be_st

[@@ Comment "Serialize a bignum into big-endian memory.

  The argument b points to a 4096-bit bignum.
  The outparam res points to 512 bytes of valid memory."]
val bn_to_bytes_be: Hacl.Bignum.Convert.bn_to_bytes_be_st n_bytes

[@@ CPrologue
"\n/***************/
/* Comparisons */
/***************/\n";
"Returns 2 ^ 64 - 1 if and only if argument a is strictly less than the argument b,
 otherwise returns 0."]
val lt_mask: Hacl.Bignum.bn_lt_mask_st n_limbs
