module Hacl.Bignum256

open FStar.Mul

module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery
module BE = Hacl.Bignum.Exponentiation

let _ = assert_norm (256ul = 64ul `FStar.UInt32.mul` 4ul)

inline_for_extraction noextract
let n_limbs: BN.meta_len = 4ul

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
"Write `a + b mod 2^256` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 256-bit bignums, i.e. uint64_t[64]"]
val add: Hacl.Bignum.Addition.bn_add_eq_len_st n_limbs

[@@ Comment "Write `a - b mod 2^256` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 256-bit bignums, i.e. uint64_t[64]"]
val sub: Hacl.Bignum.Addition.bn_sub_eq_len_st n_limbs

[@@ Comment "Write `a * b` in `res`.

  The arguments a and b are meant to be 256-bit bignums, i.e. uint64_t[64].
  The outparam res is meant to be a 8192-bit bignum, i.e. uint64_t[128]."]
val mul: a:lbignum n_limbs -> b:lbignum n_limbs -> BN.bn_mul_st a b

[@@ Comment "Write `a ^ b mod n1` in `res`.

  The arguments a, n1 and the outparam res are meant to be 256-bit bignums, i.e. uint64_t[64].
  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. For instance, if b is a 256-bit bignum,
  bBits should be 256."]
val mod_exp: BE.bn_mod_exp_st 256ul n_limbs

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

  The argument b points to a 256-bit bignum.
  The outparam res points to 512 bytes of valid memory."]
val bn_to_bytes_be: Hacl.Bignum.Convert.bn_to_bytes_be_st n_bytes

[@@ CPrologue
"\n/***************/
/* Comparisons */
/***************/\n";
Comment
"Returns true if and only if argument a is strictly less than the argument b."]
val lt: Hacl.Bignum.bn_is_less_st n_limbs
