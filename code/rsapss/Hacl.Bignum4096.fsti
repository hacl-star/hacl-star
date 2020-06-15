module Hacl.Bignum4096

open FStar.Mul

module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery
module BE = Hacl.Bignum.Exponentiation

let _ = assert_norm (4096ul = 64ul `FStar.UInt32.mul` 64ul)

inline_for_extraction noextract
let n: BN.meta_len = 64ul

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
val add: Hacl.Bignum.Addition.bn_add_eq_len_st n

[@@ Comment "Write `a - b mod 2^4096` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 4096-bit bignums, i.e. uint64_t[64]"]
val sub: Hacl.Bignum.Addition.bn_sub_eq_len_st n

[@@ Comment "Write `a * b` in `res`.

  The arguments a and b are meant to be 4096-bit bignums, i.e. uint64_t[64].
  The outparam res is meant to be a 8192-bit bignum, i.e. uint64_t[128]."]
val mul: a:lbignum n -> b:lbignum n -> BN.bn_mul_st a b

[@@ Comment "Write `a ^ b mod n1` in `res`.

  The arguments a, n1 and the outparam res are meant to be 4096-bit bignums, i.e. uint64_t[64].
  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. For instance, if b is a 4096-bit bignum,
  bBits should be 4096."]
val mod_exp: BE.bn_mod_exp_st 4096ul n

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
val bn_to_bytes_be: Hacl.Bignum.Convert.bn_to_bytes_be_st n

[@@ CPrologue
"\n/***************/
/* Comparisons */
/***************/\n";
Comment
"Returns true if and only if argument a is strictly see then argument b."]
val lt: Hacl.Bignum.bn_is_less_st n
