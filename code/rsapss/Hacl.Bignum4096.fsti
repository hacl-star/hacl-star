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

[@@ Comment "Write `a + b mod 2^4096` in `res`.

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

val mod_exp: BE.bn_mod_exp_st 4096ul n
