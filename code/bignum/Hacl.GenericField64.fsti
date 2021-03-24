module Hacl.GenericField64

open FStar.Mul

module BN = Hacl.Bignum
module MA = Hacl.Bignum.MontArithmetic

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let t_limbs: Hacl.Bignum.Definitions.limb_t = Lib.IntTypes.U64

[@@ CPrologue
"/*******************************************************************************

A verified field arithmetic library.

This is a 64-bit optimized version, where bignums are represented as an array
of `len` unsigned 64-bit integers, i.e. uint64_t[len].

All the arithmetic operations are performed in the Montgomery domain.

All the functions below preserve the following invariant for a bignum `aM` in
Montgomery form.
  • aM < n

*******************************************************************************/\n";

Comment "Check whether this library will work for a modulus `n`.

  The function returns false if any of the following preconditions are violated,
  true otherwise.
  • n % 2 = 1
  • 1 < n "]
val field_modulus_check: len:BN.meta_len t_limbs -> MA.bn_field_check_modulus_st t_limbs len

[@@ Comment "Allocate and initialize a montgomery context.

  The argument n is meant to be `len` limbs in size, i.e. uint64_t[len]."]
val field_init: len:BN.meta_len t_limbs -> MA.bn_field_init_st t_limbs len

[@@ Comment "Return a size of the modulus `n` in limbs.

  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init."]
val field_get_len: k:MA.bn_mont_ctx_u64 -> MA.bn_field_get_len_st k

[@@ Comment "Convert a bignum from the regular representation to the Montgomery representation.

  Write `a * R mod n` in `aM`.

  The arguments a and aM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init."]
val to_field: k:MA.bn_mont_ctx_u64 -> MA.bn_to_field_st k

[@@ Comment "Convert a result back from the Montgomery representation to the regular representation.

  Write `aM / R mod n` in `a`, i.e.
  Hacl_GenericField64_from_field(k, Hacl_GenericField64_to_field(k, a)) == a % n

  The arguments a and aM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init."]
val from_field: k:MA.bn_mont_ctx_u64 -> MA.bn_from_field_st k

[@@ Comment "Write `aM + bM mod n` in `cM`.

  The arguments aM, bM, and cM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init."]
val add: k:MA.bn_mont_ctx_u64 -> MA.bn_field_add_st k

[@@ Comment "Write `aM - bM mod n` to `cM`.

  The arguments aM, bM, and cM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init."]
val sub: k:MA.bn_mont_ctx_u64 -> MA.bn_field_sub_st k

[@@ Comment "Write `aM * bM mod n` in `cM`.

  The arguments aM, bM, and cM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init."]
val mul: k:MA.bn_mont_ctx_u64 -> MA.bn_field_mul_st k

[@@ Comment "Write `aM * aM mod n` in `cM`.

  The arguments aM and cM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init."]
val sqr: k:MA.bn_mont_ctx_u64 -> MA.bn_field_sqr_st k

[@@ Comment "Convert a bignum `one` to its Montgomery representation.

  The argument oneM is meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init."]
val one: k:MA.bn_mont_ctx_u64 -> MA.bn_field_one_st k

[@@ Comment "Write `aM ^ b mod n` in `resM`.

  The arguments aM and resM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than exp_vartime.

  Before calling this function, the caller will need to ensure that
  the following preconditions are observed.
  • 0 < b
  • b < pow2 bBits "]
val exp_consttime: k:MA.bn_mont_ctx_u64 -> MA.bn_field_exp_consttime_st k

[@@ Comment "Write `aM ^ b mod n` in `resM`.

  The arguments aM and resM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  The function is *NOT* constant-time on the argument b. See the
  exp_consttime function for constant-time variant.

  Before calling this function, the caller will need to ensure that
  the following preconditions are observed.
  • 0 < b
  • b < pow2 bBits "]
val exp_vartime: k:MA.bn_mont_ctx_u64 -> MA.bn_field_exp_vartime_st k

[@@ Comment "Write `aM ^ (-1) mod n` in `aInvM`.

  The arguments aM and aInvM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  Before calling this function, the caller will need to ensure that
  the following preconditions are observed.
  • n is a prime
  • 0 < aM "]
val inverse: k:MA.bn_mont_ctx_u64 -> MA.bn_field_inv_st k
