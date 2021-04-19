module Hacl.GenericField64

open FStar.Mul

module BN = Hacl.Bignum
module MA = Hacl.Bignum.MontArithmetic

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let t_limbs: Hacl.Bignum.Definitions.limb_t = Lib.IntTypes.U64

let pbn_mont_ctx_u64 = MA.pbn_mont_ctx_u64

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

[@@ Comment "Heap-allocate and initialize a montgomery context.

  The argument n is meant to be `len` limbs in size, i.e. uint64_t[len].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n % 2 = 1
  • 1 < n

  The caller will need to call Hacl_GenericField64_field_free on the return value
  to avoid memory leaks."]
val field_init: len:BN.meta_len t_limbs -> MA.bn_field_init_st t_limbs len

[@@ Comment "Deallocate the memory previously allocated by Hacl_GenericField64_field_init.

  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init."]
val field_free: MA.bn_field_free_st t_limbs

[@@ Comment "Return the size of a modulus `n` in limbs.

  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init."]
val field_get_len: MA.bn_field_get_len_st t_limbs

[@@ Comment "Convert a bignum from the regular representation to the Montgomery representation.

  Write `a * R mod n` in `aM`.

  The argument a and the outparam aM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init."]
val to_field: len:Ghost.erased _ -> MA.bn_to_field_st t_limbs len

[@@ Comment "Convert a result back from the Montgomery representation to the regular representation.

  Write `aM / R mod n` in `a`, i.e.
  Hacl_GenericField64_from_field(k, Hacl_GenericField64_to_field(k, a)) == a % n

  The argument aM and the outparam a are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init."]
val from_field: len:Ghost.erased _ -> MA.bn_from_field_st t_limbs len

[@@ Comment "Write `aM + bM mod n` in `cM`.

  The arguments aM, bM, and the outparam cM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init."]
val add: len:Ghost.erased _ -> MA.bn_field_add_st t_limbs len

[@@ Comment "Write `aM - bM mod n` to `cM`.

  The arguments aM, bM, and the outparam cM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init."]
val sub: len:Ghost.erased _ -> MA.bn_field_sub_st t_limbs len

[@@ Comment "Write `aM * bM mod n` in `cM`.

  The arguments aM, bM, and the outparam cM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init."]
val mul: len:Ghost.erased _ -> MA.bn_field_mul_st t_limbs len

[@@ Comment "Write `aM * aM mod n` in `cM`.

  The argument aM and the outparam cM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init."]
val sqr: len:Ghost.erased _ -> MA.bn_field_sqr_st t_limbs len

[@@ Comment "Convert a bignum `one` to its Montgomery representation.

  The outparam oneM is meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init."]
val one: len:Ghost.erased _ -> MA.bn_field_one_st t_limbs len

[@@ Comment "Write `aM ^ b mod n` in `resM`.

  The argument aM and the outparam resM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than exp_vartime.

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • b < pow2 bBits "]
val exp_consttime: len:Ghost.erased _ -> MA.bn_field_exp_consttime_st t_limbs len

[@@ Comment "Write `aM ^ b mod n` in `resM`.

  The argument aM and the outparam resM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  The function is *NOT* constant-time on the argument b. See the
  exp_consttime function for constant-time variant.

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • b < pow2 bBits "]
val exp_vartime: len:Ghost.erased _ -> MA.bn_field_exp_vartime_st t_limbs len

[@@ Comment "Write `aM ^ (-1) mod n` in `aInvM`.

  The argument aM and the outparam aInvM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n is a prime
  • 0 < aM "]
val inverse: len:Ghost.erased _ -> MA.bn_field_inv_st t_limbs len
