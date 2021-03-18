module Hacl.GenericField64

open FStar.Mul

module BN = Hacl.Bignum
module GF = Hacl.Bignum.GenericField

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let t_limbs: Hacl.Bignum.Definitions.limb_t = Lib.IntTypes.U64

[@@ CPrologue
"/*******************************************************************************

A verified field arithmetic library.

This is a 64-bit optimized version, where bignums are represented as an array
of `len` unsigned 64-bit integers, i.e. uint64_t[len].
All the arithmetic operations are performed in the Montgomery domain.

*******************************************************************************/\n";
Comment "Allocate and initialize a montgomery context.

  The argument n is meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument nBits is an exact number of significant bits of n.

  This function is *UNSAFE* and requires C clients to observe bn_mont_ctx_pre
  from Hacl.Spec.Bignum.GenericField.fsti, which amounts to:

  • 0 < nBits /\ (nBits - 1) / bits t < len
  • pow2 (nBits - 1) < n /\ n < pow2 nBits

  • n % 2 = 1
  • 1 < n

  • n is a prime // needed for the modular multiplicative inverse
"]
val field_init: len:BN.meta_len t_limbs -> GF.bn_field_init_st t_limbs len

[@@ Comment "Return a size of the modulus `n` in limbs.

  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init."]
val field_get_len: k:GF.bn_mont_ctx_u64 -> GF.bn_field_get_len_st k

[@@ Comment "Convert a bignum to its Montgomery representation.

  Write `a * R mod n` in `aM`.

  The arguments a and aM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  This function is *UNSAFE* and requires C clients to observe bn_to_field
  from Hacl.Spec.Bignum.GenericField.fsti, which amounts to:
  • a < n
"]
val to_field: k:GF.bn_mont_ctx_u64 -> GF.bn_to_field_st k

[@@ Comment "Convert the result back from the Montgomery representation to the regular representation.

  Write `aM / R mod n` in `a`, i.e.
  Hacl_GenericField64_from_field(k, Hacl_GenericField64_to_field(k, a)) == a

  The arguments a and aM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  This function is *UNSAFE* and requires C clients to observe bn_from_field
  from Hacl.Spec.Bignum.GenericField.fsti, which amounts to:
  • aM < n
"]
val from_field: k:GF.bn_mont_ctx_u64 -> GF.bn_from_field_st k

[@@ Comment "Write `aM + bM mod n` in `cM`.

  The arguments aM, bM, and cM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  This function is *UNSAFE* and requires C clients to observe bn_field_add
  from Hacl.Spec.Bignum.GenericField.fsti, which amounts to:
  • aM < n
  • bM < n "]
val add: k:GF.bn_mont_ctx_u64 -> GF.bn_field_add_st k

[@@ Comment "Write `aM - bM mod n` to `cM`.

  The arguments aM, bM, and cM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  This function is *UNSAFE* and requires C clients to observe bn_field_sub
  from Hacl.Spec.Bignum.GenericField.fsti, which amounts to:
  • aM < n
  • bM < n "]
val sub: k:GF.bn_mont_ctx_u64 -> GF.bn_field_sub_st k

[@@ Comment "Write `aM * bM mod n` in `cM`.

  The arguments aM, bM, and cM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  This function is *UNSAFE* and requires C clients to observe bn_field_mul
  from Hacl.Spec.Bignum.GenericField.fsti, which amounts to:
  • aM < n
  • bM < n "]
val mul: k:GF.bn_mont_ctx_u64 -> GF.bn_field_mul_st k

[@@ Comment "Write `aM * aM mod n` in `cM`.

  The arguments aM and cM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  This function is *UNSAFE* and requires C clients to observe bn_field_sqr
  from Hacl.Spec.Bignum.GenericField.fsti, which amounts to:
  • aM < n "]
val sqr: k:GF.bn_mont_ctx_u64 -> GF.bn_field_sqr_st k

[@@ Comment "Convert a bignum `one` to its Montgomery representation.

  The argument oneM is meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init."]
val one: k:GF.bn_mont_ctx_u64 -> GF.bn_field_one_st k

[@@ Comment "Write `aM ^ (-1) mod n` in `aInvM`.

  The arguments aM and aInvM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  This function is *UNSAFE* and requires C clients to observe bn_field_inv
  from Hacl.Spec.Bignum.GenericField.fsti, which amounts to:
  • aM < n
  • 0 < aM "]
val inverse: k:GF.bn_mont_ctx_u64 -> GF.bn_field_inv_st k
