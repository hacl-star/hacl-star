module Hacl.Bignum.ModInvLimb

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions

module S = Hacl.Spec.Bignum.ModInvLimb


#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let mod_inv_limb_st (t:limb_t) =
  n0:limb t ->
  Stack (limb t)
  (requires fun h -> True)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.mod_inv_limb n0)


val mod_inv_limb: #t:limb_t -> mod_inv_limb_st t
