module Hacl.Spec.Bignum.ModInvLimb

open FStar.Mul

open Lib.IntTypes
open Hacl.Spec.Bignum.Definitions

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(** Precomputed constant for Montgomery arithmetic *)

val mod_inv_limb: #t:limb_t -> n0:limb t -> limb t

val mod_inv_limb_lemma: #t:limb_t -> n0:limb t -> Lemma
  (requires v n0 % 2 == 1)
  (ensures (1 + v n0 * v (mod_inv_limb n0)) % pow2 (bits t) == 0)
