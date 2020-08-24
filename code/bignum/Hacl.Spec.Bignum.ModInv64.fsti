module Hacl.Spec.Bignum.ModInv64

open FStar.Mul

open Lib.IntTypes

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(** Precomputed constant for Montgomery arithmetic *)

val mod_inv_u64: n0:uint64 -> uint64

val mod_inv_u64_lemma: n0:uint64 -> Lemma
  (requires v n0 % 2 == 1)
  (ensures (1 + v n0 * v (mod_inv_u64 n0)) % pow2 64 == 0)
