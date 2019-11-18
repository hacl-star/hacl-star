module Hacl.Poly.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence


open Hacl.Poly

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"


///
///  Poly evaluation properties
///

val load_acc_v_lemma: #w:lanes -> b:block_v w -> acc0:felem -> r:felem -> Lemma
  (FStar.Math.Lemmas.cancel_mul_mod w blocksize;
   normalize_v r (load_acc_v b acc0) == repeat_blocks_multi blocksize b (poly_update1 r) acc0)


val poly_update_nblocks_lemma: #w:lanes -> r:felem -> b:block_v w -> acc_v0:felem_v w -> Lemma
  (let pre = create w (pow_w w r) in
  FStar.Math.Lemmas.cancel_mul_mod w blocksize;
  normalize_v r (poly_update_nblocks #w pre b acc_v0) == repeat_blocks_multi blocksize b (poly_update1 r) (normalize_v r acc_v0))
