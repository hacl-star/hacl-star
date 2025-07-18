module Hacl.Spec.Poly1305.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.IntVector

module Loops = Lib.LoopCombinators
module VecLemmas = Lib.Vec.Lemmas
module SeqLemmas = Lib.Sequence.Lemmas
module Lemmas = Hacl.Spec.Poly1305.Lemmas
module S = Spec.Poly1305

include Hacl.Spec.Poly1305.Vec

#set-options "--fuel 0 --ifuel 0"

let load_acc_lemma1 b acc0 r =
  let f = S.poly1305_update1 r size_block in
  let nb = size_block / size_block in
  let repeat_f = repeat_blocks_f size_block b f nb in

  lemma_repeat_blocks_multi size_block b f acc0;
  Loops.unfold_repeati nb repeat_f acc0 0;
  Loops.eq_repeati0 nb repeat_f acc0

#push-options "--z3smtopt '(set-option :smt.arith.solver 2)'"
let load_acc_lemma2 b acc0 r =
  let b0 = Seq.slice b 0 size_block in
  let b1 = Seq.slice b size_block (2 * size_block) in
  let c0 = pfadd (pow2 128) (nat_from_bytes_le b0) in
  let c1 = pfadd (pow2 128) (nat_from_bytes_le b1) in

  FStar.Math.Lemmas.modulo_lemma c1 prime;

  let f = S.poly1305_update1 r size_block in
  let nb = (2 * size_block) / size_block in
  let repeat_f = repeat_blocks_f size_block b f nb in

  lemma_repeat_blocks_multi size_block b f acc0;
  Loops.unfold_repeati nb repeat_f acc0 1;
  Loops.unfold_repeati nb repeat_f acc0 0;
  Loops.eq_repeati0 nb repeat_f acc0;
  Lemmas.poly_update_multi_lemma_load2_simplify acc0 r c0 c1;
  ()
#pop-options

#push-options "--z3smtopt '(set-option :smt.arith.solver 2)'"
let load_acc_lemma4 b acc0 r =
  let b0 = Seq.slice b 0 size_block in
  let b1 = Seq.slice b size_block (2 * size_block) in
  let b2 = Seq.slice b (2 * size_block) (3 * size_block) in
  let b3 = Seq.slice b (3 * size_block) (4 * size_block) in

  let c0 = pfadd (pow2 128) (nat_from_bytes_le b0) in
  let c1 = pfadd (pow2 128) (nat_from_bytes_le b1) in
  let c2 = pfadd (pow2 128) (nat_from_bytes_le b2) in
  let c3 = pfadd (pow2 128) (nat_from_bytes_le b3) in

  FStar.Math.Lemmas.modulo_lemma c1 prime;
  FStar.Math.Lemmas.modulo_lemma c2 prime;
  FStar.Math.Lemmas.modulo_lemma c3 prime;

  let f = S.poly1305_update1 r size_block in
  let nb = (4 * size_block) / size_block in
  let repeat_f = repeat_blocks_f size_block b f nb in

  lemma_repeat_blocks_multi size_block b f acc0;
  Loops.unfold_repeati nb repeat_f acc0 3;
  Loops.unfold_repeati nb repeat_f acc0 2;
  Loops.unfold_repeati nb repeat_f acc0 1;
  Loops.unfold_repeati nb repeat_f acc0 0;
  Loops.eq_repeati0 nb repeat_f acc0;
  Lemmas.poly_update_multi_lemma_load4_simplify acc0 r c0 c1 c2 c3;
  ()
#pop-options

let load_acc_lemma #w b acc0 r =
  match w with
  | 1 -> load_acc_lemma1 b acc0 r
  | 2 -> load_acc_lemma2 b acc0 r
  | 4 -> load_acc_lemma4 b acc0 r

let poly_update_nblocks_lemma1 r b acc_v0 =
  let acc0 = normalize_n r acc_v0 in
  let f = S.poly1305_update1 r size_block in
  let nb = size_block / size_block in
  let repeat_f = repeat_blocks_f size_block b f nb in

  lemma_repeat_blocks_multi size_block b f acc0;
  Loops.unfold_repeati nb repeat_f acc0 0;
  Loops.eq_repeati0 nb repeat_f acc0


#push-options "--z3smtopt '(set-option :smt.arith.solver 2)'"
let poly_update_nblocks_lemma2 r b acc_v0 =
  let acc0 = normalize_n r acc_v0 in
  let b0 = Seq.slice b 0 size_block in
  let b1 = Seq.slice b size_block (2 * size_block) in
  let c0 = pfadd (pow2 128) (nat_from_bytes_le b0) in
  let c1 = pfadd (pow2 128) (nat_from_bytes_le b1) in

  let f = S.poly1305_update1 r size_block in
  let nb = (2 * size_block) / size_block in
  let repeat_f = repeat_blocks_f size_block b f nb in

  lemma_repeat_blocks_multi size_block b f acc0;
  Loops.unfold_repeati nb repeat_f acc0 1;
  Loops.unfold_repeati nb repeat_f acc0 0;
  Loops.eq_repeati0 nb repeat_f acc0;
  Lemmas.poly_update_multi_lemma_load2_simplify acc0 r c0 c1;
  Lemmas.poly_update_repeat_blocks_multi_lemma2_simplify acc_v0.[0] acc_v0.[1] c0 c1 r;
  ()
#pop-options


#push-options "--z3smtopt '(set-option :smt.arith.solver 2)' --z3rlimit 40"

let poly_update_nblocks_lemma4 r b acc_v0 =
  let acc0 = normalize_n r acc_v0 in
  let b0 = Seq.slice b 0 size_block in
  let b1 = Seq.slice b size_block (2 * size_block) in
  let b2 = Seq.slice b (2 * size_block) (3 * size_block) in
  let b3 = Seq.slice b (3 * size_block) (4 * size_block) in

  let c0 = pfadd (pow2 128) (nat_from_bytes_le b0) in
  let c1 = pfadd (pow2 128) (nat_from_bytes_le b1) in
  let c2 = pfadd (pow2 128) (nat_from_bytes_le b2) in
  let c3 = pfadd (pow2 128) (nat_from_bytes_le b3) in

  let r2 = pfmul r r in
  let r4 = pfmul r2 r2 in

  let f = S.poly1305_update1 r size_block in
  let nb = (4 * size_block) / size_block in
  let repeat_f = repeat_blocks_f size_block b f nb in

  lemma_repeat_blocks_multi size_block b f acc0;
  Loops.unfold_repeati nb repeat_f acc0 3;
  Loops.unfold_repeati nb repeat_f acc0 2;
  Loops.unfold_repeati nb repeat_f acc0 1;
  Loops.unfold_repeati nb repeat_f acc0 0;
  Loops.eq_repeati0 nb repeat_f acc0;

  Lemmas.poly_update_repeat_blocks_multi_lemma4_simplify
    acc_v0.[0] acc_v0.[1] acc_v0.[2] acc_v0.[3] c0 c1 c2 c3 r r2 r4;
  ()
#pop-options


let poly_update_nblocks_lemma #w r b acc_v0 =
  match w with
  | 1 -> poly_update_nblocks_lemma1 r b acc_v0
  | 2 -> poly_update_nblocks_lemma2 r b acc_v0
  | 4 -> poly_update_nblocks_lemma4 r b acc_v0



let repeat_blocks_multi_vec_equiv_pre_lemma #w r b acc_v0 =
  poly_update_nblocks_lemma #w r b acc_v0



let poly_update_multi_lemma_v #w text acc_v0 r =
  let rw = compute_rw #w r in
  let f = S.poly1305_update1 r size_block in
  let f_v = poly1305_update_nblocks rw in

  Classical.forall_intro_2 (repeat_blocks_multi_vec_equiv_pre_lemma #w r);
  VecLemmas.lemma_repeat_blocks_multi_vec w size_block text f f_v (normalize_n r) acc_v0



let poly_update_multi_lemma #w text acc0 r =
  let len = length text in
  let blocksize_v = w * size_block in
  let text0 = Seq.slice text 0 blocksize_v in
  let text1 = Seq.slice text blocksize_v len in
  FStar.Math.Lemmas.modulo_addition_lemma len blocksize_v (- 1);
  assert (length text1 % (w * size_block) = 0 /\ length text1 % size_block = 0);

  let f = S.poly1305_update1 r size_block in
  let acc_v0 = load_acc #w text0 acc0 in

  let rp = poly1305_update_multi #w text acc0 r in
  poly_update_multi_lemma_v #w text1 acc_v0 r;
  load_acc_lemma #w text0 acc0 r;
  SeqLemmas.repeat_blocks_multi_split size_block blocksize_v text f acc0



let poly1305_update_vec_lemma #w text acc0 r =
  let len = length text in
  let blocksize_v = w * size_block in
  let len0 = len / blocksize_v * blocksize_v in
  FStar.Math.Lemmas.cancel_mul_mod (len / blocksize_v) blocksize_v;
  assert (len0 % blocksize_v = 0);
  assert (len0 % size_block = 0);

  let text0 = Seq.slice text 0 len0 in
  let f = S.poly1305_update1 r size_block in
  let l = S.poly1305_update_last r in

  if len0 > 0 then begin
    poly_update_multi_lemma #w text0 acc0 r;
    SeqLemmas.repeat_blocks_split size_block len0 text f l acc0 end


let poly1305_vec_lemma #w msg k =
  let acc0, r = S.poly1305_init k in
  poly1305_update_vec_lemma #w msg acc0 r
