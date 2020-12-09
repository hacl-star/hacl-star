module Hacl.Impl.Poly

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.Poly.Field

module ST = FStar.HyperStack.ST
module BSeq = Lib.ByteSequence
module LSeq = Lib.Sequence
module Loops = Lib.LoopCombinators

module S = Spec.Poly

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let state_inv_t (h:mem) (acc:felem) (p:precomp_r) : Type0 =
  felem_fits h acc (2, 2, 2, 2, 2) /\
  precomp_r_pre h p


private
val encode_block:
     f:felem
  -> b:lbuffer uint8 16ul ->
  Stack unit
  (requires fun h ->
    live h b /\ live h f /\ disjoint b f)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    felem_fits h1 f (1, 1, 1, 1, 1) /\
    as_nat h1 f == S.encode_block (as_seq h0 b))

let encode_block f b =
  load_felem_le f b;
  set_bit128 f


private
val poly1305_update1:
     acc:felem
  -> p:precomp_r
  -> b:lbuffer uint8 16ul ->
  Stack unit
  (requires fun h ->
    live h acc /\ live h p /\ live h b /\
    disjoint acc p /\ disjoint acc b /\
    state_inv_t h acc p)
  (ensures  fun h0 _ h1 -> modifies (loc acc) h0 h1 /\
    feval h1 acc == S.poly1305_update1 (feval h0 (gsub p 0ul 5ul)) (as_seq h0 b) (feval h0 acc) /\
    state_inv_t h1 acc p)

let poly1305_update1 acc p b =
  push_frame ();
  let e = create 5ul (u64 0) in
  encode_block e b;
  let h1 = ST.get () in
  Math.Lemmas.small_mod (as_nat h1 e) S.prime;
  fadd_mul_r acc e p;
  pop_frame ()


val poly1305_update_multi:
     acc:felem
  -> p:precomp_r
  -> len:size_t{v len % 16 = 0}
  -> msg:lbuffer uint8 len ->
  Stack unit
  (requires fun h ->
    live h acc /\ live h p /\ live h msg /\
    disjoint acc p /\ disjoint acc msg /\
    state_inv_t h acc p)
  (ensures  fun h0 _ h1 -> modifies (loc acc) h0 h1 /\
    feval h1 acc == S.poly1305_update_multi (as_seq h0 msg) (feval h0 (gsub p 0ul 5ul)) (feval h0 acc) /\
    state_inv_t h1 acc p)

let poly1305_update_multi acc p len msg =
  let nb = len /. 16ul in
  let h0 = ST.get () in

  [@ inline_let]
  let spec_fh h0 =
    S.poly1305_update1_f (as_seq h0 msg) (feval h0 (gsub p 0ul 5ul)) in

  [@ inline_let]
  let inv h (i:nat{i <= v nb}) =
    modifies (loc acc) h0 h /\
    state_inv_t h acc p /\
    feval h acc == Loops.repeati i (spec_fh h0) (feval h0 acc) in

  Loops.eq_repeati0 (v nb) (spec_fh h0) (feval h0 acc);
  Lib.Loops.for (size 0) nb inv
  (fun i ->
    Loops.unfold_repeati (v nb) (spec_fh h0) (feval h0 acc) (v i);
    Math.Lemmas.multiply_fractions (v len) 16;
    Math.Lemmas.lemma_mult_le_right 16 (v i) (v nb);
    let block = sub msg (i *! 16ul) 16ul in
    poly1305_update1 acc p block);

  let h1 = ST.get () in
  assert (feval h1 acc == Loops.repeati (v nb) (spec_fh h0) (feval h0 acc))
