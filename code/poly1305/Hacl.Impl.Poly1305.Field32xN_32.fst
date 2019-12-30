module Hacl.Impl.Poly1305.Field32xN_32

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

include Hacl.Spec.Poly1305.Field32xN
open Hacl.Spec.Poly1305.Field32xN.Lemmas

module Vec = Hacl.Spec.Poly1305.Vec
module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

open Hacl.Impl.Poly1305.Field32xN

/// See comments in Hacl.Impl.Poly1305.Field32xN_256

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50 --using_facts_from '* -FStar.Seq'"


val load_acc1:
    acc:felem 1
  -> b:lbuffer uint8 16ul
  -> Stack unit
    (requires fun h ->
      live h acc /\ live h b /\ disjoint acc b /\
      felem_fits h acc (2, 2, 2, 2, 2))
    (ensures  fun h0 _ h1 ->
      modifies (loc acc) h0 h1 /\
      felem_fits h1 acc (3, 3, 3, 3, 3) /\
      feval h1 acc == Vec.load_acc1 (as_seq h0 b) (feval h0 acc).[0])

[@CInline]
let load_acc1 acc b =
  push_frame();
  let h0 = ST.get () in
  LSeq.eq_intro (feval h0 acc) (LSeq.create 1 (feval h0 acc).[0]);
  let e = create 5ul (zero 1) in
  load_blocks e b;
  fadd acc acc e;
  pop_frame()


val fmul_r1_normalize:
    out:felem 1
  -> p:precomp_r 1
  -> Stack unit
    (requires fun h ->
      live h out /\ live h p /\
      felem_fits h out (3, 3, 3, 3, 3) /\
      load_precompute_r_post h p)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      felem_fits h1 out (2, 2, 2, 2, 2) /\
     (let r = feval h0 (gsub p 0ul 5ul) in
      (feval h1 out).[0] == Vec.normalize_1 r.[0] (feval h0 out)))
[@CInline]
let fmul_r1_normalize out p =
  let r = sub p 0ul 5ul in
  let r5 = sub p 5ul 5ul in
  fmul_r out out r r5
