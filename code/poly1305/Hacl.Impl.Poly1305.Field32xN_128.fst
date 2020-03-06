module Hacl.Impl.Poly1305.Field32xN_128

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

include Hacl.Spec.Poly1305.Field32xN
open Hacl.Spec.Poly1305.Field32xN.Lemmas

module Vec = Hacl.Spec.Poly1305.Vec
module ST = FStar.HyperStack.ST

open Hacl.Impl.Poly1305.Field32xN

/// See comments in Hacl.Impl.Poly1305.Field32xN_256

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50 --using_facts_from '* -FStar.Seq'"


val load_acc2:
    acc:felem 2
  -> b:lbuffer uint8 32ul
  -> Stack unit
    (requires fun h ->
      live h acc /\ live h b /\ disjoint acc b /\
      felem_fits h acc (2, 2, 2, 2, 2))
    (ensures  fun h0 _ h1 ->
      modifies (loc acc) h0 h1 /\
      felem_fits h1 acc (3, 3, 3, 3, 3) /\
      feval h1 acc == Vec.load_acc2 (as_seq h0 b) (feval h0 acc).[0])
let load_acc2 acc b =
  push_frame();
  let e = create 5ul (zero 2) in
  load_blocks e b;

  let acc0 = acc.(0ul) in
  let acc1 = acc.(1ul) in
  let acc2 = acc.(2ul) in
  let acc3 = acc.(3ul) in
  let acc4 = acc.(4ul) in
  let e0 = e.(0ul) in
  let e1 = e.(1ul) in
  let e2 = e.(2ul) in
  let e3 = e.(3ul) in
  let e4 = e.(4ul) in

  let (acc0, acc1, acc2, acc3, acc4) =
    load_acc5_2 (acc0, acc1, acc2, acc3, acc4) (e0, e1, e2, e3, e4) in
  acc.(0ul) <- acc0;
  acc.(1ul) <- acc1;
  acc.(2ul) <- acc2;
  acc.(3ul) <- acc3;
  acc.(4ul) <- acc4;
  pop_frame()


val fmul_r2_normalize:
    out:felem 2
  -> p:precomp_r 2
  -> Stack unit
    (requires fun h ->
      live h out /\ live h p /\
      felem_fits h out (3, 3, 3, 3, 3) /\
      load_precompute_r_post h p)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      felem_fits h1 out (2, 2, 2, 2, 2) /\
     (let r = feval h0 (gsub p 0ul 5ul) in
      (feval h1 out).[0] == Vec.normalize_2 r.[0] (feval h0 out)))
let fmul_r2_normalize out p =
  let r = sub p 0ul 5ul in
  let r2 = sub p 10ul 5ul in

  let a0 = out.(0ul) in
  let a1 = out.(1ul) in
  let a2 = out.(2ul) in
  let a3 = out.(3ul) in
  let a4 = out.(4ul) in

  let r10 = r.(0ul) in
  let r11 = r.(1ul) in
  let r12 = r.(2ul) in
  let r13 = r.(3ul) in
  let r14 = r.(4ul) in

  let r20 = r2.(0ul) in
  let r21 = r2.(1ul) in
  let r22 = r2.(2ul) in
  let r23 = r2.(3ul) in
  let r24 = r2.(4ul) in

  let (o0, o1, o2, o3, o4) =
    fmul_r2_normalize5 (a0, a1, a2, a3, a4) (r10, r11, r12, r13, r14) (r20, r21, r22, r23, r24) in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3;
  out.(4ul) <- o4
