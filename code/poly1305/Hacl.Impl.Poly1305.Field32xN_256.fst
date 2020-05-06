module Hacl.Impl.Poly1305.Field32xN_256

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

/// Note: on fstar-master, we extract everything in a single invocation of
/// KreMLin. However, we cannot mix in the same C file functions that cannot
/// assume avx2 and functions that demand it, because the compiler will optimize
/// the fallback version with avx2 instructions, which will in turn generate
/// illegal instruction errors on some target machines.
///
/// The load_accN variants pose a problem, because they all end up in the same
/// file when, really, they should be in separate files to allow compiling each
/// C translation unit with the same flags.
///
/// One way to solve this problem is to mark them noextract
/// inline_for_extraction, as was done previously. Another way would be to fix
/// KreMLin to allow moving functions in a given module to other modules. A
/// third, more mundame fix is to split these functions in separate modules and
/// package them with their top-level bundle file, which will achieve the same
/// effect.

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50 --using_facts_from '* -FStar.Seq'"

val load_acc4:
    acc:felem 4
  -> b:lbuffer uint8 64ul
  -> Stack unit
    (requires fun h ->
      live h acc /\ live h b /\ disjoint acc b /\
      felem_fits h acc (2, 2, 2, 2, 2))
    (ensures  fun h0 _ h1 ->
      modifies (loc acc) h0 h1 /\
      felem_fits h1 acc (3, 3, 3, 3, 3) /\
      feval h1 acc == Vec.load_acc4 (as_seq h0 b) (feval h0 acc).[0])
let load_acc4 acc b =
  push_frame();
  let e = create 5ul (zero 4) in
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
    load_acc5_4 (acc0, acc1, acc2, acc3, acc4) (e0, e1, e2, e3, e4) in
  acc.(0ul) <- acc0;
  acc.(1ul) <- acc1;
  acc.(2ul) <- acc2;
  acc.(3ul) <- acc3;
  acc.(4ul) <- acc4;
  pop_frame()


val fmul_r4_normalize:
    out:felem 4
  -> p:precomp_r 4
  -> Stack unit
    (requires fun h ->
      live h out /\ live h p /\
      felem_fits h out (3, 3, 3, 3, 3) /\
      load_precompute_r_post h p)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      felem_fits h1 out (2, 2, 2, 2, 2) /\
     (let r = feval h0 (gsub p 0ul 5ul) in
      (feval h1 out).[0] == Vec.normalize_4 r.[0] (feval h0 out)))
let fmul_r4_normalize out p =
  let r = sub p 0ul 5ul in
  let r_5 = sub p 5ul 5ul in
  let r4 = sub p 10ul 5ul in

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

  let r150 = r_5.(0ul) in
  let r151 = r_5.(1ul) in
  let r152 = r_5.(2ul) in
  let r153 = r_5.(3ul) in
  let r154 = r_5.(4ul) in

  let r40 = r4.(0ul) in
  let r41 = r4.(1ul) in
  let r42 = r4.(2ul) in
  let r43 = r4.(3ul) in
  let r44 = r4.(4ul) in

  let (o0, o1, o2, o3, o4) =
    fmul_r4_normalize5 (a0, a1, a2, a3, a4) (r10, r11, r12, r13, r14)
      (r150, r151, r152, r153, r154) (r40, r41, r42, r43, r44) in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3;
  out.(4ul) <- o4
