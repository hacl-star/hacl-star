module Hacl.Bignum.ModInv64

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module Loops = Lib.LoopCombinators
module LSeq = Lib.Sequence

module S = Hacl.Spec.Bignum.ModInv64

friend Hacl.Spec.Bignum.ModInv64

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"


inline_for_extraction noextract
val mod_inv_u64_:
    alpha:uint64
  -> beta:uint64
  -> ub:lbuffer uint64 1ul
  -> vb:lbuffer uint64 1ul ->
  Stack unit
  (requires fun h -> live h ub /\ live h vb /\ disjoint ub vb)
  (ensures  fun h0 _ h1 -> modifies (loc ub |+| loc vb) h0 h1 /\
    (let (us, vs) =
      Loops.repeat_gen 64 S.mod_inv_u64_t
	(S.mod_inv_u64_f alpha beta)
	(LSeq.index (as_seq h0 ub) 0, LSeq.index (as_seq h0 vb) 0) in
    LSeq.index (as_seq h1 ub) 0 == us /\ LSeq.index (as_seq h1 vb) 0 == vs))

let mod_inv_u64_ alpha beta ub vb =
  [@inline_let]
  let refl h i : GTot (uint64 & uint64) = LSeq.index (as_seq h ub) 0, LSeq.index (as_seq h vb) 0 in
  [@inline_let]
  let footprint i = loc ub |+| loc vb in
  [@inline_let]
  let spec h0 = S.mod_inv_u64_f alpha beta in
  let h0 = ST.get () in
  loop h0 64ul S.mod_inv_u64_t refl footprint spec
  (fun i ->
    Loops.unfold_repeat_gen 64 S.mod_inv_u64_t (spec h0) (refl h0 0) (v i);
    let us = ub.(0ul) in
    let vs = vb.(0ul) in
    let u_is_odd = u64 0 -. (us &. u64 1) in
    let beta_if_u_is_odd = beta &. u_is_odd in
    ub.(0ul) <- ((us ^. beta_if_u_is_odd) >>. 1ul) +. (us &. beta_if_u_is_odd);

    let alpha_if_u_is_odd = alpha &. u_is_odd in
    vb.(0ul) <- (vs >>. 1ul) +. alpha_if_u_is_odd
  )


[@CInline]
let mod_inv_u64 n0 =
  push_frame ();
  let alpha = u64 1 <<. 63ul in
  let beta = n0 in
  let ub = create 1ul (u64 0) in
  let vb = create 1ul (u64 0) in
  ub.(0ul) <- u64 1;
  vb.(0ul) <- u64 0;
  mod_inv_u64_ alpha beta ub vb;
  let res = vb.(0ul) in
  pop_frame ();
  res
