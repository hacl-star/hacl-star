module Hacl.Bignum.ModInvLimb

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions

module ST = FStar.HyperStack.ST
module Loops = Lib.LoopCombinators
module LSeq = Lib.Sequence

module S = Hacl.Spec.Bignum.ModInvLimb

friend Hacl.Spec.Bignum.ModInvLimb

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"


inline_for_extraction noextract
val mod_inv_limb_:
    #t:limb_t
  -> alpha:limb t
  -> beta:limb t
  -> ub:lbignum t 1ul
  -> vb:lbignum t 1ul ->
  Stack unit
  (requires fun h -> live h ub /\ live h vb /\ disjoint ub vb)
  (ensures  fun h0 _ h1 -> modifies (loc ub |+| loc vb) h0 h1 /\
    (let (us, vs) =
      Loops.repeat_gen (bits t)
	(S.mod_inv_limb_t t)
	(S.mod_inv_limb_f alpha beta)
	(LSeq.index (as_seq h0 ub) 0, LSeq.index (as_seq h0 vb) 0) in
    LSeq.index (as_seq h1 ub) 0 == us /\ LSeq.index (as_seq h1 vb) 0 == vs))

let mod_inv_limb_ #t alpha beta ub vb =
  [@inline_let]
  let refl h i : GTot (S.mod_inv_limb_t t i) = LSeq.index (as_seq h ub) 0, LSeq.index (as_seq h vb) 0 in
  [@inline_let]
  let footprint i = loc ub |+| loc vb in
  [@inline_let]
  let spec h0 = S.mod_inv_limb_f alpha beta in
  let h0 = ST.get () in
  loop h0 (size (bits t)) (S.mod_inv_limb_t t) refl footprint spec
  (fun i ->
    Loops.unfold_repeat_gen (bits t) (S.mod_inv_limb_t t) (spec h0) (refl h0 0) (v i);
    let us = ub.(0ul) in
    let vs = vb.(0ul) in
    let u_is_odd = uint #t 0 -. (us &. uint #t 1) in
    let beta_if_u_is_odd = beta &. u_is_odd in
    ub.(0ul) <- ((us ^. beta_if_u_is_odd) >>. 1ul) +. (us &. beta_if_u_is_odd);

    let alpha_if_u_is_odd = alpha &. u_is_odd in
    vb.(0ul) <- (vs >>. 1ul) +. alpha_if_u_is_odd
  )


inline_for_extraction noextract
val mk_mod_inv_limb: #t:limb_t -> mod_inv_limb_st t
let mk_mod_inv_limb #t n0 =
  push_frame ();
  let alpha = uint #t 1 <<. size (bits t - 1) in
  let beta = n0 in
  let ub = create 1ul (uint #t 0) in
  let vb = create 1ul (uint #t 0) in
  ub.(0ul) <- uint #t 1;
  vb.(0ul) <- uint #t 0;
  mod_inv_limb_ alpha beta ub vb;
  let res = vb.(0ul) in
  pop_frame ();
  res


[@CInline]
let mod_inv_uint32 : mod_inv_limb_st U32 = mk_mod_inv_limb #U32
[@CInline]
let mod_inv_uint64 : mod_inv_limb_st U64 = mk_mod_inv_limb #U64


let mod_inv_limb #t =
  match t with
  | U32 -> mod_inv_uint32
  | U64 -> mod_inv_uint64
