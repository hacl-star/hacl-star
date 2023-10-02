module Hacl.Spec.P256.PrecompTable

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

open Hacl.Impl.P256.Point

module S = Spec.P256
module SM = Hacl.Spec.P256.Montgomery
module FL = FStar.List.Tot

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

unfold
let create4 (x0 x1 x2 x3:uint64) : list uint64 = [x0; x1; x2; x3]

inline_for_extraction noextract
let felem_list {| cp:S.curve_params |} =
    x:list uint64{FL.length x == v cp.bn_limbs}
inline_for_extraction noextract
let point_list {| cp:S.curve_params |} =
    x:list uint64{FL.length x == 3 * v cp.bn_limbs}

inline_for_extraction noextract
let felem_to_list {| cp:S.curve_params |} (x:S.felem) : felem_list =
  if cp.bn_limbs = 4ul then 
    [@inline_let] let x0 = x % pow2 64 in
    [@inline_let] let x1 = x / pow2 64 % pow2 64 in
    [@inline_let] let x2 = x / pow2 128 % pow2 64 in
    [@inline_let] let x3 = x / pow2 192 % pow2 64 in
    [@inline_let] let r = create4 (u64 x0) (u64 x1) (u64 x2) (u64 x3) in
    assert_norm (FL.length r = 4);
    r
  else admit()

inline_for_extraction noextract
let proj_point_to_list {| S.curve_params |} (p:S.proj_point) : point_list =
  [@inline_let] let (px, py, pz) = p in
  [@inline_let] let pxM = SM.to_mont px in
  [@inline_let] let pyM = SM.to_mont py in
  [@inline_let] let pzM = SM.to_mont pz in
  FL.(felem_to_list pxM @ felem_to_list pyM @ felem_to_list pzM)


inline_for_extraction noextract
let point_inv_list {| cp:S.curve_params |} (p:point_list) =
  let x = Seq.seq_of_list p <: lseq uint64 (3 * v cp.bn_limbs) in
  point_inv_seq x

noextract
let point_eval_list {| cp: S.curve_params |} (p:point_list) =
  let x = Seq.seq_of_list p <: lseq uint64 (3 * v cp.bn_limbs)  in
  from_mont_point (as_point_nat_seq x)
    

val proj_point_to_list_lemma {| S.curve_params |} : p:S.proj_point ->
  Lemma (point_inv_list (proj_point_to_list p) /\ point_eval_list (proj_point_to_list p) == p)
