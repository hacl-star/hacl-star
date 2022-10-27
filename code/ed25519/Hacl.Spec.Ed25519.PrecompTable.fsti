module Hacl.Spec.Ed25519.PrecompTable

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

module F51 = Hacl.Impl.Ed25519.Field51
module SF51 = Hacl.Spec.Curve25519.Field51.Definition

module S = Spec.Ed25519
module SC = Spec.Curve25519
module FL = FStar.List.Tot

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

unfold
let create5 (x0 x1 x2 x3 x4:uint64) : list uint64 = [x0; x1; x2; x3; x4]

inline_for_extraction noextract
let felem_list = x:list uint64{FL.length x == 5}
inline_for_extraction noextract
let point_list = x:list uint64{FL.length x == 20}

inline_for_extraction noextract
let pow51 = SF51.pow51

[@"opaque_to_smt"]
let pow102: (pow102:pos{pow2 102 == pow102 /\ pow102 = pow51 * pow51}) =
  let pow102:pos = normalize_term (pow2 102) in
  normalize_term_spec (pow2 102);
  Math.Lemmas.pow2_plus 51 51;
  pow102

[@"opaque_to_smt"]
let pow153: (pow153:pos{pow2 153 == pow153 /\ pow153 = pow51 * pow51 * pow51}) =
  let pow153:pos = normalize_term (pow2 153) in
  normalize_term_spec (pow2 153);
  Math.Lemmas.pow2_plus 51 51;
  Math.Lemmas.pow2_plus 102 51;
  pow153

[@"opaque_to_smt"]
let pow204: (pow204:pos{pow2 204 == pow204 /\ pow204 = pow51 * pow51 * pow51 * pow51}) =
  let pow204:pos = normalize_term (pow2 204) in
  normalize_term_spec (pow2 204);
  Math.Lemmas.pow2_plus 51 51;
  Math.Lemmas.pow2_plus 102 51;
  Math.Lemmas.pow2_plus 153 51;
  pow204


inline_for_extraction noextract
let felem_to_list (x:SC.elem) : felem_list =
  [@inline_let] let x0 = x % pow51 in
  [@inline_let] let x1 = x / pow51 % pow51 in
  [@inline_let] let x2 = x / pow102 % pow51 in
  [@inline_let] let x3 = x / pow153 % pow51 in
  [@inline_let] let x4 = x / pow204 in
  Math.Lemmas.lemma_div_lt_nat x 255 204;
  [@inline_let] let r = create5 (u64 x0) (u64 x1) (u64 x2) (u64 x3) (u64 x4) in
  assert_norm (FL.length r = 5);
  r


inline_for_extraction noextract
let ext_point_to_list (p:S.ext_point) : point_list =
  [@inline_let] let (px, py, pz, pt) = p in
  FL.(felem_to_list px @ felem_to_list py @ felem_to_list pz @ felem_to_list pt)


inline_for_extraction noextract
let point_inv_list (p:point_list) =
  let x = Seq.seq_of_list p <: lseq uint64 20 in
  //F51.inv_ext_point x
  F51.linv x

noextract
let point_eval_list (p:point_list) : GTot S.ext_point =
  let x = Seq.seq_of_list p <: lseq uint64 20 in
  F51.refl_ext_point x

val ext_point_to_list_lemma: p:S.ext_point{Spec.Ed25519.point_inv p} ->
  Lemma (point_inv_list (ext_point_to_list p) /\ point_eval_list (ext_point_to_list p) == p)
