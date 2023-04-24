module Hacl.Spec.P256.PrecompTable

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

open Hacl.Impl.P256.Point

module S = Spec.P256
module SM = Hacl.Spec.P256.Montgomery
module BD = Hacl.Spec.Bignum.Definitions
module FL = FStar.List.Tot
module SPT = Hacl.Spec.PrecompBaseTable

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let create4_lseq (x0 x1 x2 x3:uint64) : lseq uint64 4 =
  let l = [x0; x1; x2; x3] in
  assert_norm (FL.length l = 4);
  Seq.seq_of_list l


val create4_lemma (x0 x1 x2 x3:uint64) :
  Lemma (let s = create4_lseq x0 x1 x2 x3 in
    s.[0] == x0 /\ s.[1] == x1 /\ s.[2] == x2 /\ s.[3] == x3)
let create4_lemma x0 x1 x2 x3 =
  Seq.elim_of_list [x0; x1; x2; x3]

//-----------------------------------

noextract
let list_as_felem4 (f:felem_list) : lseq uint64 4 =
  Seq.seq_of_list f <: lseq uint64 4


val felem_to_list_lemma_eval: x:S.felem ->
  Lemma (BD.bn_v (list_as_felem4 (felem_to_list x)) == x)

let felem_to_list_lemma_eval x =
  let x0 = x % pow2 64 in
  let x1 = x / pow2 64 % pow2 64 in
  let x2 = x / pow2 128 % pow2 64 in
  let x3 = x / pow2 192 % pow2 64 in
  let bn_x = list_as_felem4 (felem_to_list x) in
  create4_lemma (u64 x0) (u64 x1) (u64 x2) (u64 x3);
  assert (v bn_x.[0] == x0 /\ v bn_x.[1] == x1 /\ v bn_x.[2] == x2 /\ v bn_x.[3] == x3);
  Hacl.Impl.P256.Bignum.bn_v_is_as_nat bn_x;
  assert (BD.bn_v bn_x = x0 + x1 * pow2 64 + x2 * pow2 128 + x3 * pow2 192);
  Hacl.Spec.PrecompBaseTable256.lemma_decompose_nat256_as_four_u64 x

//--------------------------------------------

val proj_point_to_list_sub: p:S.proj_point -> Lemma
 (let (px, py, pz) = p in
  let pxM = SM.to_mont px in
  let pyM = SM.to_mont py in
  let pzM = SM.to_mont pz in
  let px_list = felem_to_list pxM in
  let py_list = felem_to_list pyM in
  let pz_list = felem_to_list pzM in
  let p_list = FL.(px_list @ py_list @ pz_list) in

  let p_lseq = Seq.seq_of_list p_list <: lseq uint64 12 in
  let px_lseq = Seq.seq_of_list px_list <: lseq uint64 4 in
  let py_lseq = Seq.seq_of_list py_list <: lseq uint64 4 in
  let pz_lseq = Seq.seq_of_list pz_list <: lseq uint64 4 in
  sub p_lseq 0 4 == px_lseq /\
  sub p_lseq 4 4 == py_lseq /\
  sub p_lseq 8 4 == pz_lseq)

let proj_point_to_list_sub p =
  let (px, py, pz) = p in
  let pxM = SM.to_mont px in
  let pyM = SM.to_mont py in
  let pzM = SM.to_mont pz in
  let px_list = felem_to_list pxM in
  let py_list = felem_to_list pyM in
  let pz_list = felem_to_list pzM in

  FL.append_assoc px_list py_list pz_list;
  SPT.seq_of_list_append_lemma px_list py_list;
  SPT.seq_of_list_append_lemma FL.(px_list @ py_list) pz_list


val proj_point_to_list_fits: p:S.proj_point ->
  Lemma (point_inv_list (proj_point_to_list p))

let proj_point_to_list_fits p =
  let (px, py, pz) = p in
  let pxM = SM.to_mont px in
  let pyM = SM.to_mont py in
  let pzM = SM.to_mont pz in

  proj_point_to_list_sub p;
  felem_to_list_lemma_eval pxM;
  felem_to_list_lemma_eval pyM;
  felem_to_list_lemma_eval pzM


val proj_point_to_list_eval: p:S.proj_point ->
  Lemma (point_eval_list (proj_point_to_list p) == p)

let proj_point_to_list_eval p =
  let (px, py, pz) = p in
  let pxM = SM.to_mont px in
  let pyM = SM.to_mont py in
  let pzM = SM.to_mont pz in

  proj_point_to_list_sub p;
  felem_to_list_lemma_eval pxM;
  felem_to_list_lemma_eval pyM;
  felem_to_list_lemma_eval pzM;
  SM.lemma_to_from_mont_id px;
  SM.lemma_to_from_mont_id py;
  SM.lemma_to_from_mont_id pz


let proj_point_to_list_lemma p =
  proj_point_to_list_fits p;
  proj_point_to_list_eval p
