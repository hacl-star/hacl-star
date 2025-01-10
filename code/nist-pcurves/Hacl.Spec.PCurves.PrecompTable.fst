module Hacl.Spec.PCurves.PrecompTable

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

open Hacl.Impl.PCurves.Point

module S = Spec.PCurves
module SM = Hacl.Spec.PCurves.Montgomery
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
let list_as_felem {| cp:S.curve_params |} (f:felem_list) : lseq uint64 (v cp.bn_limbs) =
  Seq.seq_of_list f <: lseq uint64 (v cp.bn_limbs)


val felem_to_list_lemma_rec_eval: {| cp:S.curve_params |} -> x:S.felem -> i:nat ->
  Lemma (requires (i <= v cp.bn_limbs /\ x < pow2 (i * 64))) 
        (ensures (BD.bn_v #U64 #i (Seq.seq_of_list (felem_to_list_rec x i)) == 
                  x))

#push-options "--fuel 2 --ifuel 2"
let rec felem_to_list_lemma_rec_eval x i =
  if i > 0 then (
    [@inline_let] let x0 = x % pow2 64 in
    [@inline_let] let x1 = x / pow2 64 in
    [@inline_let] let l = felem_to_list_rec x1 (i - 1) in
    [@inline_let] let r = (u64 x0) :: l in
    assert (List.Tot.length r == i);
    assert (Seq.length (Seq.seq_of_list r) == i);
    assert (Seq.index (Seq.seq_of_list r) 0 == u64 x0);
    let r0 = Seq.slice (Seq.seq_of_list r) 0 1 in
    let r1 = Seq.slice (Seq.seq_of_list r) 1 i in
    assert (Seq.index r0 0 == u64 x0);
    BD.bn_eval1 #U64 r0;
    assert (BD.bn_v #U64 #1 r0 == x0);
    Seq.lemma_eq_intro (Seq.slice (Seq.seq_of_list r) 1 i) (Seq.seq_of_list l);
    assert (Seq.slice (Seq.seq_of_list r) 1 i == Seq.seq_of_list l);
    BD.bn_eval_split_i #U64 #i (Seq.seq_of_list r) 1;
    assert (BD.bn_v #U64 #i (Seq.seq_of_list r) == 
            BD.bn_v #U64 #1 r0 + pow2 64 * BD.bn_v #U64 #(i-1) r1); 
    Math.Lemmas.lemma_div_lt x (64 * i) 64;
    assert (x1 < pow2 (64 * i - 64));
    assert (x1 < pow2 (64 * (i - 1)));
    felem_to_list_lemma_rec_eval x1 (i-1);
    assert (BD.bn_v #U64 #(i-1) (Seq.seq_of_list l) == x1);
    assert (BD.bn_v #U64 #i (Seq.seq_of_list r) == x0 + pow2 64 * x1);
    assert (BD.bn_v #U64 #i (Seq.seq_of_list r) == x)
  )
  else (
    assert (felem_to_list_rec x i == []);
    assert (BD.bn_v #U64 #0 (Seq.seq_of_list []) == 0)
  )
#pop-options

val felem_to_list_lemma_eval: {| cp:S.curve_params |} -> x:S.felem ->
  Lemma (BD.bn_v (list_as_felem (felem_to_list x)) == x)

let felem_to_list_lemma_eval {| cp:S.curve_params |} x =
  assert (64 * v cp.bn_limbs >= cp.bits);
  Math.Lemmas.pow2_le_compat (64 * v cp.bn_limbs) cp.bits;
  assert (pow2 (64 * v cp.bn_limbs) >= pow2 cp.bits);
  assert (x < pow2 (64 * v cp.bn_limbs));
  felem_to_list_lemma_rec_eval x (v cp.bn_limbs)
  
//--------------------------------------------

val proj_point_to_list_sub {| cp:S.curve_params |} : p:S.proj_point -> Lemma
 (let (px, py, pz) = p in
  let pxM = SM.to_mont px in
  let pyM = SM.to_mont py in
  let pzM = SM.to_mont pz in
  let px_list = felem_to_list pxM in
  let py_list = felem_to_list pyM in
  let pz_list = felem_to_list pzM in
  let p_list = FL.(px_list @ py_list @ pz_list) in

  let p_lseq = Seq.seq_of_list p_list <: lseq uint64 (3 * v cp.bn_limbs) in
  let px_lseq = Seq.seq_of_list px_list <: lseq uint64 (v cp.bn_limbs) in
  let py_lseq = Seq.seq_of_list py_list <: lseq uint64 (v cp.bn_limbs) in
  let pz_lseq = Seq.seq_of_list pz_list <: lseq uint64 (v cp.bn_limbs) in
  sub p_lseq 0 (v cp.bn_limbs) == px_lseq /\
  sub p_lseq (v cp.bn_limbs) (v cp.bn_limbs) == py_lseq /\
  sub p_lseq (2 * v cp.bn_limbs) (v cp.bn_limbs) == pz_lseq)

let proj_point_to_list_sub {| cp:S.curve_params |} p =
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


val proj_point_to_list_fits {| cp:S.curve_params |} : p:S.proj_point ->
  Lemma (point_inv_list (proj_point_to_list p))

let proj_point_to_list_fits {| cp:S.curve_params |} p =
  let (px, py, pz) = p in
  let pxM = SM.to_mont px in
  let pyM = SM.to_mont py in
  let pzM = SM.to_mont pz in

  proj_point_to_list_sub p;
  felem_to_list_lemma_eval pxM;
  felem_to_list_lemma_eval pyM;
  felem_to_list_lemma_eval pzM


val proj_point_to_list_eval: {| cp:S.curve_params |} -> p:S.proj_point ->
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
