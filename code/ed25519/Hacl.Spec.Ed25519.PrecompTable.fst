module Hacl.Spec.Ed25519.PrecompTable

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

module F51 = Hacl.Impl.Ed25519.Field51
module SF51 = Hacl.Spec.Curve25519.Field51.Definition

module S = Spec.Ed25519
module SC = Spec.Curve25519
module FL = FStar.List.Tot
module SPT = Hacl.Spec.PrecompBaseTable

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"


let create5_lseq (x0 x1 x2 x3 x4:uint64) : lseq uint64 5 =
  let l = [x0; x1; x2; x3; x4] in
  assert_norm (FL.length l = 5);
  Seq.seq_of_list l


val create5_lemma (x0 x1 x2 x3 x4:uint64) :
  Lemma (let s = create5_lseq x0 x1 x2 x3 x4 in
    s.[0] == x0 /\ s.[1] == x1 /\ s.[2] == x2 /\ s.[3] == x3 /\ s.[4] == x4)
let create5_lemma x0 x1 x2 x3 x4 =
  Seq.elim_of_list [x0; x1; x2; x3; x4]

//-----------------------------------

noextract
let list_as_felem5 (f:felem_list) : SF51.felem5 =
  let x = Seq.seq_of_list f <: lseq uint64 5 in
  F51.lseq_as_felem x


val felem_to_list_index_lemma: x:SC.elem ->
  Lemma (let (f0, f1, f2, f3, f4) = list_as_felem5 (felem_to_list x) in
    let x0 = x % pow51 in
    let x1 = x / pow51 % pow51 in
    let x2 = x / pow102 % pow51 in
    let x3 = x / pow153 % pow51 in
    let x4 = x / pow204 in
    v f0 == x0 /\ v f1 == x1 /\ v f2 == x2 /\ v f3 == x3 /\ v f4 == x4)

let felem_to_list_index_lemma x =
  let x0 = x % pow51 in
  let x1 = x / pow51 % pow51 in
  let x2 = x / pow102 % pow51 in
  let x3 = x / pow153 % pow51 in
  let x4 = x / pow204 in
  let f = felem_to_list x in

  let (f0, f1, f2, f3, f4) = list_as_felem5 f in
  Math.Lemmas.lemma_div_lt_nat x 255 204;
  create5_lemma (u64 x0) (u64 x1) (u64 x2) (u64 x3) (u64 x4);
  assert (v f0 == x0 /\ v f1 == x1 /\ v f2 == x2 /\ v f3 == x3 /\ v f4 == x4)


val felem_to_list_lemma_fits: x:SC.elem ->
  Lemma (SF51.felem_fits5 (list_as_felem5 (felem_to_list x)) (1, 1, 1, 1, 1))

let felem_to_list_lemma_fits x =
  felem_to_list_index_lemma x;
  let x0 = x % pow51 in
  let x1 = x / pow51 % pow51 in
  let x2 = x / pow102 % pow51 in
  let x3 = x / pow153 % pow51 in
  let x4 = x / pow204 in
  assert (SF51.felem_fits1 (u64 x0) 1);
  assert (SF51.felem_fits1 (u64 x1) 1);
  assert (SF51.felem_fits1 (u64 x2) 1);
  assert (SF51.felem_fits1 (u64 x3) 1);
  Math.Lemmas.lemma_div_lt_nat x 255 204;
  assert (SF51.felem_fits1 (u64 x4) 1)


val lemma_mod_pow2_sub: x:nat -> a:nat -> b:nat ->
  Lemma (x / pow2 a % pow2 b * pow2 a == x % pow2 (a + b) - x % pow2 a)

let lemma_mod_pow2_sub x a b =
  calc (==) {
    x / pow2 a % pow2 b * pow2 a;
    (==) { Math.Lemmas.pow2_modulo_division_lemma_1 x a (a + b) }
    x % pow2 (a + b) / pow2 a * pow2 a;
    (==) { Math.Lemmas.euclidean_division_definition (x % pow2 (a + b)) (pow2 a) }
    x % pow2 (a + b) - x % pow2 (a + b) % pow2 a;
    (==) { Math.Lemmas.pow2_modulo_modulo_lemma_1 x a (a + b) }
    x % pow2 (a + b) - x % pow2 a;
  }


val felem_to_list_lemma_eval: x:SC.elem ->
  Lemma (SF51.as_nat5 (list_as_felem5 (felem_to_list x)) == x)

let felem_to_list_lemma_eval x =
  felem_to_list_index_lemma x;
  let x0 = x % pow51 in
  let x1 = x / pow51 % pow51 in
  let x2 = x / pow102 % pow51 in
  let x3 = x / pow153 % pow51 in
  let x4 = x / pow204 in
  let (f0, f1, f2, f3, f4) = list_as_felem5 (felem_to_list x) in
  Math.Lemmas.lemma_div_lt_nat x 255 204;
  let nat_x = SF51.as_nat5 (f0, f1, f2, f3, f4) in
  assert (nat_x == x0 + x1 * pow51 + x2 * pow102 + x3 * pow153 + x4 * pow204);
  calc (==) {
    x0 + x1 * pow51 + x2 * pow102 + x3 * pow153 + x4 * pow204;
    (==) { }
    x0 + x1 * pow51 + x2 * pow102 + (x / pow153 % pow51) * pow153 + x / pow204 * pow204;
    (==) { lemma_mod_pow2_sub x 153 51 }
    x0 + x1 * pow51 + x2 * pow102 + x % pow204 - x % pow153 + x / pow204 * pow204;
    (==) { Math.Lemmas.euclidean_division_definition x pow204 }
    x0 + x1 * pow51 + (x / pow102 % pow51) * pow102 - x % pow153 + x;
    (==) { lemma_mod_pow2_sub x 102 51 }
    x0 + (x / pow51 % pow51) * pow51 - x % pow102 + x;
    (==) { lemma_mod_pow2_sub x 51 51 }
    x;
  }

//--------------------------------------------

val ext_point_to_list_sub: p:S.ext_point -> Lemma
 (let (px, py, pz, pt) = p in
  let px_list = felem_to_list px in
  let py_list = felem_to_list py in
  let pz_list = felem_to_list pz in
  let pt_list = felem_to_list pt in
  let p_list = FL.(px_list @ py_list @ pz_list @ pt_list) in

  let p_lseq = Seq.seq_of_list p_list <: lseq uint64 20 in
  let px_lseq = Seq.seq_of_list px_list <: lseq uint64 5 in
  let py_lseq = Seq.seq_of_list py_list <: lseq uint64 5 in
  let pz_lseq = Seq.seq_of_list pz_list <: lseq uint64 5 in
  let pt_lseq = Seq.seq_of_list pt_list <: lseq uint64 5 in
  sub p_lseq 0 5 == px_lseq /\
  sub p_lseq 5 5 == py_lseq /\
  sub p_lseq 10 5 == pz_lseq /\
  sub p_lseq 15 5 == pt_lseq)

let ext_point_to_list_sub p =
  let (px, py, pz, pt) = p in
  let px_list = felem_to_list px in
  let py_list = felem_to_list py in
  let pz_list = felem_to_list pz in
  let pt_list = felem_to_list pt in

  FL.append_assoc px_list py_list pz_list;
  assert (FL.(px_list @ py_list @ pz_list) ==
    FL.append (FL.append px_list py_list) pz_list);

  calc (==) { // ((a * b) * c) * d == a * (b * (c * d))
    FL.append (FL.append (FL.append px_list py_list) pz_list) pt_list;
    (==) { FL.append_assoc FL.(px_list @ py_list) pz_list pt_list }
    FL.append (FL.append px_list py_list) (FL.append pz_list pt_list);
    (==) { FL.append_assoc px_list py_list (FL.append pz_list pt_list) }
    FL.(px_list @ py_list @ pz_list @ pt_list);
  };

  SPT.seq_of_list_append_lemma px_list py_list;
  SPT.seq_of_list_append_lemma FL.(px_list @ py_list) pz_list;
  SPT.seq_of_list_append_lemma FL.(px_list @ py_list @ pz_list) pt_list


val ext_point_to_list_eval: p:S.ext_point ->
  Lemma (point_eval_list (ext_point_to_list p) == p)

let ext_point_to_list_eval p =
  let (px, py, pz, pt) = p in
  ext_point_to_list_sub p;
  felem_to_list_lemma_eval px;
  felem_to_list_lemma_eval py;
  felem_to_list_lemma_eval pz;
  felem_to_list_lemma_eval pt;
  Math.Lemmas.small_mod px SC.prime;
  Math.Lemmas.small_mod py SC.prime;
  Math.Lemmas.small_mod pz SC.prime;
  Math.Lemmas.small_mod pt SC.prime


let ext_point_to_list_lemma p =
  ext_point_to_list_eval p;
  let (px, py, pz, pt) = p in
  ext_point_to_list_sub p;
  felem_to_list_lemma_fits px;
  felem_to_list_lemma_fits py;
  felem_to_list_lemma_fits pz;
  felem_to_list_lemma_fits pt
