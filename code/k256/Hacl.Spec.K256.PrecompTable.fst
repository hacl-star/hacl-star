module Hacl.Spec.K256.PrecompTable

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.K256.Field52.Definitions
open Hacl.Impl.K256.Point

module S = Spec.K256
module FL = FStar.List.Tot
module SPT = Hacl.Spec.PrecompBaseTable

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

unfold
let create5 (x0 x1 x2 x3 x4:uint64) : list uint64 = [x0; x1; x2; x3; x4]

inline_for_extraction noextract
let felem_list = x:list uint64{FL.length x == 5}
inline_for_extraction noextract
let point_list = x:list uint64{FL.length x == 15}

inline_for_extraction noextract
let felem_to_list (x:S.felem) : felem_list =
  [@inline_let] let x0 = x % pow52 in
  [@inline_let] let x1 = x / pow52 % pow52 in
  [@inline_let] let x2 = x / pow104 % pow52 in
  [@inline_let] let x3 = x / pow156 % pow52 in
  [@inline_let] let x4 = x / pow208 in
  [@inline_let] let r = create5 (u64 x0) (u64 x1) (u64 x2) (u64 x3) (u64 x4) in
  assert_norm (FL.length r = 5);
  r

inline_for_extraction noextract
let proj_point_to_list (p:S.proj_point) : point_list =
  [@inline_let] let (px, py, pz) = p in
  FL.(felem_to_list px @ felem_to_list py @ felem_to_list pz)

//----------------------------------------------

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
let list_as_felem5 (f:felem_list) : felem5 =
  let x = Seq.seq_of_list f <: lseq uint64 5 in
  as_felem5_lseq x


val felem_to_list_index_lemma: x:S.felem ->
  Lemma (let (f0, f1, f2, f3, f4) = list_as_felem5 (felem_to_list x) in
    let x0 = x % pow52 in
    let x1 = x / pow52 % pow52 in
    let x2 = x / pow104 % pow52 in
    let x3 = x / pow156 % pow52 in
    let x4 = x / pow208 in
    v f0 == x0 /\ v f1 == x1 /\ v f2 == x2 /\ v f3 == x3 /\ v f4 == x4)

let felem_to_list_index_lemma x =
  let x0 = x % pow52 in
  let x1 = x / pow52 % pow52 in
  let x2 = x / pow104 % pow52 in
  let x3 = x / pow156 % pow52 in
  let x4 = x / pow208 in
  let f = felem_to_list x in

  let (f0, f1, f2, f3, f4) = list_as_felem5 f in
  create5_lemma (u64 x0) (u64 x1) (u64 x2) (u64 x3) (u64 x4);
  assert (v f0 == x0 /\ v f1 == x1 /\ v f2 == x2 /\ v f3 == x3 /\ v f4 == x4)


val felem_to_list_lemma_fits: x:S.felem ->
  Lemma (felem_fits5 (list_as_felem5 (felem_to_list x)) (1, 1, 1, 1, 1))

let felem_to_list_lemma_fits x =
  felem_to_list_index_lemma x;
  let x0 = x % pow52 in
  let x1 = x / pow52 % pow52 in
  let x2 = x / pow104 % pow52 in
  let x3 = x / pow156 % pow52 in
  let x4 = x / pow208 in
  assert (felem_fits1 (u64 x0) 1);
  assert (felem_fits1 (u64 x1) 1);
  assert (felem_fits1 (u64 x2) 1);
  assert (felem_fits1 (u64 x3) 1);
  Math.Lemmas.lemma_div_lt_nat x 256 208;
  assert (felem_fits_last1 (u64 x4) 1)


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


val felem_to_list_lemma_eval: x:S.felem ->
  Lemma (as_nat5 (list_as_felem5 (felem_to_list x)) == x)

let felem_to_list_lemma_eval x =
  felem_to_list_index_lemma x;
  let x0 = x % pow52 in
  let x1 = x / pow52 % pow52 in
  let x2 = x / pow104 % pow52 in
  let x3 = x / pow156 % pow52 in
  let x4 = x / pow208 in
  let (f0, f1, f2, f3, f4) = list_as_felem5 (felem_to_list x) in
  let nat_x = as_nat5 (f0, f1, f2, f3, f4) in
  assert (nat_x == x0 + x1 * pow52 + x2 * pow104 + x3 * pow156 + x4 * pow208);
  calc (==) {
    x0 + x1 * pow52 + x2 * pow104 + x3 * pow156 + x4 * pow208;
    (==) { }
    x0 + x1 * pow52 + x2 * pow104 + (x / pow156 % pow52) * pow156 + x / pow208 * pow208;
    (==) { lemma_mod_pow2_sub x 156 52 }
    x0 + x1 * pow52 + x2 * pow104 + x % pow208 - x % pow156 + x / pow208 * pow208;
    (==) { Math.Lemmas.euclidean_division_definition x pow208 }
    x0 + x1 * pow52 + (x / pow104 % pow52) * pow104 - x % pow156 + x;
    (==) { lemma_mod_pow2_sub x 104 52 }
    x0 + (x / pow52 % pow52) * pow52 - x % pow104 + x;
    (==) { lemma_mod_pow2_sub x 52 52 }
    x;
  }

//--------------------------------------------

inline_for_extraction noextract
let point_inv_list (p:point_list) =
  let x = Seq.seq_of_list p <: lseq uint64 15 in
  point_inv_lseq x

noextract
let point_eval_list (p:point_list) : GTot S.proj_point =
  let x = Seq.seq_of_list p <: lseq uint64 15 in
  point_eval_lseq x


val proj_point_to_list_sub: p:S.proj_point -> Lemma
 (let (px, py, pz) = p in
  let px_list = felem_to_list px in
  let py_list = felem_to_list py in
  let pz_list = felem_to_list pz in
  let p_list = FL.(px_list @ py_list @ pz_list) in

  let p_lseq = Seq.seq_of_list p_list <: lseq uint64 15 in
  let px_lseq = Seq.seq_of_list px_list <: lseq uint64 5 in
  let py_lseq = Seq.seq_of_list py_list <: lseq uint64 5 in
  let pz_lseq = Seq.seq_of_list pz_list <: lseq uint64 5 in
  sub p_lseq 0 5 == px_lseq /\
  sub p_lseq 5 5 == py_lseq /\
  sub p_lseq 10 5 == pz_lseq)

let proj_point_to_list_sub p =
  let (px, py, pz) = p in
  let px_list = felem_to_list px in
  let py_list = felem_to_list py in
  let pz_list = felem_to_list pz in

  FL.append_assoc px_list py_list pz_list;
  SPT.seq_of_list_append_lemma px_list py_list;
  SPT.seq_of_list_append_lemma FL.(px_list @ py_list) pz_list


val proj_point_to_list_fits: p:S.proj_point ->
  Lemma (point_inv_list (proj_point_to_list p))

let proj_point_to_list_fits p =
  let (px, py, pz) = p in
  proj_point_to_list_sub p;
  felem_to_list_lemma_fits px;
  felem_to_list_lemma_fits py;
  felem_to_list_lemma_fits pz


val proj_point_to_list_eval: p:S.proj_point ->
  Lemma (point_eval_list (proj_point_to_list p) == p)

let proj_point_to_list_eval p =
  let (px, py, pz) = p in
  proj_point_to_list_sub p;
  felem_to_list_lemma_eval px;
  felem_to_list_lemma_eval py;
  felem_to_list_lemma_eval pz;
  Math.Lemmas.small_mod px S.prime;
  Math.Lemmas.small_mod py S.prime;
  Math.Lemmas.small_mod pz S.prime


val proj_point_to_list_lemma: p:S.proj_point ->
  Lemma (point_inv_list (proj_point_to_list p) /\ point_eval_list (proj_point_to_list p) == p)

let proj_point_to_list_lemma p =
  proj_point_to_list_fits p;
  proj_point_to_list_eval p
