module Hacl.Spec.K256.PrecompTable.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.K256.Field52.Definitions
open Hacl.Impl.K256.Point

module S = Spec.K256
module SL = Spec.K256.Lemmas

module LE = Lib.Exponentiation
module FL = FStar.List.Tot

open Hacl.Spec.K256.PrecompTable

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

//----------------------------------------------

#push-options "--fuel 2"
val list_append_index1: #a:Type -> x:list a -> y:list a -> i:nat{i < FL.length x} ->
  Lemma (ensures (FL.(index (x @ y)) i == FL.index x i)) (decreases (FL.length x))

let rec list_append_index1 #a x y i =
  match x with
  | [] -> ()
  | hd::tl -> if i = 0 then () else list_append_index1 tl y (i - 1)


val list_append_index2: #a:Type -> x:list a -> y:list a -> i:nat{FL.length x <= i /\ i < FL.length x + FL.length y} ->
  Lemma (ensures (FL.(index (x @ y)) i == FL.index y (i - FL.length x))) (decreases (FL.length x))

let rec list_append_index2 #a x y i =
  match x with
  | [] -> ()
  | hd::tl -> list_append_index2 tl y (i - 1)
#pop-options


val list_append_index: #a:Type -> x:list a -> y:list a -> i:nat{i < FL.length x + FL.length y} ->
  Lemma (FL.(index (x @ y)) i ==
    (if i < FL.length x then FL.index x i else FL.index y (i - FL.length x)))

let list_append_index #a x y i =
  if i < FL.length x then list_append_index1 x y i else list_append_index2 x y i


val seq_of_list_append_lemma: #a:Type -> x:list a -> y:list a ->
  Lemma (let xy_lseq = Seq.seq_of_list FL.(x @ y) in
    Seq.slice xy_lseq 0 (FL.length x) == Seq.seq_of_list x /\
    Seq.slice xy_lseq (FL.length x) (FL.length x + FL.length y) == Seq.seq_of_list y)

let seq_of_list_append_lemma #a x y =
  let xy = FL.(x @ y) in
  let x_lseq = Seq.seq_of_list x in
  let y_lseq = Seq.seq_of_list y in
  let xy_lseq = Seq.seq_of_list xy in
  let x_len = FL.length x in
  let y_len = FL.length y in

  let lemma_x_lseq (i:nat{i < x_len}) : Lemma (Seq.index xy_lseq i == Seq.index x_lseq i) =
    list_append_index x y i in

  FStar.Classical.forall_intro lemma_x_lseq;
  Seq.lemma_eq_intro (Seq.slice xy_lseq 0 x_len) x_lseq;
  assert (Seq.slice xy_lseq 0 x_len == x_lseq);

  let lemma_y_lseq (i:nat{i < y_len}) :
    Lemma (Seq.index xy_lseq (x_len + i) == Seq.index y_lseq i) =
    list_append_index x y (x_len + i) in

  FStar.Classical.forall_intro lemma_y_lseq;
  Seq.lemma_eq_intro (Seq.slice xy_lseq x_len (x_len + y_len)) y_lseq;
  assert (Seq.slice xy_lseq x_len (x_len + y_len) == y_lseq)

//-----------------------------------

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

//----------------------------------------------

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
  seq_of_list_append_lemma px_list py_list;
  seq_of_list_append_lemma FL.(px_list @ py_list) pz_list


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

//--------------------------------------------

#push-options "--fuel 1"
val eq_precomp_basepoint_table_list_rec0 (n:nat) (acc:g_i_acc_t 0) :
  Lemma (precomp_basepoint_table_list_rec 0 acc == acc)
let eq_precomp_basepoint_table_list_rec0 n acc = ()

val unroll_precomp_basepoint_table_list_rec (n:pos) (acc:g_i_acc_t 0) :
  Lemma (precomp_basepoint_table_list_rec n acc ==
    precomp_basepoint_table_f (n - 1) (precomp_basepoint_table_list_rec (n - 1) acc))
let unroll_precomp_basepoint_table_list_rec n acc = ()
#pop-options

//--------------------------------------------

let pow_base_point (k:nat) =
  LE.pow S.mk_k256_comm_monoid (S.to_aff_point S.g) k

unfold
let precomp_table_acc_inv
  (table_len:nat{table_len * 15 <= max_size_t})
  (table:lseq uint64 (table_len * 15))
  (j:nat{j < table_len})
=
  Math.Lemmas.lemma_mult_lt_right 15 j table_len;
  Math.Lemmas.lemma_mult_le_right 15 (j + 1) table_len;
  let bj = sub table (j * 15) 15 in
  point_inv_lseq bj /\ S.to_aff_point (point_eval_lseq bj) == pow_base_point j


val precomp_table_acc_inv0: unit ->
  Lemma (precomp_table_acc_inv 1 (Seq.seq_of_list (proj_point_to_list S.point_at_inf)) 0)

let precomp_table_acc_inv0 () =
  let table = Seq.seq_of_list (proj_point_to_list S.point_at_inf) <: lseq uint64 15 in
  let bj = sub table 0 15 in
  assert (bj == table);

  proj_point_to_list_lemma S.point_at_inf;
  assert (point_inv_lseq bj);
  assert (point_eval_lseq bj == S.point_at_inf);

  LE.lemma_pow0 S.mk_k256_comm_monoid (S.to_aff_point S.g);
  assert (pow_base_point 0 == S.aff_point_at_inf);
  SL.to_aff_point_at_infinity_lemma ();
  assert (S.to_aff_point S.point_at_inf == pow_base_point 0)


inline_for_extraction noextract
let max_table_len_t = n:nat{(n + 1) * 15 <= max_size_t}


unfold
let precomp_basepoint_table_inv (n:max_table_len_t) ((g_i, acc_i):g_i_acc_t n) =
  S.to_aff_point g_i == pow_base_point (n + 1) /\
  (forall (i:nat{i < n + 1}). precomp_table_acc_inv (n + 1) (Seq.seq_of_list acc_i) i)


val precomp_basepoint_table_step_g_i:
  n:max_table_len_t{0 < n} -> g_i_acc1:g_i_acc_t (n - 1) -> Lemma
  (requires precomp_basepoint_table_inv (n - 1) g_i_acc1)
  (ensures (let (g_i, acc_i) = precomp_basepoint_table_f (n - 1) g_i_acc1 in
    S.to_aff_point g_i == pow_base_point (n + 1)))

let precomp_basepoint_table_step_g_i n g_i_acc1 =
  let (g_i1, acc_i1) = g_i_acc1 in
  let (g_i, acc_i) = precomp_basepoint_table_f (n - 1) (g_i1, acc_i1) in
  assert (g_i == Spec.K256.point_add g_i1 S.g);

  assert (precomp_basepoint_table_inv (n - 1) g_i_acc1);
  assert (S.to_aff_point g_i1 == pow_base_point n);
  calc (==) {
    S.to_aff_point g_i;
    (==) { }
    S.to_aff_point (Spec.K256.point_add g_i1 S.g);
    (==) { SL.to_aff_point_add_lemma g_i1 S.g }
    Spec.K256.aff_point_add (S.to_aff_point g_i1) (S.to_aff_point S.g);
    (==) { }
    Spec.K256.aff_point_add (pow_base_point n) (S.to_aff_point S.g);
    (==) { SL.aff_point_add_comm_lemma (pow_base_point n) (S.to_aff_point S.g) }
    Spec.K256.aff_point_add (S.to_aff_point S.g) (pow_base_point n);
    (==) { LE.lemma_pow_unfold S.mk_k256_comm_monoid (S.to_aff_point S.g) (n + 1) }
    pow_base_point (n + 1);
  };

  assert (S.to_aff_point g_i == pow_base_point (n + 1))


val precomp_basepoint_table_list_lemma_step:
  n:max_table_len_t{0 < n} -> g_i_acc1:g_i_acc_t (n - 1) -> Lemma
  (requires precomp_basepoint_table_inv (n - 1) g_i_acc1)
  (ensures (let (g_i, acc_i) = precomp_basepoint_table_f (n - 1) g_i_acc1 in
    precomp_basepoint_table_inv n (g_i, acc_i)))

let precomp_basepoint_table_list_lemma_step n g_i_acc1 =
  let (g_i1, acc_i1) = g_i_acc1 in
  let (g_i, acc_i) = precomp_basepoint_table_f (n - 1) g_i_acc1 in
  assert (g_i == Spec.K256.point_add g_i1 S.g);
  assert (acc_i == FL.(acc_i1 @ proj_point_to_list g_i1));

  assert (precomp_basepoint_table_inv (n - 1) g_i_acc1);
  // assert (S.to_aff_point g_i1 == pow_base_point n);
  precomp_basepoint_table_step_g_i n g_i_acc1;
  assert (S.to_aff_point g_i == pow_base_point (n + 1));

  let g_i1_list = proj_point_to_list g_i1 in
  let acc_i_lseq = Seq.seq_of_list acc_i in
  let acc_i1_lseq = Seq.seq_of_list acc_i1 in
  let g_i1_lseq = Seq.seq_of_list g_i1_list in

  let acc_i1_len = FL.length acc_i1 in
  let g_i1_len = FL.length g_i1_list in

  seq_of_list_append_lemma acc_i1 g_i1_list;

  assert (Seq.slice acc_i_lseq 0 acc_i1_len == acc_i1_lseq);
  assert (Seq.slice acc_i_lseq acc_i1_len (acc_i1_len + g_i1_len) == g_i1_lseq);
  assert (forall (i:nat{i < n}). precomp_table_acc_inv n acc_i1_lseq i);
  proj_point_to_list_lemma g_i1;
  assert (precomp_table_acc_inv (n + 1) acc_i_lseq n);
  assert (forall (i:nat{i < n}). precomp_table_acc_inv (n + 1) acc_i_lseq i);

  let aux (i:nat{i < n + 1}) : Lemma (precomp_table_acc_inv (n + 1) acc_i_lseq i) = () in
  Classical.forall_intro aux;
  assert (forall (i:nat{i < n + 1}). precomp_table_acc_inv (n + 1) acc_i_lseq i)


val precomp_basepoint_table_list_lemma: n:max_table_len_t -> Lemma
 (let acc0 = (Spec.K256.g, proj_point_to_list S.point_at_inf) in
  let g_i, acc_i = precomp_basepoint_table_list_rec n acc0 in
  precomp_basepoint_table_inv n (g_i, acc_i))

let rec precomp_basepoint_table_list_lemma n =
  let acc0 = (Spec.K256.g, proj_point_to_list S.point_at_inf) in
  let g_i, acc_i = precomp_basepoint_table_list_rec n acc0 in

  if n = 0 then begin
    eq_precomp_basepoint_table_list_rec0 n acc0;
    assert (g_i == Spec.K256.g /\ acc_i == proj_point_to_list S.point_at_inf);
    LE.lemma_pow1 S.mk_k256_comm_monoid (S.to_aff_point S.g);
    assert (S.to_aff_point g_i == pow_base_point 1);
    precomp_table_acc_inv0 ();
    assert (precomp_table_acc_inv 1 (Seq.seq_of_list acc_i) 0) end
  else begin
    let (g_i1, acc_i1) = precomp_basepoint_table_list_rec (n - 1) acc0 in
    let (g_i2, acc_i2) = precomp_basepoint_table_f (n - 1) (g_i1, acc_i1) in
    unroll_precomp_basepoint_table_list_rec n acc0;
    //assert (g_i2 == g_i /\ acc_i2 == acc_i);
    precomp_basepoint_table_list_lemma (n - 1);
    // assert (precomp_basepoint_table_inv (n - 1) (g_i1, acc_i1));
    precomp_basepoint_table_list_lemma_step n (g_i1, acc_i1);
    assert (precomp_basepoint_table_inv n (g_i, acc_i)) end


val precomp_basepoint_table_lemma: unit ->
  Lemma (forall (i:nat{i < 16}). precomp_table_acc_inv 16 precomp_basepoint_table_lseq i)

let precomp_basepoint_table_lemma () =
  precomp_basepoint_table_list_lemma 15;
  normalize_term_spec precomp_basepoint_table_list_aux
