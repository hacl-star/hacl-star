module Hacl.Spec.PrecompBaseTable

open FStar.Mul
open Lib.IntTypes

module FL = FStar.List.Tot
module LSeq = Lib.Sequence

module LE = Lib.Exponentiation
module SE = Spec.Exponentiation
module BE = Hacl.Impl.Exponentiation.Definitions

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

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

#push-options "--fuel 1"
val eq_precomp_base_table_list_rec0
  (#t:Type) (#a_t:BE.inttype_a) (#len:size_t{v len > 0}) (#ctx_len:size_t)
  (k:mk_precomp_base_table t a_t len ctx_len) (g:t)
  (n:nat) (acc:g_i_acc_t t a_t len ctx_len 0) :
  Lemma (precomp_base_table_list_rec k g 0 acc == acc)

let eq_precomp_base_table_list_rec0 #t #a_t #len #ctx_len k g n acc = ()

val unroll_precomp_base_table_list_rec
  (#t:Type) (#a_t:BE.inttype_a) (#len:size_t{v len > 0}) (#ctx_len:size_t)
  (k:mk_precomp_base_table t a_t len ctx_len) (g:t)
  (n:pos) (acc:g_i_acc_t t a_t len ctx_len 0) :
  Lemma (precomp_base_table_list_rec k g n acc ==
    precomp_base_table_f k g (n - 1) (precomp_base_table_list_rec k g (n - 1) acc))

let unroll_precomp_base_table_list_rec #t #a_t #len #ctx_len k g n acc = ()
#pop-options

//--------------------------------------------

val precomp_base_table_acc_inv0
  (#t:Type) (#a_t:BE.inttype_a) (#len:size_t{v len > 0}) (#ctx_len:size_t)
  (k:mk_precomp_base_table t a_t len ctx_len) (g:t) :
  Lemma (precomp_base_table_acc_inv k g 1 (Seq.seq_of_list (k.to_list (k.concr_ops.SE.one ()))) 0)

let precomp_base_table_acc_inv0 #t #a_t #len #ctx_len k g =
  let table = Seq.seq_of_list (k.to_list (k.concr_ops.SE.one ())) <:
    LSeq.lseq (uint_t a_t SEC) (v len) in
  let bj = LSeq.sub table 0 (v len) in
  assert (bj == table);

  assert (k.to_cm.BE.linv bj);
  k.lemma_refl (k.concr_ops.SE.one ());
  assert (k.to_cm.BE.refl (Seq.seq_of_list (k.to_list (k.concr_ops.SE.one ()))) ==
    k.concr_ops.SE.to.SE.refl (k.concr_ops.SE.one ()));
  assert (k.concr_ops.SE.to.SE.refl (k.concr_ops.SE.one ()) ==
    k.concr_ops.SE.to.SE.comm_monoid.LE.one);

  LE.lemma_pow0 k.concr_ops.SE.to.comm_monoid (k.concr_ops.SE.to.refl g)


let max_table_len_t (len:size_t) = n:nat{(n + 1) * v len <= max_size_t}

unfold
let precomp_base_table_inv
  (#t:Type) (#a_t:BE.inttype_a) (#len:size_t{v len > 0}) (#ctx_len:size_t)
  (k:mk_precomp_base_table t a_t len ctx_len) (g:t)
  (n:max_table_len_t len) ((g_i, acc_i):g_i_acc_t t a_t len ctx_len n) =
  k.concr_ops.SE.to.SE.refl g_i == pow_base k g (n + 1) /\
  (forall (i:nat{i < n + 1}). precomp_base_table_acc_inv k g (n + 1) (Seq.seq_of_list acc_i) i)


val precomp_base_table_step_g_i
  (#t:Type) (#a_t:BE.inttype_a) (#len:size_t{v len > 0}) (#ctx_len:size_t)
  (k:mk_precomp_base_table t a_t len ctx_len) (g:t)
  (n:max_table_len_t len{0 < n}) (g_i_acc1:g_i_acc_t t a_t len ctx_len (n - 1)) :
  Lemma
  (requires precomp_base_table_inv k g (n - 1) g_i_acc1)
  (ensures (let (g_i, acc_i) = precomp_base_table_f k g (n - 1) g_i_acc1 in
    k.concr_ops.SE.to.SE.refl g_i == pow_base k g (n + 1)))

let precomp_base_table_step_g_i #t #a_t #len #ctx_len k g n g_i_acc1 =
  let (g_i1, acc_i1) = g_i_acc1 in
  let (g_i, acc_i) = precomp_base_table_f k g (n - 1) (g_i1, acc_i1) in
  assert (g_i == k.concr_ops.SE.mul g_i1 g);

  assert (precomp_base_table_inv k g (n - 1) g_i_acc1);
  [@inline_let] let refl = k.concr_ops.SE.to.SE.refl in
  assert (k.concr_ops.SE.to.SE.refl g_i1 == pow_base k g n);
  calc (==) {
    refl g_i;
    (==) { }
    refl (k.concr_ops.SE.mul g_i1 g);
    (==) { }
    k.concr_ops.SE.to.SE.comm_monoid.LE.mul (refl g_i1) (refl g);
    (==) { }
    k.concr_ops.SE.to.SE.comm_monoid.LE.mul (pow_base k g n) (refl g);
    (==) { k.concr_ops.SE.to.SE.comm_monoid.LE.lemma_mul_comm (pow_base k g n) (refl g) }
    k.concr_ops.SE.to.SE.comm_monoid.LE.mul (refl g) (pow_base k g n);
    (==) { LE.lemma_pow_unfold k.concr_ops.SE.to.SE.comm_monoid (refl g) (n + 1) }
    pow_base k g (n + 1);
  };
  assert (refl g_i == pow_base k g (n + 1))


val precomp_base_table_list_lemma_step
  (#t:Type) (#a_t:BE.inttype_a) (#len:size_t{v len > 0}) (#ctx_len:size_t)
  (k:mk_precomp_base_table t a_t len ctx_len) (g:t)
  (n:max_table_len_t len{0 < n}) (g_i_acc1:g_i_acc_t t a_t len ctx_len (n - 1)) :
  Lemma
  (requires precomp_base_table_inv k g (n - 1) g_i_acc1)
  (ensures (let (g_i, acc_i) = precomp_base_table_f k g (n - 1) g_i_acc1 in
    precomp_base_table_inv k g n (g_i, acc_i)))

let precomp_base_table_list_lemma_step #t #a_t #len #ctx_len k g n g_i_acc1 =
  let (g_i1, acc_i1) = g_i_acc1 in
  let (g_i, acc_i) = precomp_base_table_f k g (n - 1) g_i_acc1 in
  assert (g_i == k.concr_ops.SE.mul g_i1 g);
  assert (acc_i == FL.(acc_i1 @ k.to_list g_i1));

  assert (precomp_base_table_inv k g (n - 1) g_i_acc1);
  precomp_base_table_step_g_i #t #a_t #len #ctx_len k g n g_i_acc1;
  [@inline_let] let refl = k.concr_ops.SE.to.SE.refl in
  assert (refl g_i == pow_base k g (n + 1));

  let g_i1_list = k.to_list g_i1 in
  let acc_i_lseq = Seq.seq_of_list acc_i in
  let acc_i1_lseq = Seq.seq_of_list acc_i1 in
  let g_i1_lseq = Seq.seq_of_list g_i1_list in

  let acc_i1_len = FL.length acc_i1 in
  let g_i1_len = FL.length g_i1_list in

  seq_of_list_append_lemma acc_i1 g_i1_list;

  assert (Seq.slice acc_i_lseq 0 acc_i1_len == acc_i1_lseq);
  assert (Seq.slice acc_i_lseq acc_i1_len (acc_i1_len + g_i1_len) == g_i1_lseq);
  assert (forall (i:nat{i < n}). precomp_base_table_acc_inv k g n acc_i1_lseq i);
  k.lemma_refl g_i1;
  assert (precomp_base_table_acc_inv k g (n + 1) acc_i_lseq n);
  assert (forall (i:nat{i < n}). precomp_base_table_acc_inv k g (n + 1) acc_i_lseq i);

  let aux (i:nat{i < n + 1}) : Lemma (precomp_base_table_acc_inv k g (n + 1) acc_i_lseq i) = () in
  Classical.forall_intro aux;
  assert (forall (i:nat{i < n + 1}). precomp_base_table_acc_inv k g (n + 1) acc_i_lseq i)


val precomp_base_table_list_lemma
  (#t:Type) (#a_t:BE.inttype_a) (#len:size_t{v len > 0}) (#ctx_len:size_t)
  (k:mk_precomp_base_table t a_t len ctx_len) (g:t)
  (n:max_table_len_t len) :
  Lemma (let acc0 = (g, k.to_list (k.concr_ops.SE.one ())) in
    let g_i, acc_i = precomp_base_table_list_rec k g n acc0 in
    precomp_base_table_inv k g n (g_i, acc_i))

let rec precomp_base_table_list_lemma #t #a_t #len #ctx_len k g n =
  let acc0 = (g, k.to_list (k.concr_ops.SE.one ())) in
  let g_i, acc_i = precomp_base_table_list_rec k g n acc0 in
  [@inline_let] let refl = k.concr_ops.SE.to.SE.refl in

  if n = 0 then begin
    eq_precomp_base_table_list_rec0 k g n acc0;
    assert (g_i == g /\ acc_i == k.to_list (k.concr_ops.SE.one ()));
    LE.lemma_pow1 k.concr_ops.SE.to.comm_monoid (k.concr_ops.SE.to.refl g);
    assert (refl g_i == pow_base k g 1);
    precomp_base_table_acc_inv0 k g;
    assert (precomp_base_table_acc_inv k g 1 (Seq.seq_of_list acc_i) 0) end
  else begin
    let (g_i1, acc_i1) = precomp_base_table_list_rec k g (n - 1) acc0 in
    let (g_i2, acc_i2) = precomp_base_table_f k g (n - 1) (g_i1, acc_i1) in
    unroll_precomp_base_table_list_rec k g n acc0;
    precomp_base_table_list_lemma k g (n - 1);
    precomp_base_table_list_lemma_step k g n (g_i1, acc_i1);
    assert (precomp_base_table_inv k g n (g_i, acc_i)) end


let precomp_base_table_lemma #t #a_t #len #ctx_len k g table_len table =
  precomp_base_table_list_lemma k g (table_len - 1)
