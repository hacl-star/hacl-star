module Hacl.Spec.Exponentiation

open FStar.Mul
open Lib.IntTypes

module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence
module Loops = Lib.LoopCombinators

module S = Lib.Exponentiation
module SB = Hacl.Spec.Bignum.Base

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"


val precomp_table_inv_lemma_j:
    #a_t:inttype_a
  -> len:size_nat{len > 0}
  -> ctx_len:size_nat
  -> k:to_comm_monoid a_t len ctx_len
  -> a:LSeq.lseq (uint_t a_t SEC) len
  -> table_len:size_nat{table_len * len <= max_size_t}
  -> table1:LSeq.lseq (uint_t a_t SEC) (table_len * len)
  -> table2:LSeq.lseq (uint_t a_t SEC) (table_len * len)
  -> i:nat{i <= table_len}
  -> j:nat{j < i} -> Lemma
  (requires
    LSeq.sub table1 0 (i * len) == LSeq.sub table2 0 (i * len) /\
    precomp_table_inv len ctx_len k a table_len table1 j)
  (ensures
    precomp_table_inv len ctx_len k a table_len table2 j)

let precomp_table_inv_lemma_j #a_t len ctx_len k a table_len table1 table2 i j =
  assert (precomp_table_inv len ctx_len k a table_len table1 j);
  Math.Lemmas.lemma_mult_le_right len (j + 1) table_len;
  let bj1 = LSeq.sub table1 (j * len) len in
  let bj2 = LSeq.sub table2 (j * len) len in

  let aux (l:nat{l < len}) : Lemma (LSeq.index bj1 l == LSeq.index bj2 l) =
    Seq.lemma_index_slice table1 (j * len) (j * len + len) l;
    //assert (LSeq.index bj1 l == LSeq.index table1 (j * len + l));
    Seq.lemma_index_slice table2 (j * len) (j * len + len) l;
    //assert (LSeq.index bj2 l == LSeq.index table2 (j * len + l));
    Seq.lemma_index_slice table1 0 (i * len) (j * len + l);
    Seq.lemma_index_slice table2 0 (i * len) (j * len + l);
    //assert (LSeq.index table1 (j * len + l) == LSeq.index table2 (j * len + l));
    assert (LSeq.index bj1 l == LSeq.index bj2 l) in

  Classical.forall_intro aux;
  LSeq.eq_intro bj1 bj2;
  assert (precomp_table_inv len ctx_len k a table_len table2 j)


let precomp_table_inv_lemma #a_t len ctx_len k a table_len table1 table2 i =
  let aux (j:nat{j < i}) : Lemma (precomp_table_inv len ctx_len k a table_len table2 j) =
    assert (precomp_table_inv len ctx_len k a table_len table1 j);
    precomp_table_inv_lemma_j #a_t len ctx_len k a table_len table1 table2 i j;
    assert (precomp_table_inv len ctx_len k a table_len table2 j) in

  Classical.forall_intro aux



val table_select_consttime_f:
    #a_t:inttype_a
  -> len:size_nat{len > 0}
  -> table_len:size_nat{1 < table_len /\ table_len * len <= max_size_t}
  -> table:LSeq.lseq (uint_t a_t SEC) (table_len * len)
  -> i:uint_t a_t SEC{v i < table_len}
  -> j:size_nat{j < table_len - 1}
  -> acc:LSeq.lseq (uint_t a_t SEC) len ->
  LSeq.lseq (uint_t a_t SEC) len

let table_select_consttime_f #a_t len table_len table i j acc =
  let c = eq_mask i (SB.size_to_limb (size j +! 1ul)) in
  //assert (v c == (if v i = v j + 1 then ones_v a_t else 0));

  Math.Lemmas.lemma_mult_le_right len (j + 2) table_len;
  let res_j = LSeq.sub table ((j + 1) * len) len in
  let acc = LSeq.map2 (SB.mask_select c) res_j acc in
  acc


let table_select_consttime #a_t len table_len table i =
  let res = LSeq.sub table 0 len in
  Loops.repeati (table_len - 1) (table_select_consttime_f #a_t len table_len table i) res


val table_select_consttime_f_lemma:
    #a_t:inttype_a
  -> len:size_nat{len > 0}
  -> table_len:size_nat{1 < table_len /\ table_len * len <= max_size_t}
  -> table:LSeq.lseq (uint_t a_t SEC) (table_len * len)
  -> i:uint_t a_t SEC{v i < table_len}
  -> j:size_nat{j < table_len - 1}
  -> acc:LSeq.lseq (uint_t a_t SEC) len ->
  Lemma (
    let res = table_select_consttime_f len table_len table i j acc in
    Math.Lemmas.lemma_mult_le_right len (j + 2) table_len;
    let res_j = LSeq.sub table ((j + 1) * len) len in
    res == (if v i = j + 1 then res_j else acc))

let table_select_consttime_f_lemma #a_t len table_len table i j acc =
  let c = eq_mask i (SB.size_to_limb (size (j + 1))) in
  assert (v c == (if v i = j + 1 then ones_v a_t else 0));

  Math.Lemmas.lemma_mult_le_right len (j + 2) table_len;
  let res_j = LSeq.sub table ((j + 1) * len) len in
  let res = LSeq.map2 (SB.mask_select c) res_j acc in
  SB.lseq_mask_select_lemma res_j acc c


val table_select_consttime_loop_lemma:
    #a_t:inttype_a
  -> len:size_nat{len > 0}
  -> table_len:size_nat{1 < table_len /\ table_len * len <= max_size_t}
  -> table:LSeq.lseq (uint_t a_t SEC) (table_len * len)
  -> i:uint_t a_t SEC{v i < table_len} ->
  Pure (LSeq.lseq (uint_t a_t SEC) len)
  (requires True)
  (ensures  fun res ->
    let res0 = LSeq.sub table 0 len in
    Math.Lemmas.lemma_mult_le_right len (v i + 1) table_len;
    res == Loops.repeati (table_len - 1) (table_select_consttime_f len table_len table i) res0 /\
    res == LSeq.sub table (v i * len) len)

let table_select_consttime_loop_lemma #a_t len table_len table i =
  let f = table_select_consttime_f len table_len table i in
  let res0 = LSeq.sub table 0 len in
  Math.Lemmas.lemma_mult_le_right len (v i + 1) table_len;

  Loops.eq_repeati0 (table_len - 1) f res0;
  Loops.repeati_inductive (table_len - 1)
  (fun j priv ->
    priv == Loops.repeati j f res0 /\
    priv == (if j >= v i then LSeq.sub table (v i * len) len else res0))
  (fun j priv ->
    Loops.unfold_repeati (j + 1) f res0 j;
    let res = f j priv in
    table_select_consttime_f_lemma len table_len table i j priv;
    Math.Lemmas.lemma_mult_le_right len (j + 2) table_len;
    let res_j = LSeq.sub table ((j + 1) * len) len in
    assert (res == (if v i = j + 1 then res_j else priv));
    res) res0

let table_select_consttime_lemma #a_t len table_len table i =
  let _ = table_select_consttime_loop_lemma len table_len table i in ()
