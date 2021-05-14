module Hacl.Spec.PrecompTable

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

module BSeq = Lib.ByteSequence
module Loops = Lib.LoopCombinators

module SB = Hacl.Spec.Bignum.Base

open Hacl.Spec.Bignum.Definitions

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val table_select_f:
    #t:limb_t
  -> len:size_nat{len > 0}
  -> table_len:size_nat{1 < table_len /\ table_len * len <= max_size_t}
  -> table:lseq (uint_t t SEC) (table_len * len)
  -> i:uint_t t SEC{v i < table_len}
  -> j:size_nat{j < table_len - 1}
  -> acc:lseq (uint_t t SEC) len ->
  lseq (uint_t t SEC) len

let table_select_f #t len table_len table i j acc =
  let c = eq_mask i (SB.size_to_limb (size j +! 1ul)) in
  //assert (v c == (if v i = v j + 1 then ones_v a_t else 0));

  Math.Lemmas.lemma_mult_le_right len (j + 2) table_len;
  let res_j = sub table ((j + 1) * len) len in
  let acc = map2 (SB.mask_select c) res_j acc in
  acc


val table_select:
    #t:limb_t
  -> len:size_nat{len > 0}
  -> table_len:size_nat{1 < table_len /\ table_len * len <= max_size_t}
  -> table:lseq (uint_t t SEC) (table_len * len)
  -> i:uint_t t SEC{v i < table_len} ->
  lseq (uint_t t SEC) len

let table_select #a_t len table_len table i =
  let res = sub table 0 len in
  Loops.repeati (table_len - 1) (table_select_f #a_t len table_len table i) res



val table_select_f_lemma:
    #t:limb_t
  -> len:size_nat{len > 0}
  -> table_len:size_nat{1 < table_len /\ table_len * len <= max_size_t}
  -> table:lseq (uint_t t SEC) (table_len * len)
  -> i:uint_t t SEC{v i < table_len}
  -> j:size_nat{j < table_len - 1}
  -> acc:lseq (uint_t t SEC) len ->
  Lemma (
    let res = table_select_f len table_len table i j acc in
    Math.Lemmas.lemma_mult_le_right len (j + 2) table_len;
    let res_j = sub table ((j + 1) * len) len in
    res == (if v i = j + 1 then res_j else acc))

let table_select_f_lemma #t len table_len table i j acc =
  let c = eq_mask i (SB.size_to_limb (size (j + 1))) in
  assert (v c == (if v i = j + 1 then ones_v t else 0));

  Math.Lemmas.lemma_mult_le_right len (j + 2) table_len;
  let res_j = sub table ((j + 1) * len) len in
  let res = map2 (SB.mask_select c) res_j acc in
  SB.lseq_mask_select_lemma res_j acc c


val table_select_loop_lemma:
    #t:limb_t
  -> len:size_nat{len > 0}
  -> table_len:size_nat{1 < table_len /\ table_len * len <= max_size_t}
  -> table:lseq (uint_t t SEC) (table_len * len)
  -> i:uint_t t SEC{v i < table_len} ->
  Pure (lseq (uint_t t SEC) len)
  (requires True)
  (ensures  fun res ->
    let res0 = sub table 0 len in
    Math.Lemmas.lemma_mult_le_right len (v i + 1) table_len;
    res == Loops.repeati (table_len - 1) (table_select_f len table_len table i) res0 /\
    res == sub table (v i * len) len)

let table_select_loop_lemma #t len table_len table i =
  let f = table_select_f len table_len table i in
  let res0 = sub table 0 len in
  Math.Lemmas.lemma_mult_le_right len (v i + 1) table_len;

  Loops.eq_repeati0 (table_len - 1) f res0;
  Loops.repeati_inductive (table_len - 1)
  (fun j priv ->
    priv == Loops.repeati j f res0 /\
    priv == (if j >= v i then sub table (v i * len) len else res0))
  (fun j priv ->
    Loops.unfold_repeati (j + 1) f res0 j;
    let res = f j priv in
    table_select_f_lemma len table_len table i j priv;
    Math.Lemmas.lemma_mult_le_right len (j + 2) table_len;
    let res_j = sub table ((j + 1) * len) len in
    assert (res == (if v i = j + 1 then res_j else priv));
    res) res0


val table_select_lemma:
    #t:limb_t
  -> len:size_nat{len > 0}
  -> table_len:size_nat{1 < table_len /\ table_len * len <= max_size_t}
  -> table:lseq (uint_t t SEC) (table_len * len)
  -> i:uint_t t SEC{v i < table_len} ->
  Lemma (Math.Lemmas.lemma_mult_le_right len (v i + 1) table_len;
    table_select len table_len table i == sub table (v i * len) len)

let table_select_lemma #t len table_len table i =
  let _ = table_select_loop_lemma len table_len table i in ()
