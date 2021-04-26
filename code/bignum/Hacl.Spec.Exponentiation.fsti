module Hacl.Spec.Exponentiation

open FStar.Mul
open Lib.IntTypes

module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence
module Loops = Lib.LoopCombinators

module S = Lib.Exponentiation

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let inttype_a = t:inttype{t = U32 \/ t = U64}

inline_for_extraction noextract
class to_comm_monoid (a_t:inttype_a) (len:size_nat{len > 0}) (ctx_len:size_nat) = {
  a_spec: Type0;
  comm_monoid: S.comm_monoid a_spec;
  linv_ctx: LSeq.lseq (uint_t a_t SEC) ctx_len -> Type0;
  linv: LSeq.lseq (uint_t a_t SEC) len -> Type0;
  refl: x:LSeq.lseq (uint_t a_t SEC) len{linv x} -> GTot a_spec;
}


inline_for_extraction noextract
let precomp_table_inv
  (#a_t:inttype_a)
  (len:size_nat{len > 0})
  (ctx_len:size_nat)
  (k:to_comm_monoid a_t len ctx_len)
  (a:LSeq.lseq (uint_t a_t SEC) len)
  (table_len:size_nat{table_len * len <= max_size_t})
  (table:LSeq.lseq (uint_t a_t SEC) (table_len * len))
  (j:nat{j < table_len}) : Type0
 =
  Math.Lemmas.lemma_mult_le_right len (j + 1) table_len;
  let bj = LSeq.sub table (j * len) len in
  k.linv bj /\ k.linv a /\
  k.refl bj == S.pow k.comm_monoid (k.refl a) j


val precomp_table_inv_lemma:
    #a_t:inttype_a
  -> len:size_nat{len > 0}
  -> ctx_len:size_nat
  -> k:to_comm_monoid a_t len ctx_len
  -> a:LSeq.lseq (uint_t a_t SEC) len
  -> table_len:size_nat{table_len * len <= max_size_t}
  -> table1:LSeq.lseq (uint_t a_t SEC) (table_len * len)
  -> table2:LSeq.lseq (uint_t a_t SEC) (table_len * len)
  -> i:nat{i <= table_len} -> Lemma
  (requires
    LSeq.sub table1 0 (i * len) == LSeq.sub table2 0 (i * len) /\
    (forall (j:nat{j < i}). precomp_table_inv len ctx_len k a table_len table1 j))
  (ensures
    (forall (j:nat{j < i}). precomp_table_inv len ctx_len k a table_len table2 j))

//`consttime` doesn't mean anything at the spec level
val table_select_consttime:
    #a_t:inttype_a
  -> len:size_nat{len > 0}
  -> table_len:size_nat{1 < table_len /\ table_len * len <= max_size_t}
  -> table:LSeq.lseq (uint_t a_t SEC) (table_len * len)
  -> i:uint_t a_t SEC{v i < table_len} ->
  LSeq.lseq (uint_t a_t SEC) len


val table_select_consttime_lemma:
    #a_t:inttype_a
  -> len:size_nat{len > 0}
  -> table_len:size_nat{1 < table_len /\ table_len * len <= max_size_t}
  -> table:LSeq.lseq (uint_t a_t SEC) (table_len * len)
  -> i:uint_t a_t SEC{v i < table_len} ->
  Lemma (Math.Lemmas.lemma_mult_le_right len (v i + 1) table_len;
    table_select_consttime len table_len table i == LSeq.sub table (v i * len) len)
