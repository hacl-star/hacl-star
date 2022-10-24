module Hacl.K256.PrecompTable

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

module LE = Lib.Exponentiation
module SE = Spec.Exponentiation
module BE = Hacl.Impl.Exponentiation.Definitions
module SPT = Hacl.Spec.PrecompBaseTable

module S = Spec.K256

open Hacl.Impl.K256.Point
include Hacl.Impl.K256.Group

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val proj_point_to_list: p:S.proj_point
  -> x:list uint64{FStar.List.Tot.length x = 15 /\
    mk_to_k256_comm_monoid.BE.linv (Seq.seq_of_list x)}

val lemma_refl: x:S.proj_point ->
  Lemma (S.mk_k256_concrete_ops.SE.to.SE.refl x ==
    mk_to_k256_comm_monoid.BE.refl (Seq.seq_of_list (proj_point_to_list x)))


inline_for_extraction noextract
let mk_k256_precomp_base_table: SPT.mk_precomp_base_table S.proj_point U64 15ul 0ul = {
  SPT.concr_ops = S.mk_k256_concrete_ops;
  SPT.to_cm = mk_to_k256_comm_monoid;
  SPT.to_list = proj_point_to_list;
  SPT.lemma_refl = lemma_refl;
}


inline_for_extraction noextract
let pow_base_point (k:nat) =
  LE.pow S.mk_k256_comm_monoid (S.to_aff_point S.g) k


unfold
let precomp_table_acc_inv
  (table_len:nat{table_len * 15 <= max_size_t})
  (table:LSeq.lseq uint64 (table_len * 15))
  (j:nat{j < table_len})
=
  Math.Lemmas.lemma_mult_lt_right 15 j table_len;
  Math.Lemmas.lemma_mult_le_right 15 (j + 1) table_len;
  let bj = LSeq.sub table (j * 15) 15 in
  point_inv_lseq bj /\ S.to_aff_point (point_eval_lseq bj) == pow_base_point j


///  window size = 4

inline_for_extraction noextract
val precomp_basepoint_table_list_w4: x:list uint64{FStar.List.Tot.length x = 240}

inline_for_extraction noextract
val precomp_basepoint_table_lseq_w4 : LSeq.lseq uint64 240

val precomp_basepoint_table_lemma_w4: unit ->
  Lemma (forall (i:nat{i < 16}). precomp_table_acc_inv 16 precomp_basepoint_table_lseq_w4 i)

val precomp_basepoint_table_w4:
  x:glbuffer uint64 240ul{witnessed x precomp_basepoint_table_lseq_w4 /\ recallable x}
