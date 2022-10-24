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

let proj_point_to_list p =
  Hacl.Spec.K256.PrecompTable.proj_point_to_list_lemma p;
  Hacl.Spec.K256.PrecompTable.proj_point_to_list p

let lemma_refl x =
  Hacl.Spec.K256.PrecompTable.proj_point_to_list_lemma x


let precomp_basepoint_table_list_w4: x:list uint64{FStar.List.Tot.length x = 240} =
  normalize_term (SPT.precomp_base_table_list mk_k256_precomp_base_table S.g 15)


let precomp_basepoint_table_lseq_w4 : LSeq.lseq uint64 240 =
  normalize_term_spec (SPT.precomp_base_table_list mk_k256_precomp_base_table S.g 15);
  Seq.seq_of_list precomp_basepoint_table_list_w4


let precomp_basepoint_table_lemma_w4 () =
  normalize_term_spec (SPT.precomp_base_table_list mk_k256_precomp_base_table S.g 15);
  SPT.precomp_base_table_lemma mk_k256_precomp_base_table S.g 16 precomp_basepoint_table_lseq_w4


let precomp_basepoint_table_w4:
  x:glbuffer uint64 240ul{witnessed x precomp_basepoint_table_lseq_w4 /\ recallable x} =
  createL_global precomp_basepoint_table_list_w4


///  window size = 5

let precomp_basepoint_table_list_w5: x:list uint64{FStar.List.Tot.length x = 480} =
  normalize_term (SPT.precomp_base_table_list mk_k256_precomp_base_table S.g 31)


let precomp_basepoint_table_lseq_w5 : LSeq.lseq uint64 480 =
  normalize_term_spec (SPT.precomp_base_table_list mk_k256_precomp_base_table S.g 31);
  Seq.seq_of_list precomp_basepoint_table_list_w5


let precomp_basepoint_table_lemma_w5 () =
  normalize_term_spec (SPT.precomp_base_table_list mk_k256_precomp_base_table S.g 31);
  SPT.precomp_base_table_lemma mk_k256_precomp_base_table S.g 32 precomp_basepoint_table_lseq_w5


let precomp_basepoint_table_w5:
  x:glbuffer uint64 480ul{witnessed x precomp_basepoint_table_lseq_w5 /\ recallable x} =
  createL_global precomp_basepoint_table_list_w5
