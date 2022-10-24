module Hacl.Ed25519.PrecompTable

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum25519
module F51 = Hacl.Impl.Ed25519.Field51

module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module LE = Lib.Exponentiation
module SE = Spec.Exponentiation
module BE = Hacl.Impl.Exponentiation
module ME = Hacl.Impl.MultiExponentiation
module PT = Hacl.Impl.PrecompTable
module SPT = Hacl.Spec.PrecompBaseTable

module BD = Hacl.Bignum.Definitions
module BC = Hacl.Bignum.Convert
module SC = Hacl.Spec.Bignum.Convert

module S = Spec.Ed25519

open Hacl.Impl.Ed25519.PointConstants
include Hacl.Impl.Ed25519.Group

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let ext_point_to_list p =
  Hacl.Spec.Ed25519.PrecompTable.ext_point_to_list_lemma p;
  Hacl.Spec.Ed25519.PrecompTable.ext_point_to_list p


let lemma_refl x =
  Hacl.Spec.Ed25519.PrecompTable.ext_point_to_list_lemma x

///  window size = 4

let precomp_basepoint_table_list_w4: x:list uint64{FStar.List.Tot.length x = 320} =
  normalize_term (SPT.precomp_base_table_list mk_ed25519_precomp_base_table g_c 15)


let precomp_basepoint_table_lseq_w4 : LSeq.lseq uint64 320 =
  normalize_term_spec (SPT.precomp_base_table_list mk_ed25519_precomp_base_table g_c 15);
  Seq.seq_of_list precomp_basepoint_table_list_w4


let precomp_basepoint_table_lemma_w4 () =
  normalize_term_spec (SPT.precomp_base_table_list mk_ed25519_precomp_base_table g_c 15);
  SPT.precomp_base_table_lemma
    mk_ed25519_precomp_base_table g_c 16 precomp_basepoint_table_lseq_w4


let precomp_basepoint_table_w4:
  x:glbuffer uint64 320ul{witnessed x precomp_basepoint_table_lseq_w4 /\ recallable x} =
  createL_global precomp_basepoint_table_list_w4


///  window size = 5

let precomp_basepoint_table_list_w5: x:list uint64{FStar.List.Tot.length x = 640} =
  normalize_term (SPT.precomp_base_table_list mk_ed25519_precomp_base_table g_c 31)


let precomp_basepoint_table_lseq_w5 : LSeq.lseq uint64 640 =
  normalize_term_spec (SPT.precomp_base_table_list mk_ed25519_precomp_base_table g_c 31);
  Seq.seq_of_list precomp_basepoint_table_list_w5


let precomp_basepoint_table_lemma_w5 () =
  normalize_term_spec (SPT.precomp_base_table_list mk_ed25519_precomp_base_table g_c 31);
  SPT.precomp_base_table_lemma
    mk_ed25519_precomp_base_table g_c 32 precomp_basepoint_table_lseq_w5


let precomp_basepoint_table_w5:
  x:glbuffer uint64 640ul{witnessed x precomp_basepoint_table_lseq_w5 /\ recallable x} =
  createL_global precomp_basepoint_table_list_w5
