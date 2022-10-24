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

inline_for_extraction noextract
val ext_point_to_list: p:S.ext_point_c
  -> x:list uint64{FStar.List.Tot.length x = 20 /\
    mk_to_ed25519_comm_monoid.BE.linv (Seq.seq_of_list x)}


val lemma_refl: x:S.ext_point_c ->
  Lemma (S.mk_ed25519_concrete_ops.SE.to.SE.refl x ==
    mk_to_ed25519_comm_monoid.BE.refl (Seq.seq_of_list (ext_point_to_list x)))


inline_for_extraction noextract
let mk_ed25519_precomp_base_table: SPT.mk_precomp_base_table S.ext_point_c U64 20ul 0ul = {
  SPT.concr_ops = S.mk_ed25519_concrete_ops;
  SPT.to_cm = mk_to_ed25519_comm_monoid;
  SPT.to_list = ext_point_to_list;
  SPT.lemma_refl = lemma_refl;
}


inline_for_extraction noextract
let g_c : S.ext_point_c =
  Spec.Ed25519.Lemmas.g_is_on_curve ();
  S.g


inline_for_extraction noextract
let pow_base_point (k:nat) =
  LE.pow S.mk_ed25519_comm_monoid (S.to_aff_point g_c) k

unfold
let precomp_table_acc_inv
  (table_len:nat{table_len * 20 <= max_size_t})
  (table:LSeq.lseq uint64 (table_len * 20))
  (j:nat{j < table_len})
=
  Math.Lemmas.lemma_mult_lt_right 20 j table_len;
  Math.Lemmas.lemma_mult_le_right 20 (j + 1) table_len;
  let bj = LSeq.sub table (j * 20) 20 in
  F51.linv bj /\ refl bj == pow_base_point j


///  window size = 4

inline_for_extraction noextract
val precomp_basepoint_table_list_w4: x:list uint64{FStar.List.Tot.length x = 320}

inline_for_extraction noextract
val precomp_basepoint_table_lseq_w4 : LSeq.lseq uint64 320

val precomp_basepoint_table_lemma_w4: unit ->
  Lemma (forall (i:nat{i < 16}). precomp_table_acc_inv 16 precomp_basepoint_table_lseq_w4 i)

val precomp_basepoint_table_w4:
  x:glbuffer uint64 320ul{witnessed x precomp_basepoint_table_lseq_w4 /\ recallable x}


///  window size = 5

inline_for_extraction noextract
val precomp_basepoint_table_list_w5: x:list uint64{FStar.List.Tot.length x = 640}

inline_for_extraction noextract
val precomp_basepoint_table_lseq_w5 : LSeq.lseq uint64 640

val precomp_basepoint_table_lemma_w5: unit ->
  Lemma (forall (i:nat{i < 32}). precomp_table_acc_inv 32 precomp_basepoint_table_lseq_w5 i)


val precomp_basepoint_table_w5:
  x:glbuffer uint64 640ul{witnessed x precomp_basepoint_table_lseq_w5 /\ recallable x}
