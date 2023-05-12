module Hacl.P256.PrecompTable

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

module LE = Lib.Exponentiation
module SE = Spec.Exponentiation
module SPT = Hacl.Spec.PrecompBaseTable
module SPT256 = Hacl.Spec.PrecompBaseTable256
module SPTK = Hacl.Spec.P256.PrecompTable

module S = Spec.P256

open Hacl.Impl.P256.Point
include Hacl.Impl.P256.Group

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let mk_p256_concrete_ops =
 Spec.ECC.Projective.mk_ec_concrete_ops_a3 S.p256

let proj_point_to_list p =
  SPTK.proj_point_to_list_lemma p;
  SPTK.proj_point_to_list p

let lemma_refl x =
  SPTK.proj_point_to_list_lemma x

//-----------------

inline_for_extraction noextract
let proj_g_pow2_64 : S.proj_point =
  [@inline_let]
  let rX : S.felem = 0x000931f4ae428a4ad81ee0aa89cf5247ce85d4dd696c61b4bb9d4761e57b7fbe in
  [@inline_let]
  let rY : S.felem = 0x7e88e5e6a142d5c2269f21a158e82ab2c79fcecb26e397b96fd5b9fbcd0a69a5 in
  [@inline_let]
  let rZ : S.felem = 0x02626dc2dd5e06cd19de5e6afb6c5dbdd3e41dc1472e7b8ef11eb0662e41c44b in
  (rX, rY, rZ)

val lemma_proj_g_pow2_64_eval : unit ->
  Lemma (SE.exp_pow2 mk_p256_concrete_ops (S.to_proj_point S.base_point) 64 == proj_g_pow2_64)

let lemma_proj_g_pow2_64_eval () =
  let base_point = S.to_proj_point S.base_point in
  SPT256.exp_pow2_rec_is_exp_pow2 mk_p256_concrete_ops base_point 64;
  let qX, qY, qZ = normalize_term (SPT256.exp_pow2_rec mk_p256_concrete_ops base_point 64) in
  normalize_term_spec (SPT256.exp_pow2_rec mk_p256_concrete_ops base_point 64);
  let rX : S.felem = 0x000931f4ae428a4ad81ee0aa89cf5247ce85d4dd696c61b4bb9d4761e57b7fbe in
  let rY : S.felem = 0x7e88e5e6a142d5c2269f21a158e82ab2c79fcecb26e397b96fd5b9fbcd0a69a5 in
  let rZ : S.felem = 0x02626dc2dd5e06cd19de5e6afb6c5dbdd3e41dc1472e7b8ef11eb0662e41c44b in
  assert_norm (qX == rX /\ qY == rY /\ qZ == rZ)

inline_for_extraction noextract
let proj_g_pow2_64_c : S.proj_point_c =
  lemma_proj_g_pow2_64_eval (); proj_g_pow2_64


inline_for_extraction noextract
let proj_g_pow2_128 : S.proj_point =
  [@inline_let]
  let rX : S.felem = 0x04c3aaf6c6c00704e96eda89461d63fd2c97ee1e6786fc785e6afac7aa92f9b1 in
  [@inline_let]
  let rY : S.felem = 0x14f1edaeb8e9c8d4797d164a3946c7ff50a7c8cd59139a4dbce354e6e4df09c3 in
  [@inline_let]
  let rZ : S.felem = 0x80119ced9a5ce83c4e31f8de1a38f89d5f9ff9f637dca86d116a4217f83e55d2 in
  (rX, rY, rZ)

val lemma_proj_g_pow2_128_eval : unit ->
  Lemma (SE.exp_pow2 mk_p256_concrete_ops proj_g_pow2_64_c 64 == proj_g_pow2_128)

let lemma_proj_g_pow2_128_eval () =
  SPT256.exp_pow2_rec_is_exp_pow2 mk_p256_concrete_ops proj_g_pow2_64_c 64;
  let qX, qY, qZ = normalize_term (SPT256.exp_pow2_rec mk_p256_concrete_ops proj_g_pow2_64_c 64) in
  normalize_term_spec (SPT256.exp_pow2_rec mk_p256_concrete_ops proj_g_pow2_64_c 64);
  let rX : S.felem = 0x04c3aaf6c6c00704e96eda89461d63fd2c97ee1e6786fc785e6afac7aa92f9b1 in
  let rY : S.felem = 0x14f1edaeb8e9c8d4797d164a3946c7ff50a7c8cd59139a4dbce354e6e4df09c3 in
  let rZ : S.felem = 0x80119ced9a5ce83c4e31f8de1a38f89d5f9ff9f637dca86d116a4217f83e55d2 in
  assert_norm (qX == rX /\ qY == rY /\ qZ == rZ)

inline_for_extraction noextract
let proj_g_pow2_128_c : S.proj_point_c =
  lemma_proj_g_pow2_128_eval (); proj_g_pow2_128


inline_for_extraction noextract
let proj_g_pow2_192 : S.proj_point =
  [@inline_let]
  let rX : S.felem = 0xc762a9c8ae1b2f7434ff8da70fe105e0d4f188594989f193de0dbdbf5f60cb9a in
  [@inline_let]
  let rY : S.felem = 0x1eddaf51836859e1369f1ae8d9ab02e4123b6f151d9b796e297a38fa5613d9bc in
  [@inline_let]
  let rZ : S.felem = 0xcb433ab3f67815707e398dc7910cc4ec6ea115360060fc73c35b53dce02e2c72 in
  (rX, rY, rZ)

val lemma_proj_g_pow2_192_eval : unit ->
  Lemma (SE.exp_pow2 mk_p256_concrete_ops proj_g_pow2_128_c 64 == proj_g_pow2_192)

let lemma_proj_g_pow2_192_eval () =
  SPT256.exp_pow2_rec_is_exp_pow2 mk_p256_concrete_ops proj_g_pow2_128_c 64;
  let qX, qY, qZ = normalize_term(SPT256.exp_pow2_rec mk_p256_concrete_ops proj_g_pow2_128_c 64) in
  normalize_term_spec (SPT256.exp_pow2_rec mk_p256_concrete_ops proj_g_pow2_128_c 64);
  let rX : S.felem = 0xc762a9c8ae1b2f7434ff8da70fe105e0d4f188594989f193de0dbdbf5f60cb9a in
  let rY : S.felem = 0x1eddaf51836859e1369f1ae8d9ab02e4123b6f151d9b796e297a38fa5613d9bc in
  let rZ : S.felem = 0xcb433ab3f67815707e398dc7910cc4ec6ea115360060fc73c35b53dce02e2c72 in
  assert_norm (qX == rX /\ qY == rY /\ qZ == rZ)

inline_for_extraction noextract
let proj_g_pow2_192_c : S.proj_point_c =
  lemma_proj_g_pow2_192_eval (); proj_g_pow2_192


// let proj_g_pow2_64 : S.proj_point =
//   normalize_term (SPT256.exp_pow2_rec S.mk_p256_concrete_ops S.base_point 64)

// let proj_g_pow2_128 : S.proj_point =
//   normalize_term (SPT256.exp_pow2_rec S.mk_p256_concrete_ops proj_g_pow2_64 64)

// let proj_g_pow2_192 : S.proj_point =
//   normalize_term (SPT256.exp_pow2_rec S.mk_p256_concrete_ops proj_g_pow2_128 64)


inline_for_extraction noextract
let proj_g_pow2_64_list : SPTK.point_list =
  normalize_term (SPTK.proj_point_to_list proj_g_pow2_64_c)

inline_for_extraction noextract
let proj_g_pow2_128_list : SPTK.point_list =
  normalize_term (SPTK.proj_point_to_list proj_g_pow2_128_c)

inline_for_extraction noextract
let proj_g_pow2_192_list : SPTK.point_list =
  normalize_term (SPTK.proj_point_to_list proj_g_pow2_192_c)


let proj_g_pow2_64_lseq : LSeq.lseq uint64 12 =
  normalize_term_spec (SPTK.proj_point_to_list proj_g_pow2_64);
  Seq.seq_of_list proj_g_pow2_64_list

let proj_g_pow2_128_lseq : LSeq.lseq uint64 12 =
  normalize_term_spec (SPTK.proj_point_to_list proj_g_pow2_128);
  Seq.seq_of_list proj_g_pow2_128_list

let proj_g_pow2_192_lseq : LSeq.lseq uint64 12 =
  normalize_term_spec (SPTK.proj_point_to_list proj_g_pow2_192);
  Seq.seq_of_list proj_g_pow2_192_list


val proj_g_pow2_64_lemma: unit ->
  Lemma (S.to_aff_point proj_g_pow2_64 == pow_point (pow2 64) g_aff)

let proj_g_pow2_64_lemma () =
  lemma_proj_g_pow2_64_eval ();
  Spec.EC.Projective.Lemmas.lemma_proj_aff_id S.p256 S.base_point;
  SPT256.a_pow2_64_lemma mk_p256_concrete_ops (S.to_proj_point S.base_point)


val proj_g_pow2_128_lemma: unit ->
  Lemma (S.to_aff_point proj_g_pow2_128 == pow_point (pow2 128) g_aff)

let proj_g_pow2_128_lemma () =
  lemma_proj_g_pow2_128_eval ();
  lemma_proj_g_pow2_64_eval ();
  Spec.EC.Projective.Lemmas.lemma_proj_aff_id S.p256 S.base_point;
  SPT256.a_pow2_128_lemma mk_p256_concrete_ops (S.to_proj_point S.base_point)


val proj_g_pow2_192_lemma: unit ->
  Lemma (S.to_aff_point proj_g_pow2_192 == pow_point (pow2 192) g_aff)

let proj_g_pow2_192_lemma () =
  lemma_proj_g_pow2_192_eval ();
  lemma_proj_g_pow2_128_eval ();
  lemma_proj_g_pow2_64_eval ();
  Spec.EC.Projective.Lemmas.lemma_proj_aff_id S.p256 S.base_point;
  SPT256.a_pow2_192_lemma mk_p256_concrete_ops (S.to_proj_point S.base_point)


let proj_g_pow2_64_lseq_lemma () =
  normalize_term_spec (SPTK.proj_point_to_list proj_g_pow2_64);
  proj_g_pow2_64_lemma ();
  SPTK.proj_point_to_list_lemma proj_g_pow2_64


let proj_g_pow2_128_lseq_lemma () =
  normalize_term_spec (SPTK.proj_point_to_list proj_g_pow2_128);
  proj_g_pow2_128_lemma ();
  SPTK.proj_point_to_list_lemma proj_g_pow2_128


let proj_g_pow2_192_lseq_lemma () =
  normalize_term_spec (SPTK.proj_point_to_list proj_g_pow2_192);
  proj_g_pow2_192_lemma ();
  SPTK.proj_point_to_list_lemma proj_g_pow2_192


let mk_proj_g_pow2_64 () =
  createL proj_g_pow2_64_list

let mk_proj_g_pow2_128 () =
  createL proj_g_pow2_128_list

let mk_proj_g_pow2_192 () =
  createL proj_g_pow2_192_list

//----------------

///  window size = 4; precomputed table = [[0]G, [1]G, ..., [15]G]

inline_for_extraction noextract
let precomp_basepoint_table_list_w4: x:list uint64{FStar.List.Tot.length x = 192} =
  normalize_term (SPT.precomp_base_table_list mk_p256_precomp_base_table
    (S.to_proj_point S.base_point) 15)

let precomp_basepoint_table_lseq_w4 : LSeq.lseq uint64 192 =
  normalize_term_spec (SPT.precomp_base_table_list mk_p256_precomp_base_table
    (S.to_proj_point S.base_point) 15);
  Seq.seq_of_list precomp_basepoint_table_list_w4

let precomp_basepoint_table_lemma_w4 () =
  Spec.EC.Projective.Lemmas.lemma_proj_aff_id S.p256 S.base_point;
  normalize_term_spec (SPT.precomp_base_table_list mk_p256_precomp_base_table
    (S.to_proj_point S.base_point) 15);
  SPT.precomp_base_table_lemma mk_p256_precomp_base_table
    (S.to_proj_point S.base_point) 16 precomp_basepoint_table_lseq_w4

let precomp_basepoint_table_w4:
  x:glbuffer uint64 192ul{witnessed x precomp_basepoint_table_lseq_w4 /\ recallable x} =
  createL_global precomp_basepoint_table_list_w4


///  window size = 4; precomputed table = [[0]([pow2 64]G), [1]([pow2 64]G), ..., [15]([pow2 64]G)]

inline_for_extraction noextract
let precomp_g_pow2_64_table_list_w4: x:list uint64{FStar.List.Tot.length x = 192} =
  normalize_term (SPT.precomp_base_table_list mk_p256_precomp_base_table proj_g_pow2_64_c 15)

let precomp_g_pow2_64_table_lseq_w4 : LSeq.lseq uint64 192 =
  normalize_term_spec (SPT.precomp_base_table_list mk_p256_precomp_base_table proj_g_pow2_64_c 15);
  Seq.seq_of_list precomp_g_pow2_64_table_list_w4

let precomp_g_pow2_64_table_lemma_w4 () =
  normalize_term_spec (SPT.precomp_base_table_list mk_p256_precomp_base_table proj_g_pow2_64_c 15);
  SPT.precomp_base_table_lemma mk_p256_precomp_base_table
    proj_g_pow2_64_c 16 precomp_g_pow2_64_table_lseq_w4;
  proj_g_pow2_64_lemma ()

let precomp_g_pow2_64_table_w4:
  x:glbuffer uint64 192ul{witnessed x precomp_g_pow2_64_table_lseq_w4 /\ recallable x} =
  createL_global precomp_g_pow2_64_table_list_w4


///  window size = 4; precomputed table = [[0]([pow2 128]G), [1]([pow2 128]G),...,[15]([pow2 128]G)]

inline_for_extraction noextract
let precomp_g_pow2_128_table_list_w4: x:list uint64{FStar.List.Tot.length x = 192} =
  normalize_term (SPT.precomp_base_table_list mk_p256_precomp_base_table proj_g_pow2_128_c 15)

let precomp_g_pow2_128_table_lseq_w4 : LSeq.lseq uint64 192 =
  normalize_term_spec (SPT.precomp_base_table_list mk_p256_precomp_base_table
    proj_g_pow2_128_c 15);
  Seq.seq_of_list precomp_g_pow2_128_table_list_w4

let precomp_g_pow2_128_table_lemma_w4 () =
  normalize_term_spec (SPT.precomp_base_table_list mk_p256_precomp_base_table
    proj_g_pow2_128_c 15);
  SPT.precomp_base_table_lemma mk_p256_precomp_base_table
    proj_g_pow2_128_c 16 precomp_g_pow2_64_table_lseq_w4;
  proj_g_pow2_128_lemma ()

let precomp_g_pow2_128_table_w4:
  x:glbuffer uint64 192ul{witnessed x precomp_g_pow2_128_table_lseq_w4 /\ recallable x} =
  createL_global precomp_g_pow2_128_table_list_w4


///  window size = 4; precomputed table = [[0]([pow2 192]G), [1]([pow2 192]G),...,[15]([pow2 192]G)]

inline_for_extraction noextract
let precomp_g_pow2_192_table_list_w4: x:list uint64{FStar.List.Tot.length x = 192} =
  normalize_term (SPT.precomp_base_table_list mk_p256_precomp_base_table proj_g_pow2_192_c 15)

let precomp_g_pow2_192_table_lseq_w4 : LSeq.lseq uint64 192 =
  normalize_term_spec (SPT.precomp_base_table_list mk_p256_precomp_base_table
    proj_g_pow2_192_c 15);
  Seq.seq_of_list precomp_g_pow2_192_table_list_w4

let precomp_g_pow2_192_table_lemma_w4 () =
  normalize_term_spec (SPT.precomp_base_table_list mk_p256_precomp_base_table
    proj_g_pow2_192_c 15);
  SPT.precomp_base_table_lemma mk_p256_precomp_base_table
    proj_g_pow2_192_c 16 precomp_g_pow2_64_table_lseq_w4;
  proj_g_pow2_192_lemma ()

let precomp_g_pow2_192_table_w4:
  x:glbuffer uint64 192ul{witnessed x precomp_g_pow2_192_table_lseq_w4 /\ recallable x} =
  createL_global precomp_g_pow2_192_table_list_w4


///  window size = 5; precomputed table = [[0]G, [1]G, ..., [31]G]

inline_for_extraction noextract
let precomp_basepoint_table_list_w5: x:list uint64{FStar.List.Tot.length x = 384} =
  normalize_term (SPT.precomp_base_table_list mk_p256_precomp_base_table
    (S.to_proj_point S.base_point) 31)

let precomp_basepoint_table_lseq_w5 : LSeq.lseq uint64 384 =
  normalize_term_spec (SPT.precomp_base_table_list mk_p256_precomp_base_table
    (S.to_proj_point S.base_point) 31);
  Seq.seq_of_list precomp_basepoint_table_list_w5

let precomp_basepoint_table_lemma_w5 () =
  Spec.EC.Projective.Lemmas.lemma_proj_aff_id S.p256 S.base_point;
  normalize_term_spec (SPT.precomp_base_table_list mk_p256_precomp_base_table
    (S.to_proj_point S.base_point) 31);
  SPT.precomp_base_table_lemma mk_p256_precomp_base_table
    (S.to_proj_point S.base_point) 32 precomp_basepoint_table_lseq_w5

let precomp_basepoint_table_w5:
  x:glbuffer uint64 384ul{witnessed x precomp_basepoint_table_lseq_w5 /\ recallable x} =
  createL_global precomp_basepoint_table_list_w5
