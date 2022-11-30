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
module SPT = Hacl.Spec.PrecompBaseTable
module SPT256 = Hacl.Spec.PrecompBaseTable256
module SPTK = Hacl.Spec.K256.PrecompTable

module S = Spec.K256
module SL = Spec.K256.Lemmas

open Hacl.Impl.K256.Point
include Hacl.Impl.K256.Group

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let proj_point_to_list p =
  SPTK.proj_point_to_list_lemma p;
  SPTK.proj_point_to_list p

let lemma_refl x =
  SPTK.proj_point_to_list_lemma x

//-----------------

inline_for_extraction noextract
let proj_g_pow2_64 : S.proj_point =
  [@inline_let]
  let rX : S.felem = 0x46ec0aa60b0b98c37b29371784676ad967b7beb1a941ddb6fbbff95b44cb788b in
  [@inline_let]
  let rY : S.felem = 0x6b946755bbc6b677576579c990a1ccf14a710545251a1428fabbf02f40268e63 in
  [@inline_let]
  let rZ : S.felem = 0x3c114b2ac17c199ec9eba9f7cc64dc459ca2e53f5bbead2b4e618b318ffcc00e in
  (rX, rY, rZ)

val lemma_proj_g_pow2_64_eval : unit ->
  Lemma (SE.exp_pow2 S.mk_k256_concrete_ops S.g 64 == proj_g_pow2_64)

let lemma_proj_g_pow2_64_eval () =
  SPT256.exp_pow2_rec_is_exp_pow2 S.mk_k256_concrete_ops S.g 64;
  let qX, qY, qZ = normalize_term (SPT256.exp_pow2_rec S.mk_k256_concrete_ops S.g 64) in
  normalize_term_spec (SPT256.exp_pow2_rec S.mk_k256_concrete_ops S.g 64);
  let rX : S.felem = 0x46ec0aa60b0b98c37b29371784676ad967b7beb1a941ddb6fbbff95b44cb788b in
  let rY : S.felem = 0x6b946755bbc6b677576579c990a1ccf14a710545251a1428fabbf02f40268e63 in
  let rZ : S.felem = 0x3c114b2ac17c199ec9eba9f7cc64dc459ca2e53f5bbead2b4e618b318ffcc00e in
  assert_norm (qX == rX /\ qY == rY /\ qZ == rZ)


inline_for_extraction noextract
let proj_g_pow2_128 : S.proj_point =
  [@inline_let]
  let rX : S.felem = 0x98299efbc8e459915404ae015b48cac3b929e0158665f3c7fa5489fbd25c4297 in
  [@inline_let]
  let rY : S.felem = 0xf1e5cbc9579e7d11a31681e947c2959ae0298a006d1c06ab1ad93d6716ea50cc in
  [@inline_let]
  let rZ : S.felem = 0x5c53ffe15001674a2eacb60c9327a8b0ddbd93a0fa6d90309de6cc124133938b in
  (rX, rY, rZ)

val lemma_proj_g_pow2_128_eval : unit ->
  Lemma (SE.exp_pow2 S.mk_k256_concrete_ops proj_g_pow2_64 64 == proj_g_pow2_128)

let lemma_proj_g_pow2_128_eval () =
  SPT256.exp_pow2_rec_is_exp_pow2 S.mk_k256_concrete_ops proj_g_pow2_64 64;
  let qX, qY, qZ = normalize_term (SPT256.exp_pow2_rec S.mk_k256_concrete_ops proj_g_pow2_64 64) in
  normalize_term_spec (SPT256.exp_pow2_rec S.mk_k256_concrete_ops proj_g_pow2_64 64);
  let rX : S.felem = 0x98299efbc8e459915404ae015b48cac3b929e0158665f3c7fa5489fbd25c4297 in
  let rY : S.felem = 0xf1e5cbc9579e7d11a31681e947c2959ae0298a006d1c06ab1ad93d6716ea50cc in
  let rZ : S.felem = 0x5c53ffe15001674a2eacb60c9327a8b0ddbd93a0fa6d90309de6cc124133938b in
  assert_norm (qX == rX /\ qY == rY /\ qZ == rZ)


inline_for_extraction noextract
let proj_g_pow2_192 : S.proj_point =
  [@inline_let]
  let rX : S.felem = 0xbd382b67d20492b1480ca58a6d7d617ba413a9bc7c2f1cff51301ef960fb245c in
  [@inline_let]
  let rY : S.felem = 0x0b232afcf692673aa714357c524c07867a64ea3b9dfab53f0e74622159e86b0d in
  [@inline_let]
  let rZ : S.felem = 0x028a1380449aede5df8219420b458d464a6a4773ac91e8305237878cef1cffa6 in
  (rX, rY, rZ)

val lemma_proj_g_pow2_192_eval : unit ->
  Lemma (SE.exp_pow2 S.mk_k256_concrete_ops proj_g_pow2_128 64 == proj_g_pow2_192)

let lemma_proj_g_pow2_192_eval () =
  SPT256.exp_pow2_rec_is_exp_pow2 S.mk_k256_concrete_ops proj_g_pow2_128 64;
  let qX, qY, qZ = normalize_term (SPT256.exp_pow2_rec S.mk_k256_concrete_ops proj_g_pow2_128 64) in
  normalize_term_spec (SPT256.exp_pow2_rec S.mk_k256_concrete_ops proj_g_pow2_128 64);
  let rX : S.felem = 0xbd382b67d20492b1480ca58a6d7d617ba413a9bc7c2f1cff51301ef960fb245c in
  let rY : S.felem = 0x0b232afcf692673aa714357c524c07867a64ea3b9dfab53f0e74622159e86b0d in
  let rZ : S.felem = 0x028a1380449aede5df8219420b458d464a6a4773ac91e8305237878cef1cffa6 in
  assert_norm (qX == rX /\ qY == rY /\ qZ == rZ)


// let proj_g_pow2_64 : S.proj_point =
//   normalize_term (SPT256.exp_pow2_rec S.mk_k256_concrete_ops S.g 64)

// let proj_g_pow2_128 : S.proj_point =
//   normalize_term (SPT256.exp_pow2_rec S.mk_k256_concrete_ops proj_g_pow2_64 64)

// let proj_g_pow2_192 : S.proj_point =
//   normalize_term (SPT256.exp_pow2_rec S.mk_k256_concrete_ops proj_g_pow2_128 64)


inline_for_extraction noextract
let proj_g_pow2_64_list : SPTK.point_list =
  normalize_term (SPTK.proj_point_to_list proj_g_pow2_64)

inline_for_extraction noextract
let proj_g_pow2_128_list : SPTK.point_list =
  normalize_term (SPTK.proj_point_to_list proj_g_pow2_128)

inline_for_extraction noextract
let proj_g_pow2_192_list : SPTK.point_list =
  normalize_term (SPTK.proj_point_to_list proj_g_pow2_192)


let proj_g_pow2_64_lseq : LSeq.lseq uint64 15 =
  normalize_term_spec (SPTK.proj_point_to_list proj_g_pow2_64);
  Seq.seq_of_list proj_g_pow2_64_list

let proj_g_pow2_128_lseq : LSeq.lseq uint64 15 =
  normalize_term_spec (SPTK.proj_point_to_list proj_g_pow2_128);
  Seq.seq_of_list proj_g_pow2_128_list

let proj_g_pow2_192_lseq : LSeq.lseq uint64 15 =
  normalize_term_spec (SPTK.proj_point_to_list proj_g_pow2_192);
  Seq.seq_of_list proj_g_pow2_192_list


val proj_g_pow2_64_lemma: unit ->
  Lemma (S.to_aff_point proj_g_pow2_64 == pow_point (pow2 64) g_aff)

let proj_g_pow2_64_lemma () =
  lemma_proj_g_pow2_64_eval ();
  SPT256.a_pow2_64_lemma S.mk_k256_concrete_ops S.g


val proj_g_pow2_128_lemma: unit ->
  Lemma (S.to_aff_point proj_g_pow2_128 == pow_point (pow2 128) g_aff)

let proj_g_pow2_128_lemma () =
  lemma_proj_g_pow2_128_eval ();
  lemma_proj_g_pow2_64_eval ();
  SPT256.a_pow2_128_lemma S.mk_k256_concrete_ops S.g


val proj_g_pow2_192_lemma: unit ->
  Lemma (S.to_aff_point proj_g_pow2_192 == pow_point (pow2 192) g_aff)

let proj_g_pow2_192_lemma () =
  lemma_proj_g_pow2_192_eval ();
  lemma_proj_g_pow2_128_eval ();
  lemma_proj_g_pow2_64_eval ();
  SPT256.a_pow2_192_lemma S.mk_k256_concrete_ops S.g


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


///  window size = 4; precomputed table = [[0]([pow2 64]G), [1]([pow2 64]G), ..., [15]([pow2 64]G)]

inline_for_extraction noextract
let precomp_g_pow2_64_table_list_w4: x:list uint64{FStar.List.Tot.length x = 240} =
  normalize_term (SPT.precomp_base_table_list mk_k256_precomp_base_table proj_g_pow2_64 15)

let precomp_g_pow2_64_table_lseq_w4 : LSeq.lseq uint64 240 =
  normalize_term_spec (SPT.precomp_base_table_list mk_k256_precomp_base_table proj_g_pow2_64 15);
  Seq.seq_of_list precomp_g_pow2_64_table_list_w4

let precomp_g_pow2_64_table_lemma_w4 () =
  normalize_term_spec (SPT.precomp_base_table_list mk_k256_precomp_base_table proj_g_pow2_64 15);
  SPT.precomp_base_table_lemma mk_k256_precomp_base_table
    proj_g_pow2_64 16 precomp_g_pow2_64_table_lseq_w4;
  proj_g_pow2_64_lemma ()

let precomp_g_pow2_64_table_w4:
  x:glbuffer uint64 240ul{witnessed x precomp_g_pow2_64_table_lseq_w4 /\ recallable x} =
  createL_global precomp_g_pow2_64_table_list_w4


///  window size = 4; precomputed table = [[0]([pow2 128]G), [1]([pow2 128]G),...,[15]([pow2 128]G)]

inline_for_extraction noextract
let precomp_g_pow2_128_table_list_w4: x:list uint64{FStar.List.Tot.length x = 240} =
  normalize_term (SPT.precomp_base_table_list mk_k256_precomp_base_table proj_g_pow2_128 15)

let precomp_g_pow2_128_table_lseq_w4 : LSeq.lseq uint64 240 =
  normalize_term_spec (SPT.precomp_base_table_list mk_k256_precomp_base_table proj_g_pow2_128 15);
  Seq.seq_of_list precomp_g_pow2_128_table_list_w4

let precomp_g_pow2_128_table_lemma_w4 () =
  normalize_term_spec (SPT.precomp_base_table_list mk_k256_precomp_base_table proj_g_pow2_128 15);
  SPT.precomp_base_table_lemma mk_k256_precomp_base_table
    proj_g_pow2_128 16 precomp_g_pow2_64_table_lseq_w4;
  proj_g_pow2_128_lemma ()

let precomp_g_pow2_128_table_w4:
  x:glbuffer uint64 240ul{witnessed x precomp_g_pow2_128_table_lseq_w4 /\ recallable x} =
  createL_global precomp_g_pow2_128_table_list_w4


///  window size = 4; precomputed table = [[0]([pow2 192]G), [1]([pow2 192]G),...,[15]([pow2 192]G)]

inline_for_extraction noextract
let precomp_g_pow2_192_table_list_w4: x:list uint64{FStar.List.Tot.length x = 240} =
  normalize_term (SPT.precomp_base_table_list mk_k256_precomp_base_table proj_g_pow2_192 15)

let precomp_g_pow2_192_table_lseq_w4 : LSeq.lseq uint64 240 =
  normalize_term_spec (SPT.precomp_base_table_list mk_k256_precomp_base_table proj_g_pow2_192 15);
  Seq.seq_of_list precomp_g_pow2_192_table_list_w4

let precomp_g_pow2_192_table_lemma_w4 () =
  normalize_term_spec (SPT.precomp_base_table_list mk_k256_precomp_base_table proj_g_pow2_192 15);
  SPT.precomp_base_table_lemma mk_k256_precomp_base_table
    proj_g_pow2_192 16 precomp_g_pow2_64_table_lseq_w4;
  proj_g_pow2_192_lemma ()

let precomp_g_pow2_192_table_w4:
  x:glbuffer uint64 240ul{witnessed x precomp_g_pow2_192_table_lseq_w4 /\ recallable x} =
  createL_global precomp_g_pow2_192_table_list_w4


///  window size = 5; precomputed table = [[0]G, [1]G, ..., [31]G]

inline_for_extraction noextract
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
