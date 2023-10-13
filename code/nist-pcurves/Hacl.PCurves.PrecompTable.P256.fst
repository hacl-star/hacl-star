module Hacl.PCurves.PrecompTable.P256

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
module SPTK = Hacl.Spec.PCurves.PrecompTable

module S = Spec.PCurves
module SL = Spec.PCurves.Lemmas

open Hacl.Impl.PCurves.Point
include Hacl.Impl.PCurves.Group

open Hacl.PCurves.PrecompTable
open Spec.P256

#set-options "--z3rlimit 100 --fuel 0 --ifuel 0"

//----------------

inline_for_extraction noextract
let p256_proj_g_pow2_64 : S.proj_point =
  [@inline_let]
  let rX : S.felem = 0x000931f4ae428a4ad81ee0aa89cf5247ce85d4dd696c61b4bb9d4761e57b7fbe in
  [@inline_let]
  let rY : S.felem = 0x7e88e5e6a142d5c2269f21a158e82ab2c79fcecb26e397b96fd5b9fbcd0a69a5 in
  [@inline_let]
  let rZ : S.felem = 0x02626dc2dd5e06cd19de5e6afb6c5dbdd3e41dc1472e7b8ef11eb0662e41c44b in
  (rX, rY, rZ)

noextract
val lemma_p256_proj_g_pow2_64_eval : unit ->
  Lemma (SE.exp_pow2 S.mk_pcurve_concrete_ops S.base_point 64 == p256_proj_g_pow2_64)

noextract
let lemma_p256_proj_g_pow2_64_eval () =
  SPT256.exp_pow2_rec_is_exp_pow2 S.mk_pcurve_concrete_ops S.base_point 64;
  let qX, qY, qZ = normalize_term (SPT256.exp_pow2_rec S.mk_pcurve_concrete_ops S.base_point 64) in
  normalize_term_spec (SPT256.exp_pow2_rec #S.proj_point (S.mk_pcurve_concrete_ops #Spec.P256.p256_params) (S.base_point #Spec.P256.p256_params) 64);
  let rX : S.felem = 0x000931f4ae428a4ad81ee0aa89cf5247ce85d4dd696c61b4bb9d4761e57b7fbe in
  let rY : S.felem = 0x7e88e5e6a142d5c2269f21a158e82ab2c79fcecb26e397b96fd5b9fbcd0a69a5 in
  let rZ : S.felem = 0x02626dc2dd5e06cd19de5e6afb6c5dbdd3e41dc1472e7b8ef11eb0662e41c44b in
  assert_norm (qX == rX /\ qY == rY /\ qZ == rZ)
  

inline_for_extraction noextract
let p256_proj_g_pow2_128 : S.proj_point =
  [@inline_let]
  let rX : S.felem = 0x04c3aaf6c6c00704e96eda89461d63fd2c97ee1e6786fc785e6afac7aa92f9b1 in
  [@inline_let]
  let rY : S.felem = 0x14f1edaeb8e9c8d4797d164a3946c7ff50a7c8cd59139a4dbce354e6e4df09c3 in
  [@inline_let]
  let rZ : S.felem = 0x80119ced9a5ce83c4e31f8de1a38f89d5f9ff9f637dca86d116a4217f83e55d2 in
  (rX, rY, rZ)

noextract
val lemma_p256_proj_g_pow2_128_eval: unit ->
  Lemma (SE.exp_pow2 S.mk_pcurve_concrete_ops p256_proj_g_pow2_64 64 == p256_proj_g_pow2_128)

noextract
let lemma_p256_proj_g_pow2_128_eval () =
  SPT256.exp_pow2_rec_is_exp_pow2 S.mk_pcurve_concrete_ops p256_proj_g_pow2_64 64;
  let qX, qY, qZ = normalize_term (SPT256.exp_pow2_rec S.mk_pcurve_concrete_ops p256_proj_g_pow2_64 64) in
  normalize_term_spec (SPT256.exp_pow2_rec S.mk_pcurve_concrete_ops p256_proj_g_pow2_64 64);
  let rX : S.felem = 0x04c3aaf6c6c00704e96eda89461d63fd2c97ee1e6786fc785e6afac7aa92f9b1 in
  let rY : S.felem = 0x14f1edaeb8e9c8d4797d164a3946c7ff50a7c8cd59139a4dbce354e6e4df09c3 in
  let rZ : S.felem = 0x80119ced9a5ce83c4e31f8de1a38f89d5f9ff9f637dca86d116a4217f83e55d2 in
  assert_norm (qX == rX /\ qY == rY /\ qZ == rZ)

inline_for_extraction noextract
let p256_proj_g_pow2_192 : S.proj_point =
  [@inline_let]
  let rX : S.felem = 0xc762a9c8ae1b2f7434ff8da70fe105e0d4f188594989f193de0dbdbf5f60cb9a in
  [@inline_let]
  let rY : S.felem = 0x1eddaf51836859e1369f1ae8d9ab02e4123b6f151d9b796e297a38fa5613d9bc in
  [@inline_let]
  let rZ : S.felem = 0xcb433ab3f67815707e398dc7910cc4ec6ea115360060fc73c35b53dce02e2c72 in
  (rX, rY, rZ)

noextract
val lemma_p256_proj_g_pow2_192_eval : unit ->
  Lemma (SE.exp_pow2 S.mk_pcurve_concrete_ops p256_proj_g_pow2_128 64 == p256_proj_g_pow2_192)

noextract
let lemma_p256_proj_g_pow2_192_eval () =
  SPT256.exp_pow2_rec_is_exp_pow2 S.mk_pcurve_concrete_ops p256_proj_g_pow2_128 64;
  let qX, qY, qZ = normalize_term (SPT256.exp_pow2_rec S.mk_pcurve_concrete_ops p256_proj_g_pow2_128 64) in
  normalize_term_spec (SPT256.exp_pow2_rec S.mk_pcurve_concrete_ops p256_proj_g_pow2_128 64);
  let rX : S.felem = 0xc762a9c8ae1b2f7434ff8da70fe105e0d4f188594989f193de0dbdbf5f60cb9a in
  let rY : S.felem = 0x1eddaf51836859e1369f1ae8d9ab02e4123b6f151d9b796e297a38fa5613d9bc in
  let rZ : S.felem = 0xcb433ab3f67815707e398dc7910cc4ec6ea115360060fc73c35b53dce02e2c72 in
  assert_norm (qX == rX /\ qY == rY /\ qZ == rZ)

inline_for_extraction noextract
instance p256_precomp_g_points: precomp_g_points = {
  proj_g_pow2_64 = p256_proj_g_pow2_64;
  lemma_proj_g_pow2_64_eval = lemma_p256_proj_g_pow2_64_eval;
  proj_g_pow2_128 = p256_proj_g_pow2_128;
  lemma_proj_g_pow2_128_eval = lemma_p256_proj_g_pow2_128_eval;
  proj_g_pow2_192 = p256_proj_g_pow2_192;
  lemma_proj_g_pow2_192_eval = lemma_p256_proj_g_pow2_192_eval;
}
 

///  window size = 4; precomputed table = [[0]G, [1]G, ..., [15]G]
 
inline_for_extraction noextract
let p256_basepoint_table_list_w4: x:list uint64{FStar.List.Tot.length x = 192} =
  normalize_term (SPT.precomp_base_table_list mk_pcurve_precomp_base_table p256_basepoint 15)
 

noextract
let p256_basepoint_table_lseq_w4 : LSeq.lseq uint64 (192) =
  normalize_term_spec (SPT.precomp_base_table_list mk_pcurve_precomp_base_table S.base_point 15);
  Seq.seq_of_list p256_basepoint_table_list_w4

noextract
val p256_basepoint_table_lemma_w4: unit ->
  Lemma ((forall (i:nat{i < 16}). precomp_table_acc_inv g_aff 16
         p256_basepoint_table_lseq_w4 i))

noextract
let p256_basepoint_table_lemma_w4 () =
  normalize_term_spec (SPT.precomp_base_table_list mk_pcurve_precomp_base_table S.base_point 15);
  SPT.precomp_base_table_lemma #_ #_ #(3ul*.4ul) mk_pcurve_precomp_base_table S.base_point 16 p256_basepoint_table_lseq_w4

val p256_basepoint_table_w4:
  x:glbuffer uint64 192ul{witnessed x p256_basepoint_table_lseq_w4 /\ recallable x}

#push-options "--fuel 2 --ifuel 2"
let p256_basepoint_table_w4:
  x:glbuffer uint64 192ul{witnessed x p256_basepoint_table_lseq_w4 /\ recallable x} =
  createL_global p256_basepoint_table_list_w4
#pop-options

inline_for_extraction noextract
let p256_precomp_basepoint_table_w4 : precomp_table_w4 g_aff = {
  table_lseq_w4 = p256_basepoint_table_lseq_w4;
  table_lemma_w4 = p256_basepoint_table_lemma_w4;
  table_w4 = p256_basepoint_table_w4
}


///  window size = 4; precomputed table = [[0]([pow2 64]G), [1]([pow2 64]G), ..., [15]([pow2 64]G)]

inline_for_extraction noextract
let p256_g_pow2_64_table_list_w4: x:list uint64{FStar.List.Tot.length x = 192} =
  normalize_term (SPT.precomp_base_table_list mk_pcurve_precomp_base_table proj_g_pow2_64 15)

noextract
let p256_g_pow2_64_table_lseq_w4 : LSeq.lseq uint64 192 =
  normalize_term_spec (SPT.precomp_base_table_list mk_pcurve_precomp_base_table proj_g_pow2_64 15);
  Seq.seq_of_list p256_g_pow2_64_table_list_w4

noextract
val p256_g_pow2_64_table_lemma_w4: unit ->
  Lemma (forall (i:nat{i < 16}). precomp_table_acc_inv g_pow2_64 16 p256_g_pow2_64_table_lseq_w4 i)

noextract
let p256_g_pow2_64_table_lemma_w4 () =
  normalize_term_spec (SPT.precomp_base_table_list mk_pcurve_precomp_base_table proj_g_pow2_64 15);
  SPT.precomp_base_table_lemma mk_pcurve_precomp_base_table
    proj_g_pow2_64 16 p256_g_pow2_64_table_lseq_w4;
  proj_g_pow2_64_lemma ()


val p256_g_pow2_64_table_w4 :
  x:glbuffer uint64 192ul{witnessed x p256_g_pow2_64_table_lseq_w4 /\ recallable x}

#push-options "--fuel 2 --ifuel 2"
let p256_g_pow2_64_table_w4 :
  x:glbuffer uint64 192ul{witnessed x p256_g_pow2_64_table_lseq_w4 /\ recallable x} =
  createL_global p256_g_pow2_64_table_list_w4
#pop-options

inline_for_extraction noextract
let p256_precomp_g_pow2_64_table_w4 : precomp_table_w4 g_pow2_64 = {
  table_lseq_w4 = p256_g_pow2_64_table_lseq_w4;
  table_lemma_w4 = p256_g_pow2_64_table_lemma_w4;
  table_w4 = p256_g_pow2_64_table_w4
}



///  window size = 4; precomputed table = [[0]([pow2 128]G), [1]([pow2 128]G),...,[15]([pow2 128]G)]

inline_for_extraction noextract
let p256_g_pow2_128_table_list_w4: x:list uint64{FStar.List.Tot.length x = 192} =
  normalize_term (SPT.precomp_base_table_list mk_pcurve_precomp_base_table proj_g_pow2_128 15)

noextract
let p256_g_pow2_128_table_lseq_w4 : LSeq.lseq uint64 192 =
  normalize_term_spec (SPT.precomp_base_table_list mk_pcurve_precomp_base_table proj_g_pow2_128 15);
  Seq.seq_of_list p256_g_pow2_128_table_list_w4

noextract
val p256_g_pow2_128_table_lemma_w4: unit ->
  Lemma (forall (i:nat{i < 16}). precomp_table_acc_inv g_pow2_128 16 p256_g_pow2_128_table_lseq_w4 i)

noextract
let p256_g_pow2_128_table_lemma_w4 () =
  normalize_term_spec (SPT.precomp_base_table_list mk_pcurve_precomp_base_table proj_g_pow2_128 15);
  SPT.precomp_base_table_lemma mk_pcurve_precomp_base_table
    proj_g_pow2_128 16 p256_g_pow2_128_table_lseq_w4;
  proj_g_pow2_128_lemma ()


val p256_g_pow2_128_table_w4 :
  x:glbuffer uint64 192ul{witnessed x p256_g_pow2_128_table_lseq_w4 /\ recallable x}

#push-options "--fuel 2 --ifuel 2"
let p256_g_pow2_128_table_w4 :
  x:glbuffer uint64 192ul{witnessed x p256_g_pow2_128_table_lseq_w4 /\ recallable x} =
  createL_global p256_g_pow2_128_table_list_w4
#pop-options

inline_for_extraction noextract
let p256_precomp_g_pow2_128_table_w4 : precomp_table_w4 g_pow2_128 = {
  table_lseq_w4 = p256_g_pow2_128_table_lseq_w4;
  table_lemma_w4 = p256_g_pow2_128_table_lemma_w4;
  table_w4 = p256_g_pow2_128_table_w4
}


///  window size = 4; precomputed table = [[0]([pow2 192]G), [1]([pow2 192]G),...,[15]([pow2 192]G)]

inline_for_extraction noextract
let p256_g_pow2_192_table_list_w4: x:list uint64{FStar.List.Tot.length x = 192} =
  normalize_term (SPT.precomp_base_table_list mk_pcurve_precomp_base_table proj_g_pow2_192 15)
  
noextract
let p256_g_pow2_192_table_lseq_w4 : LSeq.lseq uint64 192 =
  normalize_term_spec (SPT.precomp_base_table_list mk_pcurve_precomp_base_table proj_g_pow2_192 15);
  Seq.seq_of_list p256_g_pow2_192_table_list_w4

noextract
val p256_g_pow2_192_table_lemma_w4: unit ->
  Lemma (forall (i:nat{i < 16}). precomp_table_acc_inv g_pow2_192 16 p256_g_pow2_192_table_lseq_w4 i)

noextract
let p256_g_pow2_192_table_lemma_w4 () =
  normalize_term_spec (SPT.precomp_base_table_list mk_pcurve_precomp_base_table proj_g_pow2_192 15);
  SPT.precomp_base_table_lemma mk_pcurve_precomp_base_table
    proj_g_pow2_192 16 p256_g_pow2_192_table_lseq_w4;
  proj_g_pow2_192_lemma ()


val p256_g_pow2_192_table_w4 :
  x:glbuffer uint64 192ul{witnessed x p256_g_pow2_192_table_lseq_w4 /\ recallable x}

#push-options "--fuel 2 --ifuel 2"
let p256_g_pow2_192_table_w4 :
  x:glbuffer uint64 192ul{witnessed x p256_g_pow2_192_table_lseq_w4 /\ recallable x} =
  createL_global p256_g_pow2_192_table_list_w4
#pop-options

inline_for_extraction noextract
let p256_precomp_g_pow2_192_table_w4 : precomp_table_w4 g_pow2_192 = {
  table_lseq_w4 = p256_g_pow2_192_table_lseq_w4;
  table_lemma_w4 = p256_g_pow2_192_table_lemma_w4;
  table_w4 = p256_g_pow2_192_table_w4
}


///  window size = 5; precomputed table = [[0]G, [1]G, ..., [31]G]

inline_for_extraction noextract
let p256_basepoint_table_list_w5 :
    x:list uint64{FStar.List.Tot.length x = 384} =
  normalize_term (SPT.precomp_base_table_list mk_pcurve_precomp_base_table S.base_point 31)

noextract
let p256_basepoint_table_lseq_w5 : LSeq.lseq uint64 384 =
  normalize_term_spec (SPT.precomp_base_table_list mk_pcurve_precomp_base_table S.base_point 31);
  Seq.seq_of_list p256_basepoint_table_list_w5

noextract
val p256_basepoint_table_lemma_w5: unit ->
  Lemma ((forall (i:nat{i < 32}). precomp_table_acc_inv g_aff 32
         p256_basepoint_table_lseq_w5 i))

let p256_basepoint_table_lemma_w5 () =
  normalize_term_spec (SPT.precomp_base_table_list mk_pcurve_precomp_base_table S.base_point 31);
  SPT.precomp_base_table_lemma mk_pcurve_precomp_base_table S.base_point 32 p256_basepoint_table_lseq_w5

val p256_basepoint_table_w5:
  x:glbuffer uint64 384ul{witnessed x p256_basepoint_table_lseq_w5 /\ recallable x}

#push-options "--fuel 2 --ifuel 2"
let p256_basepoint_table_w5:
  x:glbuffer uint64 384ul{witnessed x p256_basepoint_table_lseq_w5 /\ recallable x} =
  createL_global p256_basepoint_table_list_w5
#pop-options

noextract
let p256_precomp_basepoint_table_w5 : precomp_table_w5 g_aff = {
  table_lseq_w5 = p256_basepoint_table_lseq_w5;
  table_lemma_w5 = p256_basepoint_table_lemma_w5;
  table_w5 = p256_basepoint_table_w5
}


///////////////////////////////////

inline_for_extraction noextract
instance p256_precomp_tables: precomp_tables = {
  g_points = p256_precomp_g_points;
  basepoint_w4 = p256_precomp_basepoint_table_w4;
  g_pow2_64_w4 = p256_precomp_g_pow2_64_table_w4;
  g_pow2_128_w4 = p256_precomp_g_pow2_128_table_w4;
  g_pow2_192_w4 = p256_precomp_g_pow2_192_table_w4;
  basepoint_w5 = p256_precomp_basepoint_table_w5;
}



