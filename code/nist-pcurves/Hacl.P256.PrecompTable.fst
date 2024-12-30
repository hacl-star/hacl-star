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
module SPTK = Hacl.Spec.PCurves.PrecompTable

module S = Spec.PCurves
module SL = Spec.PCurves.Lemmas

open Hacl.Impl.PCurves.Point
include Hacl.Impl.PCurves.Group

module PP = Hacl.Impl.PCurves.PrecompPoints.P256
open Hacl.Impl.PCurves.PrecompTable
open Spec.P256

//----------------


///  window size = 4; precomputed table = [[0]G, [1]G, ..., [15]G]
 
inline_for_extraction noextract
let p256_basepoint_table_list_w4: x:list uint64{FStar.List.Tot.length x = 192} =
  normalize_term (SPT.precomp_base_table_list mk_pcurve_precomp_base_table p256_basepoint 15)
 

inline_for_extraction noextract
let p256_basepoint_table_lseq_w4 : LSeq.lseq uint64 (192) =
  normalize_term_spec (SPT.precomp_base_table_list mk_pcurve_precomp_base_table S.base_point 15);
  Seq.seq_of_list p256_basepoint_table_list_w4 

let _:squash (48 * v p256_params.bn_limbs == 192) = assert_norm (48 * v p256_params.bn_limbs == 192)
let _:squash (48ul *. p256_params.bn_limbs == 192ul) = 
  assert(v (48ul *. p256_params.bn_limbs) == 192)
let _:squash (96ul *. p256_params.bn_limbs == 384ul) = 
  assert(v (96ul *. p256_params.bn_limbs) == 384)


noextract
val p256_basepoint_table_lemma_w4: unit ->
  Lemma ((forall (i:nat{i < 16}). precomp_table_acc_inv g_aff 16
         p256_basepoint_table_lseq_w4 i))

#push-options "--z3rlimit 100"
noextract
let p256_basepoint_table_lemma_w4 () =
  normalize_term_spec (SPT.precomp_base_table_list mk_pcurve_precomp_base_table S.base_point 15);
  SPT.precomp_base_table_lemma #_ #_ #(3ul*.4ul) mk_pcurve_precomp_base_table S.base_point 16 p256_basepoint_table_lseq_w4
#pop-options

val p256_basepoint_table_w4:
  x:glbuffer uint64 192ul{witnessed x p256_basepoint_table_lseq_w4 /\ recallable x}

#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
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
  normalize_term (SPT.precomp_base_table_list mk_pcurve_precomp_base_table PP.proj_g_pow2_64 15)

#push-options "--z3rlimit 100"
inline_for_extraction noextract
let p256_g_pow2_64_table_lseq_w4 : LSeq.lseq uint64 192 =
  normalize_term_spec (SPT.precomp_base_table_list mk_pcurve_precomp_base_table PP.proj_g_pow2_64 15);
  Seq.seq_of_list p256_g_pow2_64_table_list_w4
#pop-options

noextract
val p256_g_pow2_64_table_lemma_w4: unit ->
  Lemma (forall (i:nat{i < 16}). precomp_table_acc_inv g_pow2_64 16 p256_g_pow2_64_table_lseq_w4 i)

noextract
let p256_g_pow2_64_table_lemma_w4 () =
  normalize_term_spec (SPT.precomp_base_table_list mk_pcurve_precomp_base_table PP.proj_g_pow2_64 15);
  SPT.precomp_base_table_lemma mk_pcurve_precomp_base_table
    PP.proj_g_pow2_64 16 p256_g_pow2_64_table_lseq_w4;
  PP.proj_g_pow2_64_lemma ()


val p256_g_pow2_64_table_w4 :
  x:glbuffer uint64 192ul{witnessed x p256_g_pow2_64_table_lseq_w4 /\ recallable x}

#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
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
  normalize_term (SPT.precomp_base_table_list mk_pcurve_precomp_base_table PP.proj_g_pow2_128 15)

inline_for_extraction noextract
let p256_g_pow2_128_table_lseq_w4 : LSeq.lseq uint64 192 =
  normalize_term_spec (SPT.precomp_base_table_list mk_pcurve_precomp_base_table PP.proj_g_pow2_128 15);
  Seq.seq_of_list p256_g_pow2_128_table_list_w4

noextract
val p256_g_pow2_128_table_lemma_w4: unit ->
  Lemma (forall (i:nat{i < 16}). precomp_table_acc_inv g_pow2_128 16 p256_g_pow2_128_table_lseq_w4 i)

noextract
let p256_g_pow2_128_table_lemma_w4 () =
  normalize_term_spec (SPT.precomp_base_table_list mk_pcurve_precomp_base_table PP.proj_g_pow2_128 15);
  SPT.precomp_base_table_lemma mk_pcurve_precomp_base_table
    PP.proj_g_pow2_128 16 p256_g_pow2_128_table_lseq_w4;
  PP.proj_g_pow2_128_lemma ()


val p256_g_pow2_128_table_w4 :
  x:glbuffer uint64 192ul{witnessed x p256_g_pow2_128_table_lseq_w4 /\ recallable x}

#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
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
  normalize_term (SPT.precomp_base_table_list mk_pcurve_precomp_base_table PP.proj_g_pow2_192 15)
  
inline_for_extraction noextract
let p256_g_pow2_192_table_lseq_w4 : LSeq.lseq uint64 192 =
  normalize_term_spec (SPT.precomp_base_table_list mk_pcurve_precomp_base_table PP.proj_g_pow2_192 15);
  Seq.seq_of_list p256_g_pow2_192_table_list_w4

noextract
val p256_g_pow2_192_table_lemma_w4: unit ->
  Lemma (forall (i:nat{i < 16}). precomp_table_acc_inv g_pow2_192 16 p256_g_pow2_192_table_lseq_w4 i)

noextract
let p256_g_pow2_192_table_lemma_w4 () =
  normalize_term_spec (SPT.precomp_base_table_list mk_pcurve_precomp_base_table PP.proj_g_pow2_192 15);
  SPT.precomp_base_table_lemma mk_pcurve_precomp_base_table
    PP.proj_g_pow2_192 16 p256_g_pow2_192_table_lseq_w4;
  PP.proj_g_pow2_192_lemma ()


val p256_g_pow2_192_table_w4 :
  x:glbuffer uint64 192ul{witnessed x p256_g_pow2_192_table_lseq_w4 /\ recallable x}

#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
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

inline_for_extraction noextract
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

#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
let p256_basepoint_table_w5:
  x:glbuffer uint64 384ul{witnessed x p256_basepoint_table_lseq_w5 /\ recallable x} =
  createL_global p256_basepoint_table_list_w5
#pop-options

inline_for_extraction noextract
let p256_precomp_basepoint_table_w5 : precomp_table_w5 g_aff = {
  table_lseq_w5 = p256_basepoint_table_lseq_w5;
  table_lemma_w5 = p256_basepoint_table_lemma_w5;
  table_w5 = p256_basepoint_table_w5
}

open Hacl.Impl.PCurves.Constants.P256
open Hacl.Impl.PCurves.Bignum.P256
open Hacl.Impl.PCurves.Field.P256
open Hacl.Impl.PCurves.Finv.P256
open Hacl.Impl.PCurves.Qinv.P256
open Hacl.Impl.PCurves.Group.P256

[@CInline]
val precomp_get_consttime: precomp_get_consttime_t
let precomp_get_consttime = precomp_get_consttime_gen

///////////////////////////////////

inline_for_extraction noextract
instance p256_precomp_tables: precomp_tables = {
  mk_proj_g_pow2_64 = PP.g_pow2_64_table;
  mk_proj_g_pow2_128 = PP.g_pow2_128_table;
  mk_proj_g_pow2_192 = PP.g_pow2_192_table;
  basepoint_w4 = p256_precomp_basepoint_table_w4;
  g_pow2_64_w4 = p256_precomp_g_pow2_64_table_w4;
  g_pow2_128_w4 = p256_precomp_g_pow2_128_table_w4;
  g_pow2_192_w4 = p256_precomp_g_pow2_192_table_w4;
  basepoint_w5 = p256_precomp_basepoint_table_w5;
  precomp_get_consttime
}



