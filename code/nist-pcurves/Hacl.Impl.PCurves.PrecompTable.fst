module Hacl.Impl.PCurves.PrecompTable

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

module LE = Lib.Exponentiation.Definition
module SE = Spec.Exponentiation
module BED = Hacl.Impl.Exponentiation.Definitions
module BE = Hacl.Impl.Exponentiation
module SPT = Hacl.Spec.PrecompBaseTable
module SPTK = Hacl.Spec.PCurves.PrecompTable

module S = Spec.PCurves
module SM = Hacl.Spec.PCurves.Montgomery

open Hacl.Impl.PCurves.Bignum
open Hacl.Impl.PCurves.Constants
open Hacl.Impl.PCurves.Point
include Hacl.Impl.PCurves.Group

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val proj_point_to_list: {| cp:S.curve_params |} -> p:S.proj_point
  -> x:list uint64{FStar.List.Tot.length x = 3 * v cp.bn_limbs /\
    mk_to_pcurve_comm_monoid.BE.linv (Seq.seq_of_list x)}

let proj_point_to_list {| cp:S.curve_params |} p =
  SPTK.proj_point_to_list_lemma p;
  SPTK.proj_point_to_list p

inline_for_extraction noextract
val lemma_refl: {| cp:S.curve_params |} -> x:S.proj_point ->
  Lemma (S.mk_pcurve_concrete_ops.SE.to.SE.refl x ==
    mk_to_pcurve_comm_monoid.BE.refl (Seq.seq_of_list (proj_point_to_list x)))
let lemma_refl {| cp:S.curve_params |} x =
  SPTK.proj_point_to_list_lemma x


inline_for_extraction noextract
let mk_pcurve_precomp_base_table {| cp:S.curve_params |} : SPT.mk_precomp_base_table S.proj_point U64 (3ul *! cp.bn_limbs) 0ul = {
  SPT.concr_ops = S.mk_pcurve_concrete_ops;
  SPT.to_cm = mk_to_pcurve_comm_monoid;
    SPT.to_list = proj_point_to_list;
  SPT.lemma_refl = lemma_refl;
}

inline_for_extraction noextract
let pow_point {| cp:S.curve_params |} (k:nat) (p:S.aff_point) =
  LE.pow S.mk_pcurve_comm_monoid p k

//----------------

inline_for_extraction noextract
let g_aff {| cp:S.curve_params |} : S.aff_point = S.to_aff_point S.base_point

// [pow2 64]G
inline_for_extraction noextract
let g_pow2_64 {| cp:S.curve_params |} : S.aff_point = pow_point (pow2 64) g_aff

// [pow2 128]G
inline_for_extraction noextract
let g_pow2_128 {| cp:S.curve_params |} : S.aff_point = pow_point (pow2 128) g_aff

// [pow2 192]G
inline_for_extraction noextract
let g_pow2_192 {| cp:S.curve_params |} : S.aff_point = pow_point (pow2 192) g_aff

noextract inline_for_extraction
noeq type proj_g_pow2 {| cp:S.curve_params |} (p:S.aff_point #cp) = {
  proj_g_pow2_lseq: LSeq.lseq uint64 (3 * v cp.bn_limbs);
  proj_g_pow2_lseq_lemma: unit ->
  Lemma (point_inv_seq proj_g_pow2_lseq /\
         S.to_aff_point (from_mont_point
           (as_point_nat_seq proj_g_pow2_lseq)) == p);
  mk_proj_g_pow2: unit -> StackInline (lbuffer uint64 (3ul *! cp.bn_limbs))
    (requires fun _ -> True)
    (ensures  fun h0 b h1 -> live h1 b /\ 
              stack_allocated b h0 h1 proj_g_pow2_lseq)
}

//----------------

unfold
let precomp_table_acc_inv {| cp:S.curve_params |} 
  (p:S.aff_point)
  (table_len:nat{table_len * 3 * v cp.bn_limbs <= max_size_t})
  (table:LSeq.lseq uint64 (table_len * 3 * v cp.bn_limbs))
  (j:nat{j < table_len})
=
  Math.Lemmas.lemma_mult_lt_right (3 * v cp.bn_limbs) j table_len;
  Math.Lemmas.lemma_mult_le_right (3 * v cp.bn_limbs) (j + 1) table_len;
  let bj = LSeq.sub table (j * (3 * v cp.bn_limbs)) (3 * v cp.bn_limbs) in
  point_inv_seq bj /\
  S.to_aff_point (from_mont_point (as_point_nat_seq bj)) == pow_point j p

noextract inline_for_extraction
noeq type precomp_table_w4 {| cp:S.curve_params |} (p:S.aff_point #cp) = {
  table_lseq_w4: (LSeq.lseq uint64 (48 * v cp.bn_limbs));
  table_lemma_w4: unit ->
  Lemma ((forall (i:nat{i < 16}). precomp_table_acc_inv p 16 table_lseq_w4 i));
  table_w4: x:glbuffer uint64 (48ul *! cp.bn_limbs){witnessed x table_lseq_w4 /\ recallable x}
}

noextract inline_for_extraction
noeq type precomp_table_w5 {| cp:S.curve_params |} (p:S.aff_point #cp) = {
  table_lseq_w5: (LSeq.lseq uint64 (96 * v cp.bn_limbs));
  table_lemma_w5: unit ->
  Lemma ((forall (i:nat{i < 32}). precomp_table_acc_inv p 32 table_lseq_w5 i));
  table_w5: x:glbuffer uint64 (96ul *! cp.bn_limbs){witnessed x table_lseq_w5 /\ recallable x}
}

open Hacl.Impl.PCurves.Field
open Hacl.Impl.PCurves.InvSqrt
open Hacl.Impl.PCurves.Group

inline_for_extraction noextract
let precomp_get_consttime_t {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt|} {| p:point_ops |} = BE.pow_a_to_small_b_st U64 (3ul *! cp.bn_limbs) 0ul mk_pcurve_concrete_ops 4ul 16ul
    (BE.table_inv_precomp (3ul *! cp.bn_limbs) 0ul mk_pcurve_concrete_ops 4ul 16ul)

inline_for_extraction noextract
val precomp_get_consttime_gen {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt |} {| point_ops |}: precomp_get_consttime_t

let precomp_get_consttime_gen {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt |} ctx a table bits_l tmp =
  [@inline_let] let len = 3ul *! cp.bn_limbs in
  [@inline_let] let ctx_len = 0ul in
  [@inline_let] let k = mk_pcurve_concrete_ops in
  [@inline_let] let l = 4ul in
  [@inline_let] let table_len = 16ul in

  BE.lprecomp_get_consttime len ctx_len k l table_len ctx a table bits_l tmp

inline_for_extraction
class precomp_tables {| S.curve_params |} {| cp:S.curve_params |} {| bn_ops |} {| curve_constants |} {| f:field_ops |} {| curve_inv_sqrt |} {| point_ops |} = {
  mk_proj_g_pow2_64: proj_g_pow2 g_pow2_64;
  mk_proj_g_pow2_128: proj_g_pow2 g_pow2_128;
  mk_proj_g_pow2_192: proj_g_pow2 g_pow2_192;
  basepoint_w4: precomp_table_w4 g_aff;
  g_pow2_64_w4: precomp_table_w4 g_pow2_64;  
  g_pow2_128_w4: precomp_table_w4 g_pow2_128;  
  g_pow2_192_w4: precomp_table_w4 g_pow2_192;  
  basepoint_w5: precomp_table_w5 g_aff;
  precomp_get_consttime: precomp_get_consttime_t
}


//-----------------

