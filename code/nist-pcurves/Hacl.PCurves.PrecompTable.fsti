module Hacl.PCurves.PrecompTable

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

module LE = Lib.Exponentiation.Definition
module SE = Spec.Exponentiation
module BE = Hacl.Impl.Exponentiation.Definitions
module SPT = Hacl.Spec.PrecompBaseTable
module SPTK = Hacl.Spec.PCurves.PrecompTable

module S = Spec.PCurves
module SM = Hacl.Spec.PCurves.Montgomery

open Hacl.Impl.PCurves.Point
include Hacl.Impl.PCurves.Group

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val proj_point_to_list: {| cp:S.curve_params |} -> p:S.proj_point
  -> x:list uint64{FStar.List.Tot.length x = 3 * v cp.bn_limbs /\
    mk_to_pcurve_comm_monoid.BE.linv (Seq.seq_of_list x)}

val lemma_refl: {| cp:S.curve_params |} -> x:S.proj_point ->
  Lemma (S.mk_pcurve_concrete_ops.SE.to.SE.refl x ==
    mk_to_pcurve_comm_monoid.BE.refl (Seq.seq_of_list (proj_point_to_list x)))

inline_for_extraction noextract
let mk_pcurve_precomp_base_table {| cp:S.curve_params |} : SPT.mk_precomp_base_table S.proj_point U64 (3ul *. cp.bn_limbs) 0ul = {
  SPT.concr_ops = S.mk_pcurve_concrete_ops;
  SPT.to_cm = mk_to_pcurve_comm_monoid;
    SPT.to_list = proj_point_to_list;
  SPT.lemma_refl = lemma_refl;
}

inline_for_extraction noextract
let pow_point {| cp:S.curve_params |} (k:nat) (p:S.aff_point) =
  LE.pow S.mk_pcurve_comm_monoid p k

//----------------

noextract
let g_aff {| cp:S.curve_params |} : S.aff_point = S.to_aff_point S.base_point

// [pow2 64]G
noextract
let g_pow2_64 {| cp:S.curve_params |} : S.aff_point = pow_point (pow2 64) g_aff

// [pow2 128]G
noextract
let g_pow2_128 {| cp:S.curve_params |} : S.aff_point = pow_point (pow2 128) g_aff

// [pow2 192]G
noextract
let g_pow2_192 {| cp:S.curve_params |} : S.aff_point = pow_point (pow2 192) g_aff

class precomp_g_points {| cp:S.curve_params |} = {
  proj_g_pow2_64: S.proj_point;
  lemma_proj_g_pow2_64_eval : unit ->
  Lemma (SE.exp_pow2 S.mk_pcurve_concrete_ops S.base_point 64 == proj_g_pow2_64);
  proj_g_pow2_128 : S.proj_point;
  lemma_proj_g_pow2_128_eval: unit ->
  Lemma (SE.exp_pow2 S.mk_pcurve_concrete_ops proj_g_pow2_64 64 == proj_g_pow2_128);
  proj_g_pow2_192 : S.proj_point;
  lemma_proj_g_pow2_192_eval : unit ->
  Lemma (SE.exp_pow2 S.mk_pcurve_concrete_ops proj_g_pow2_128 64 == proj_g_pow2_192);
}


inline_for_extraction noextract
val proj_g_pow2_64_lseq {| cp:S.curve_params |} {| precomp_g_points |} : LSeq.lseq uint64 (3 * v cp.bn_limbs)

inline_for_extraction noextract
val proj_g_pow2_128_lseq {| cp:S.curve_params |} {| precomp_g_points |} : LSeq.lseq uint64 (3 * v cp.bn_limbs)

inline_for_extraction noextract
val proj_g_pow2_192_lseq{| cp:S.curve_params |}  {| precomp_g_points |} : LSeq.lseq uint64 (3 * v cp.bn_limbs)

noextract
val proj_g_pow2_64_lemma {| cp:S.curve_params |} {| p:precomp_g_points |} : unit ->
  Lemma (S.to_aff_point proj_g_pow2_64 == pow_point (pow2 64) g_aff)

noextract
val proj_g_pow2_128_lemma {| cp:S.curve_params |} {| p:precomp_g_points |} : unit ->
  Lemma (S.to_aff_point proj_g_pow2_128 == pow_point (pow2 128) g_aff)


noextract
val proj_g_pow2_192_lemma {| cp:S.curve_params |} {| p:precomp_g_points |} : unit ->
  Lemma (S.to_aff_point proj_g_pow2_192 == pow_point (pow2 192) g_aff)


noextract
val proj_g_pow2_64_lseq_lemma {| cp:S.curve_params |} {| precomp_g_points |}: unit ->
  Lemma (point_inv_seq proj_g_pow2_64_lseq /\
    S.to_aff_point (from_mont_point (as_point_nat_seq proj_g_pow2_64_lseq)) == g_pow2_64)

noextract
val proj_g_pow2_128_lseq_lemma {| cp:S.curve_params |} {| precomp_g_points |}: unit ->
  Lemma (point_inv_seq proj_g_pow2_128_lseq /\
    S.to_aff_point (from_mont_point (as_point_nat_seq proj_g_pow2_128_lseq)) == g_pow2_128)

noextract
val proj_g_pow2_192_lseq_lemma {| cp:S.curve_params |} {| precomp_g_points |}: unit ->
  Lemma (point_inv_seq proj_g_pow2_192_lseq /\
    S.to_aff_point (from_mont_point (as_point_nat_seq proj_g_pow2_192_lseq)) == g_pow2_192)

inline_for_extraction
val mk_proj_g_pow2_64 {| cp:S.curve_params |} {| precomp_g_points |}: unit -> StackInline (lbuffer uint64 (3ul *. cp.bn_limbs))
  (requires fun _ -> True)
  (ensures  fun h0 b h1 -> live h1 b /\ stack_allocated b h0 h1 proj_g_pow2_64_lseq)

inline_for_extraction
val mk_proj_g_pow2_128 {| cp:S.curve_params |} {| precomp_g_points |}: unit -> StackInline (lbuffer uint64 (3ul *. cp.bn_limbs))
  (requires fun _ -> True)
  (ensures  fun h0 b h1 -> live h1 b /\ stack_allocated b h0 h1 proj_g_pow2_128_lseq)

inline_for_extraction
val mk_proj_g_pow2_192 {| cp:S.curve_params |} {| precomp_g_points |}: unit -> StackInline (lbuffer uint64 (3ul *. cp.bn_limbs))
  (requires fun _ -> True)
  (ensures  fun h0 b h1 -> live h1 b /\ stack_allocated b h0 h1 proj_g_pow2_192_lseq)

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

noeq type precomp_table_w4 {| cp:S.curve_params |} (p:S.aff_point #cp) = {
  table_lseq_w4: (LSeq.lseq uint64 (48 * v cp.bn_limbs));
  table_lemma_w4: unit ->
  Lemma ((forall (i:nat{i < 16}). precomp_table_acc_inv p 16 table_lseq_w4 i));
  table_w4: x:glbuffer uint64 (48ul *. cp.bn_limbs){witnessed x table_lseq_w4 /\ recallable x}
}

noeq type precomp_table_w5 {| cp:S.curve_params |} (p:S.aff_point #cp) = {
  table_lseq_w5: (LSeq.lseq uint64 (96 * v cp.bn_limbs));
  table_lemma_w5: unit ->
  Lemma ((forall (i:nat{i < 32}). precomp_table_acc_inv p 32 table_lseq_w5 i));
  table_w5: x:glbuffer uint64 (96ul *. cp.bn_limbs){witnessed x table_lseq_w5 /\ recallable x}
}

class precomp_tables {| S.curve_params |} = {
  g_points : precomp_g_points;
  basepoint_w4: precomp_table_w4 g_aff;
  g_pow2_64_w4: precomp_table_w4 g_pow2_64;  
  g_pow2_128_w4: precomp_table_w4 g_pow2_128;  
  g_pow2_192_w4: precomp_table_w4 g_pow2_192;  
  basepoint_w5: precomp_table_w5 g_aff;
}
