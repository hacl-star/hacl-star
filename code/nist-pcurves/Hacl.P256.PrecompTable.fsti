module Hacl.P256.PrecompTable

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

module S = Spec.P256
module SM = Hacl.Spec.P256.Montgomery

open Hacl.Impl.P256.Point
include Hacl.Impl.P256.Group

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val proj_point_to_list: {| cp:S.curve_params |} -> p:S.proj_point
  -> x:list uint64{FStar.List.Tot.length x = 3 * v cp.bn_limbs /\
    mk_to_p256_comm_monoid.BE.linv (Seq.seq_of_list x)}

val lemma_refl: {| cp:S.curve_params |} -> x:S.proj_point ->
  Lemma (S.mk_p256_concrete_ops.SE.to.SE.refl x ==
    mk_to_p256_comm_monoid.BE.refl (Seq.seq_of_list (proj_point_to_list x)))

inline_for_extraction noextract
let mk_p256_precomp_base_table {| cp:S.curve_params |} : SPT.mk_precomp_base_table S.proj_point U64 (3ul *. cp.bn_limbs) 0ul = {
  SPT.concr_ops = S.mk_p256_concrete_ops;
  SPT.to_cm = mk_to_p256_comm_monoid;
  SPT.to_list = proj_point_to_list;
  SPT.lemma_refl = lemma_refl;
}

inline_for_extraction noextract
let pow_point {| cp:S.curve_params |} (k:nat) (p:S.aff_point) =
  LE.pow S.mk_p256_comm_monoid p k

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

inline_for_extraction noextract
val proj_g_pow2_64_lseq {| cp:S.curve_params |} : LSeq.lseq uint64 (3 * v cp.bn_limbs)

inline_for_extraction noextract
val proj_g_pow2_128_lseq {| cp:S.curve_params |} : LSeq.lseq uint64 (3 * v cp.bn_limbs)

inline_for_extraction noextract
val proj_g_pow2_192_lseq{| cp:S.curve_params |}  : LSeq.lseq uint64 (3 * v cp.bn_limbs)

val proj_g_pow2_64_lseq_lemma: {| cp:S.curve_params |} ->
  Lemma (point_inv_seq proj_g_pow2_64_lseq /\
    S.to_aff_point (from_mont_point (as_point_nat_seq proj_g_pow2_64_lseq)) == g_pow2_64)

val proj_g_pow2_128_lseq_lemma: {| cp:S.curve_params |} ->
  Lemma (point_inv_seq proj_g_pow2_128_lseq /\
    S.to_aff_point (from_mont_point (as_point_nat_seq proj_g_pow2_128_lseq)) == g_pow2_128)

val proj_g_pow2_192_lseq_lemma: {| cp:S.curve_params |} ->
  Lemma (point_inv_seq proj_g_pow2_192_lseq /\
    S.to_aff_point (from_mont_point (as_point_nat_seq proj_g_pow2_192_lseq)) == g_pow2_192)

inline_for_extraction
val mk_proj_g_pow2_64: {| cp:S.curve_params |}  -> StackInline (lbuffer uint64 (3ul *. cp.bn_limbs))
  (requires fun _ -> True)
  (ensures  fun h0 b h1 -> live h1 b /\ stack_allocated b h0 h1 proj_g_pow2_64_lseq)

inline_for_extraction
val mk_proj_g_pow2_128: {| cp:S.curve_params |}  -> StackInline (lbuffer uint64 (3ul *. cp.bn_limbs))
  (requires fun _ -> True)
  (ensures  fun h0 b h1 -> live h1 b /\ stack_allocated b h0 h1 proj_g_pow2_128_lseq)

inline_for_extraction
val mk_proj_g_pow2_192: {| cp:S.curve_params |}  -> StackInline (lbuffer uint64 (3ul *. cp.bn_limbs))
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
  point_inv_seq bj /\ S.to_aff_point (from_mont_point (as_point_nat_seq bj)) == pow_point j p


///  window size = 4; precomputed table = [[0]G, [1]G, ..., [15]G]

inline_for_extraction noextract
val precomp_basepoint_table_lseq_w4 {| cp:S.curve_params |} : LSeq.lseq uint64 (48 * v cp.bn_limbs)

val precomp_basepoint_table_lemma_w4: {| cp:S.curve_params |} ->
  Lemma ((forall (i:nat{i < 16}). precomp_table_acc_inv g_aff 16 precomp_basepoint_table_lseq_w4 i))

val precomp_basepoint_table_w4 {| cp:S.curve_params |}:
  x:glbuffer uint64 (48ul *. cp.bn_limbs){witnessed x precomp_basepoint_table_lseq_w4 /\ recallable x}


///  window size = 4; precomputed table = [[0]([pow2 64]G), [1]([pow2 64]G), ..., [15]([pow2 64]G)]

inline_for_extraction noextract
val precomp_g_pow2_64_table_lseq_w4 {| cp:S.curve_params |} : LSeq.lseq uint64 (48 * v cp.bn_limbs)

val precomp_g_pow2_64_table_lemma_w4: {| cp:S.curve_params |} ->
  Lemma (forall (i:nat{i < 16}). precomp_table_acc_inv g_pow2_64 16 precomp_g_pow2_64_table_lseq_w4 i)

val precomp_g_pow2_64_table_w4 {| cp:S.curve_params |}:
  x:glbuffer uint64 (48ul *. cp.bn_limbs){witnessed x precomp_g_pow2_64_table_lseq_w4 /\ recallable x}


///  window size = 4; precomputed table = [[0]([pow2 128]G), [1]([pow2 128]G), ..., [15]([pow2 128]G)]

inline_for_extraction noextract
val precomp_g_pow2_128_table_lseq_w4 {| cp:S.curve_params |} : LSeq.lseq uint64 (48 * v cp.bn_limbs)

val precomp_g_pow2_128_table_lemma_w4: {| cp:S.curve_params |} ->
  Lemma (forall (i:nat{i < 16}). precomp_table_acc_inv g_pow2_128 16 precomp_g_pow2_128_table_lseq_w4 i)

val precomp_g_pow2_128_table_w4 {| cp:S.curve_params |}:
  x:glbuffer uint64 (48ul *. cp.bn_limbs){witnessed x precomp_g_pow2_128_table_lseq_w4 /\ recallable x}

///  window size = 4; precomputed table = [[0]([pow2 192]G), [1]([pow2 192]G), ..., [15]([pow2 192]G)]

inline_for_extraction noextract
val precomp_g_pow2_192_table_lseq_w4 {| cp:S.curve_params |} : LSeq.lseq uint64 (48 * v cp.bn_limbs)

val precomp_g_pow2_192_table_lemma_w4: {| cp:S.curve_params |} ->
  Lemma (forall (i:nat{i < 16}). precomp_table_acc_inv g_pow2_192 16 precomp_g_pow2_192_table_lseq_w4 i)

val precomp_g_pow2_192_table_w4 {| cp:S.curve_params |}:
  x:glbuffer uint64 (48ul *. cp.bn_limbs){witnessed x precomp_g_pow2_192_table_lseq_w4 /\ recallable x}

///  window size = 5

inline_for_extraction noextract
val precomp_basepoint_table_lseq_w5 {| cp:S.curve_params |} : LSeq.lseq uint64 (96 * v cp.bn_limbs)

val precomp_basepoint_table_lemma_w5: {| cp:S.curve_params |} ->
  Lemma (forall (i:nat{i < 32}). precomp_table_acc_inv g_aff 32 precomp_basepoint_table_lseq_w5 i)

val precomp_basepoint_table_w5 {| cp:S.curve_params |}:
  x:glbuffer uint64 (96ul *. cp.bn_limbs){witnessed x precomp_basepoint_table_lseq_w5 /\ recallable x}
