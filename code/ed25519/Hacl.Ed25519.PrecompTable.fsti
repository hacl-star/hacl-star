module Hacl.Ed25519.PrecompTable

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum25519
module F51 = Hacl.Impl.Ed25519.Field51

module LSeq = Lib.Sequence
module LE = Lib.Exponentiation.Definition
module SE = Spec.Exponentiation
module BE = Hacl.Impl.Exponentiation
module SPT = Hacl.Spec.PrecompBaseTable

module S = Spec.Ed25519
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
let pow_point (k:nat) (p:S.aff_point_c) =
  LE.pow S.mk_ed25519_comm_monoid p k

//----------------

noextract
let g_aff : S.aff_point_c =
  Spec.Ed25519.Lemmas.g_is_on_curve ();
  S.to_aff_point S.g

// [pow2 64]G
noextract
let g_pow2_64 : S.aff_point = pow_point (pow2 64) g_aff

// [pow2 128]G
noextract
let g_pow2_128 : S.aff_point = pow_point (pow2 128) g_aff

// [pow2 192]G
noextract
let g_pow2_192 : S.aff_point = pow_point (pow2 192) g_aff

inline_for_extraction noextract
val ext_g_pow2_64_lseq : LSeq.lseq uint64 20

inline_for_extraction noextract
val ext_g_pow2_128_lseq : LSeq.lseq uint64 20

inline_for_extraction noextract
val ext_g_pow2_192_lseq : LSeq.lseq uint64 20

val ext_g_pow2_64_lseq_lemma: unit ->
  Lemma (F51.linv ext_g_pow2_64_lseq /\ refl ext_g_pow2_64_lseq == g_pow2_64)

val ext_g_pow2_128_lseq_lemma: unit ->
  Lemma (F51.linv ext_g_pow2_128_lseq /\ refl ext_g_pow2_128_lseq == g_pow2_128)

val ext_g_pow2_192_lseq_lemma: unit ->
  Lemma (F51.linv ext_g_pow2_192_lseq /\ refl ext_g_pow2_192_lseq == g_pow2_192)

inline_for_extraction
val mk_ext_g_pow2_64: unit -> StackInline (lbuffer uint64 20ul)
  (requires fun _ -> True)
  (ensures  fun h0 b h1 -> live h1 b /\ stack_allocated b h0 h1 ext_g_pow2_64_lseq)

inline_for_extraction
val mk_ext_g_pow2_128: unit -> StackInline (lbuffer uint64 20ul)
  (requires fun _ -> True)
  (ensures  fun h0 b h1 -> live h1 b /\ stack_allocated b h0 h1 ext_g_pow2_128_lseq)

inline_for_extraction
val mk_ext_g_pow2_192: unit -> StackInline (lbuffer uint64 20ul)
  (requires fun _ -> True)
  (ensures  fun h0 b h1 -> live h1 b /\ stack_allocated b h0 h1 ext_g_pow2_192_lseq)

//----------------

unfold
let precomp_table_acc_inv
  (p:S.aff_point_c)
  (table_len:nat{table_len * 20 <= max_size_t})
  (table:LSeq.lseq uint64 (table_len * 20))
  (j:nat{j < table_len})
=
  Math.Lemmas.lemma_mult_lt_right 20 j table_len;
  Math.Lemmas.lemma_mult_le_right 20 (j + 1) table_len;
  let bj = LSeq.sub table (j * 20) 20 in
  F51.linv bj /\ refl bj == pow_point j p


///  window size = 4; precomputed table = [[0]G, [1]G, ..., [15]G]

inline_for_extraction noextract
val precomp_basepoint_table_lseq_w4 : LSeq.lseq uint64 320

val precomp_basepoint_table_lemma_w4: unit ->
  Lemma (forall (i:nat{i < 16}). precomp_table_acc_inv g_aff 16 precomp_basepoint_table_lseq_w4 i)

val precomp_basepoint_table_w4:
  x:glbuffer uint64 320ul{witnessed x precomp_basepoint_table_lseq_w4 /\ recallable x}


///  window size = 4; precomputed table = [[0]([pow2 64]G), [1]([pow2 64]G), ..., [15]([pow2 64]G)]

inline_for_extraction noextract
val precomp_g_pow2_64_table_lseq_w4 : LSeq.lseq uint64 320

val precomp_g_pow2_64_table_lemma_w4: unit ->
  Lemma (forall (i:nat{i < 16}). precomp_table_acc_inv g_pow2_64 16 precomp_g_pow2_64_table_lseq_w4 i)

val precomp_g_pow2_64_table_w4:
  x:glbuffer uint64 320ul{witnessed x precomp_g_pow2_64_table_lseq_w4 /\ recallable x}


///  window size = 4; precomputed table = [[0]([pow2 128]G), [1]([pow2 128]G),...,[15]([pow2 128]G)]

inline_for_extraction noextract
val precomp_g_pow2_128_table_lseq_w4 : LSeq.lseq uint64 320

val precomp_g_pow2_128_table_lemma_w4: unit ->
  Lemma (forall (i:nat{i < 16}). precomp_table_acc_inv g_pow2_128 16 precomp_g_pow2_128_table_lseq_w4 i)

val precomp_g_pow2_128_table_w4:
  x:glbuffer uint64 320ul{witnessed x precomp_g_pow2_128_table_lseq_w4 /\ recallable x}

///  window size = 4; precomputed table = [[0]([pow2 192]G), [1]([pow2 192]G),...,[15]([pow2 192]G)]

inline_for_extraction noextract
val precomp_g_pow2_192_table_lseq_w4 : LSeq.lseq uint64 320

val precomp_g_pow2_192_table_lemma_w4: unit ->
  Lemma (forall (i:nat{i < 16}). precomp_table_acc_inv g_pow2_192 16 precomp_g_pow2_192_table_lseq_w4 i)

val precomp_g_pow2_192_table_w4:
  x:glbuffer uint64 320ul{witnessed x precomp_g_pow2_192_table_lseq_w4 /\ recallable x}


///  window size = 5

inline_for_extraction noextract
val precomp_basepoint_table_lseq_w5 : LSeq.lseq uint64 640

val precomp_basepoint_table_lemma_w5: unit ->
  Lemma (forall (i:nat{i < 32}). precomp_table_acc_inv g_aff 32 precomp_basepoint_table_lseq_w5 i)

val precomp_basepoint_table_w5:
  x:glbuffer uint64 640ul{witnessed x precomp_basepoint_table_lseq_w5 /\ recallable x}
