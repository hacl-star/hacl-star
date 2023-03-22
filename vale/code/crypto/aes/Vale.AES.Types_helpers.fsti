module Vale.AES.Types_helpers

open Vale.Def.Words_s
open Vale.Def.Words.Seq_s
open Vale.Def.Words.Four_s
open Vale.Def.Types_s
open Vale.Arch.Types
open FStar.Mul
open FStar.Seq
open Vale.Lib.Seqs

unfold let pow2_24 = 0x1000000
let nat24 = natN pow2_24

val lemma_slices_le_quad32_to_bytes (q:quad32) : Lemma
  (ensures (
    let s = le_quad32_to_bytes q in
    q.lo0 == four_to_nat 8 (seq_to_four_LE (slice s 0 4)) /\
    q.lo1 == four_to_nat 8 (seq_to_four_LE (slice s 4 8)) /\
    q.hi2 == four_to_nat 8 (seq_to_four_LE (slice s 8 12)) /\
    q.hi3 == four_to_nat 8 (seq_to_four_LE (slice s 12 16))
  ))

val lemma_slices_be_quad32_to_bytes (q:quad32) : Lemma
  (ensures (
    let s = be_quad32_to_bytes q in
    q.hi3 == four_to_nat 8 (seq_to_four_BE (slice s 0 4)) /\
    q.hi2 == four_to_nat 8 (seq_to_four_BE (slice s 4 8)) /\
    q.lo1 == four_to_nat 8 (seq_to_four_BE (slice s 8 12)) /\
    q.lo0 == four_to_nat 8 (seq_to_four_BE (slice s 12 16))
  ))

val lemma_BitwiseXorWithZero64 (n:nat64) : Lemma (ixor n 0 == n)

let lemma_ishl_64 (x:nat64) (k:nat) : Lemma
  (ensures ishl #pow2_64 x k == x * pow2 k % pow2_64)
  =
  Vale.Def.TypesNative_s.reveal_ishl 64 x k;
  FStar.UInt.shift_left_value_lemma #64 x k;
  ()

let lemma_ishr_64 (x:nat64) (k:nat) : Lemma
  (ensures ishr #pow2_64 x k == x / pow2 k)
  =
  Vale.Def.TypesNative_s.reveal_ishr 64 x k;
  FStar.UInt.shift_right_value_lemma #64 x k;
  ()

let lemma_ishr_32 (x:nat32) (k:nat) : Lemma
  (ensures ishr #pow2_32 x k == x / pow2 k)
  =
  Vale.Def.TypesNative_s.reveal_ishr 32 x k;
  FStar.UInt.shift_right_value_lemma #32 x k;
  ()
