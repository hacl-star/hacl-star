module Vale.AES.Types_helpers

open Vale.Def.Words.Seq_s
open Vale.Def.Words.Four_s
open Vale.Def.Types_s
open Vale.Arch.Types
open FStar.Seq
open Vale.Arch.TypesNative

let lemma_slices_le_quad32_to_bytes (q:quad32) : Lemma
  (ensures (
    let s = le_quad32_to_bytes q in
    q.lo0 == four_to_nat 8 (seq_to_four_LE (slice s 0 4)) /\
    q.lo1 == four_to_nat 8 (seq_to_four_LE (slice s 4 8)) /\
    q.hi2 == four_to_nat 8 (seq_to_four_LE (slice s 8 12)) /\
    q.hi3 == four_to_nat 8 (seq_to_four_LE (slice s 12 16))
  ))
  =
  reveal_opaque (`%seq_four_to_seq_LE) (seq_four_to_seq_LE #nat8);
  reveal_opaque (`%le_quad32_to_bytes) le_quad32_to_bytes;
  ()

let lemma_slices_be_quad32_to_bytes (q:quad32) : Lemma
  (ensures (
    let s = be_quad32_to_bytes q in
    q.hi3 == four_to_nat 8 (seq_to_four_BE (slice s 0 4)) /\
    q.hi2 == four_to_nat 8 (seq_to_four_BE (slice s 4 8)) /\
    q.lo1 == four_to_nat 8 (seq_to_four_BE (slice s 8 12)) /\
    q.lo0 == four_to_nat 8 (seq_to_four_BE (slice s 12 16))
  ))
  =
  reveal_opaque (`%seq_four_to_seq_BE) (seq_four_to_seq_BE #nat8);
  reveal_opaque (`%be_quad32_to_bytes) be_quad32_to_bytes;
  ()

let lemma_BitwiseXorWithZero64 n =
  lemma_ixor_nth_all 64;
  lemma_zero_nth 64;
  lemma_equal_nth 64 (ixor n 0) n
