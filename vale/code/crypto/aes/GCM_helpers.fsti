module GCM_helpers

open Words_s
open Words.Seq_s
open Words.Four_s
open Types_s
open Arch.Types
open FStar.Mul
open FStar.Seq
open AES_s
open GCTR_s
open FStar.Math.Lemmas
open Collections.Seqs
open Workarounds

val reveal_le_bytes_to_seq_quad32 (_:unit) : Lemma
  (forall (b:seq nat8).{:pattern le_bytes_to_seq_quad32 b} length b % 16 == 0 ==> le_bytes_to_seq_quad32 b == seq_to_seq_four_LE (seq_nat8_to_seq_nat32_LE b))

let bytes_to_quad_size (num_bytes:nat) =
  ((num_bytes + 15) / 16)

val bytes_to_quad_size_no_extra_bytes (num_bytes:nat) : Lemma
  (requires num_bytes % 16 == 0)
  (ensures bytes_to_quad_size num_bytes = num_bytes / 16)

val no_extra_bytes_helper (s:seq quad32) (num_bytes:int) : Lemma
  (requires 0 <= num_bytes /\
            num_bytes % 16 == 0 /\
            length s == bytes_to_quad_size num_bytes)
  (ensures slice (le_seq_quad32_to_bytes s) 0 num_bytes == le_seq_quad32_to_bytes s /\
           slice_work_around s (num_bytes / 16) == s)

val le_seq_quad32_to_bytes_tail_prefix (s:seq quad32) (num_bytes:nat) : Lemma
  (requires (1 <= num_bytes /\
             num_bytes < 16 * length s /\
             16 * (length s - 1) < num_bytes /\
             num_bytes % 16 <> 0))
  (ensures (let num_extra = num_bytes % 16 in
            let num_blocks = num_bytes / 16 in
            let x  = slice (le_seq_quad32_to_bytes s) (num_blocks * 16) num_bytes in
            let x' = slice (le_quad32_to_bytes (index s num_blocks)) 0 num_extra in
            x == x'))

val pad_to_128_bits_le_quad32_to_bytes (s:seq quad32) (num_bytes:int) : Lemma
  (requires 1 <= num_bytes /\
             num_bytes < 16 * length s /\
             16 * (length s - 1) < num_bytes /\
             num_bytes % 16 <> 0 /\
             length s == bytes_to_quad_size num_bytes)
  (ensures (let num_blocks = num_bytes / 16 in
            let full_quads,final_quads = split s num_blocks in
            length final_quads == 1 /\
            (let final_quad = index final_quads 0 in
             pad_to_128_bits (slice (le_seq_quad32_to_bytes s) 0 num_bytes)
             ==
             le_seq_quad32_to_bytes full_quads @| pad_to_128_bits (slice (le_quad32_to_bytes final_quad) 0 (num_bytes % 16)))))

val le_quad32_to_bytes_sel (q : quad32) (i:nat{i < 16}) :
    Lemma(let Mkfour q0 q1 q2 q3 = q in
              (i < 4 ==> index (le_quad32_to_bytes q) i = four_select (nat_to_four 8 q0) (i % 4)) /\
              (4 <= i /\ i < 8 ==> index (le_quad32_to_bytes q) i = four_select (nat_to_four 8 q1) (i % 4)) /\
               (8 <= i /\ i < 12  ==> index (le_quad32_to_bytes q) i = four_select (nat_to_four 8 q2) (i % 4)) /\
              (12 <= i /\ i < 16 ==> index (le_quad32_to_bytes q) i = four_select (nat_to_four 8 q3) (i % 4)))

val pad_to_128_bits_lower (q:quad32) (num_bytes:int) : Lemma
  (requires 1 <= num_bytes /\ num_bytes < 8)
  (ensures (let new_lo = (lo64 q) % pow2 (num_bytes * 8) in
            new_lo < pow2_64 /\
            (let q' = insert_nat64_opaque (insert_nat64_opaque q 0 1) new_lo 0 in
             q' == le_bytes_to_quad32 (pad_to_128_bits (slice (le_quad32_to_bytes q) 0 num_bytes)))))

val pad_to_128_bits_upper (q:quad32) (num_bytes:int) : Lemma
  (requires 8 <= num_bytes /\ num_bytes < 16)
  (ensures (let new_hi = (hi64 q) % pow2 ((num_bytes - 8) * 8) in
            new_hi < pow2_64 /\
            (let q' = insert_nat64_opaque q new_hi 1 in
             q' == le_bytes_to_quad32 (pad_to_128_bits (slice (le_quad32_to_bytes q) 0 num_bytes)))))


