module Vale.AES.GCM_helpers_BE

open Vale.Def.Words_s
open Vale.Def.Words.Seq_s
open Vale.Def.Words.Two_s
open Vale.Def.Words.Four_s
open Vale.Def.Types_s
open Vale.Arch.Types
open FStar.Mul
open FStar.Seq
open Vale.AES.AES_BE_s
open Vale.AES.GCTR_BE_s
open FStar.Math.Lemmas
open Vale.Lib.Seqs

let bytes_to_quad_size (num_bytes:nat) =
  ((num_bytes + 15) / 16)

val no_extra_bytes_helper (s:seq quad32) (num_bytes:int) : Lemma
  (requires 0 <= num_bytes /\
            num_bytes % 16 == 0 /\
            length s == bytes_to_quad_size num_bytes)
  (ensures slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE s)) 0 num_bytes == seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE s) /\
           slice s 0 (num_bytes / 16) == s)

val be_seq_quad32_to_bytes_tail_prefix (s:seq quad32) (num_bytes:nat) : Lemma
  (requires (1 <= num_bytes /\
             num_bytes < 16 * length s /\
             16 * (length s - 1) < num_bytes /\
             num_bytes % 16 <> 0))
  (ensures (let num_extra = num_bytes % 16 in
            let num_blocks = num_bytes / 16 in
            let x  = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE s)) (num_blocks * 16) num_bytes in
            let x' = slice (be_quad32_to_bytes (index s num_blocks)) 0 num_extra in
            x == x'))

val pad_to_128_bits_be_quad32_to_bytes (s:seq quad32) (num_bytes:int) : Lemma
  (requires 1 <= num_bytes /\
             num_bytes < 16 * length s /\
             16 * (length s - 1) < num_bytes /\
             num_bytes % 16 <> 0 /\
             length s == bytes_to_quad_size num_bytes)
  (ensures (let num_blocks = num_bytes / 16 in
            let full_quads,final_quads = split s num_blocks in
            length final_quads == 1 /\
            (let final_quad = index final_quads 0 in
             pad_to_128_bits (slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE s)) 0 num_bytes)
             ==
             seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE full_quads) @| pad_to_128_bits (slice (be_quad32_to_bytes final_quad) 0 (num_bytes % 16)))))

val pad_to_128_bits_upper (q:quad32) (num_bytes:int) : Lemma
  (requires 1 <= num_bytes /\ num_bytes < 8)
  (ensures (let new_hi = (((hi64 q) / pow2 ((8 - num_bytes) * 8)) * pow2 ((8 - num_bytes) * 8)) % pow2_64 in
            (let q' = two_two_to_four (Mktwo (nat_to_two 32 0) (nat_to_two 32 new_hi)) in
             q' == be_bytes_to_quad32 (pad_to_128_bits (slice (be_quad32_to_bytes q) 0 num_bytes)))))

val pad_to_128_bits_lower (q:quad32) (num_bytes:int) : Lemma
  (requires 8 <= num_bytes /\ num_bytes < 16)
  (ensures (let new_lo = (((lo64 q) / pow2 ((16 - num_bytes) * 8)) * pow2 ((16 - num_bytes) * 8)) % pow2_64 in
            (let q' = two_two_to_four (Mktwo (nat_to_two 32 new_lo) (nat_to_two 32 (hi64 q))) in
             q' == be_bytes_to_quad32 (pad_to_128_bits (slice (be_quad32_to_bytes q) 0 num_bytes)))))

val pad_to_128_bits_lower_8 (q:quad32) : Lemma
  (requires True)
  (ensures (let q' = two_two_to_four (Mktwo (nat_to_two 32 0) (nat_to_two 32 (hi64 q))) in
             q' == be_bytes_to_quad32 (pad_to_128_bits (slice (be_quad32_to_bytes q) 0 8))))
