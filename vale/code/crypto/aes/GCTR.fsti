module GCTR

open Opaque_s
open Words_s
open Types_s
open Arch.Types
open FStar.Mul
open FStar.Seq
open AES_s
open GCTR_s
open GCM_helpers
open FStar.Math.Lemmas
open Collections.Seqs

let make_gctr_plain_LE (p:seq nat8) : gctr_plain_LE =
  if 4096 * length p < pow2_32 then p else empty

val gctr_encrypt_block_offset (icb_BE:quad32) (plain_LE:quad32) (alg:algorithm) (key:aes_key_LE alg) (i:int) :
  Lemma (gctr_encrypt_block icb_BE plain_LE alg key i ==
         gctr_encrypt_block (inc32 icb_BE i) plain_LE alg key 0)

val gctr_encrypt_empty (icb_BE:quad32) (plain_LE cipher_LE:seq quad32) (alg:algorithm) (key:aes_key_LE alg) :
  Lemma (let plain = slice_work_around (le_seq_quad32_to_bytes plain_LE) 0 in
         let cipher = slice_work_around (le_seq_quad32_to_bytes cipher_LE) 0 in
         cipher = gctr_encrypt_LE icb_BE (make_gctr_plain_LE plain) alg key)

let aes_encrypt_BE (alg:algorithm) (key:aes_key_LE alg) (p_BE:quad32) =
  let p_LE = reverse_bytes_quad32 p_BE in
  aes_encrypt_LE alg key p_LE

let gctr_partial (alg:algorithm) (bound:nat) (plain cipher:seq quad32) (key:aes_key_LE alg) (icb:quad32) =
  let bound = min bound (min (length plain) (length cipher)) in
  forall j . {:pattern (index cipher j)} 0 <= j /\ j < bound ==>
    index cipher j == quad32_xor (index plain j) (aes_encrypt_BE alg key (inc32 icb j))

let test (alg:algorithm) (plain cipher:seq quad32) (key:aes_key_LE alg) (icb:quad32) (count:nat32) : Lemma
  (requires length plain >= 4 /\ length cipher >= 4 /\
            index_work_around_quad32 cipher 0 == quad32_xor (index_work_around_quad32 plain 0) (aes_encrypt_BE alg key (inc32 icb count)))
  (ensures gctr_partial alg 1 plain cipher key (inc32 icb count))
  =
  ()

val gctr_partial_completed (alg:algorithm) (plain cipher:seq quad32) (key:aes_key_LE alg) (icb:quad32) : Lemma
  (requires length plain == length cipher /\
            256 * (length plain) < pow2_32 /\
            gctr_partial alg (length cipher) plain cipher key icb)
  (ensures cipher == gctr_encrypt_recursive icb plain alg key 0)

val gctr_partial_to_full_basic (icb_BE:quad32) (plain:seq quad32) (alg:algorithm) (key:aes_key_LE alg) (cipher:seq quad32) : Lemma
  (requires (cipher == gctr_encrypt_recursive icb_BE plain alg key 0) /\
            (4096 * (length plain) * 16 < pow2_32))
  (ensures le_seq_quad32_to_bytes cipher == gctr_encrypt_LE icb_BE (le_seq_quad32_to_bytes plain) alg key)

open FStar.Seq.Properties

val gctr_partial_to_full_advanced (icb_BE:quad32) (plain:seq quad32) (cipher:seq quad32) (alg:algorithm) (key:aes_key_LE alg) (num_bytes:nat) : Lemma
  (requires (1 <= num_bytes /\
             num_bytes < 16 * length plain /\
             16 * (length plain - 1) < num_bytes /\
             num_bytes % 16 <> 0 /\ 4096 * num_bytes < pow2_32 /\
             length plain == length cipher /\
             (let num_blocks = num_bytes / 16 in
              slice cipher 0 num_blocks == gctr_encrypt_recursive icb_BE (slice plain 0 num_blocks) alg key 0 /\
              index cipher num_blocks == gctr_encrypt_block icb_BE (index plain num_blocks) alg key num_blocks)))
  (ensures (let plain_bytes = slice (le_seq_quad32_to_bytes plain) 0 num_bytes in
            let cipher_bytes = slice (le_seq_quad32_to_bytes cipher) 0 num_bytes in
            cipher_bytes == gctr_encrypt_LE icb_BE plain_bytes alg key))

val gctr_encrypt_one_block (icb_BE plain:quad32) (alg:algorithm) (key:aes_key_LE alg) :
  Lemma(gctr_encrypt_LE icb_BE (le_quad32_to_bytes plain) alg key =
        le_seq_quad32_to_bytes (create 1 (quad32_xor plain (aes_encrypt_BE alg key icb_BE))))
