module GCTR_s

// IMPORTANT: Following NIST's specification, this spec is written assuming a big-endian mapping from bytes to quad32s
//            Since the AES spec (AES_s) is in little-endian, we need to byteswap each time we call AES

open Prop_s
open Opaque_s
open Words_s
open Types_s
open FStar.Mul
open AES_s
open FStar.Seq

// length plain < pow2_32 / 4096 <= spec max of 2**39 - 256;
let is_gctr_plain_LE (p:seq nat8) : prop0 = 4096 * length p < pow2_32
type gctr_plain_LE:eqtype = p:seq nat8 { is_gctr_plain_LE p }
type gctr_plain_internal_LE:eqtype = p:seq quad32

let inc32 (cb:quad32) (i:int) : quad32 =
  Mkfour ((cb.lo0 + i) % pow2_32) cb.lo1 cb.hi2 cb.hi3

let gctr_encrypt_block (icb_BE:quad32) (plain_LE:quad32) (alg:algorithm) (key:seq nat32) (i:int) : Pure quad32
  (requires is_aes_key_LE alg key)
  (ensures fun _ -> True)
  =
  let icb_LE = reverse_bytes_quad32 (inc32 icb_BE i) in
  quad32_xor plain_LE (aes_encrypt_LE alg key icb_LE)


let rec gctr_encrypt_recursive (icb_BE:quad32) (plain:gctr_plain_internal_LE)
                               (alg:algorithm) (key:aes_key_LE alg) (i:int) : Tot (seq quad32) (decreases %[length plain]) =
  if length plain = 0 then empty
  else
    cons (gctr_encrypt_block icb_BE (head plain) alg key i) (gctr_encrypt_recursive icb_BE (tail plain) alg key (i + 1))

let pad_to_128_bits (p:seq nat8) : Pure (seq nat8)
  (requires True)
  (ensures fun q -> length q % 16 == 0 /\ length q <= length p + 15)
  =
  let num_extra_bytes = length p % 16 in
  if num_extra_bytes = 0 then p
  else p @| (create (16 - num_extra_bytes) 0)

// little-endian, except for icb_BE
let gctr_encrypt_LE_def (icb_BE:quad32) (plain:seq nat8) (alg:algorithm) (key:seq nat32) : Pure (seq nat8)
  (requires is_gctr_plain_LE plain /\ is_aes_key_LE alg key)
  (ensures fun _ -> True)
  =
  let num_extra = (length plain) % 16 in

  if num_extra = 0 then
    let plain_quads_LE = le_bytes_to_seq_quad32 plain in
    let cipher_quads_LE = gctr_encrypt_recursive icb_BE plain_quads_LE alg key 0 in
    le_seq_quad32_to_bytes cipher_quads_LE
  else
    let full_bytes_len = (length plain) - num_extra in
    let full_blocks, final_block = split plain full_bytes_len in

    let full_quads_LE = le_bytes_to_seq_quad32 full_blocks in
    let final_quad_LE = le_bytes_to_quad32 (pad_to_128_bits final_block) in

    let cipher_quads_LE = gctr_encrypt_recursive icb_BE full_quads_LE alg key 0 in
    let final_cipher_quad_LE = gctr_encrypt_block icb_BE final_quad_LE alg key (full_bytes_len / 16) in

    let cipher_bytes_full_LE = le_seq_quad32_to_bytes cipher_quads_LE in
    let final_cipher_bytes_LE = slice (le_quad32_to_bytes final_cipher_quad_LE) 0 num_extra in

    cipher_bytes_full_LE @| final_cipher_bytes_LE

let gctr_encrypt_LE = make_opaque gctr_encrypt_LE_def
