module Vale.AES.GCTR_BE_s

// IMPORTANT: Following NIST's specification, this spec is written assuming a big-endian mapping from bytes to quad32s

open Vale.Def.Prop_s
open Vale.Def.Opaque_s
open Vale.Def.Words_s
open Vale.Def.Words.Seq_s
open Vale.Def.Types_s
open Vale.Arch.Types
open FStar.Mul
open Vale.AES.AES_BE_s
open FStar.Seq

// The max length of pow2_32 corresponds to the max length of buffers in Low*
// length plain < pow2_32 <= spec max of 2**39 - 256;
let is_gctr_plain (p:seq nat8) : prop0 = length p < pow2_32
type gctr_plain:eqtype = p:seq nat8 { is_gctr_plain p }
type gctr_plain_internal:eqtype = seq quad32

let inc32 (cb:quad32) (i:int) : quad32 =
  Mkfour ((cb.lo0 + i) % pow2_32) cb.lo1 cb.hi2 cb.hi3

let gctr_encrypt_block (icb:quad32) (plain:quad32) (alg:algorithm) (key:seq nat32) (i:int) : Pure quad32
  (requires is_aes_key_word alg key)
  (ensures fun _ -> True)
  =
  quad32_xor plain (aes_encrypt_word alg key (inc32 icb i))


let rec gctr_encrypt_recursive (icb:quad32) (plain:gctr_plain_internal)
                               (alg:algorithm) (key:aes_key_word alg) (i:int) : Tot (seq quad32) (decreases %[length plain]) =
  if length plain = 0 then empty
  else
    cons (gctr_encrypt_block icb (head plain) alg key i) (gctr_encrypt_recursive icb (tail plain) alg key (i + 1))

let pad_to_128_bits (p:seq nat8) : Pure (seq nat8)
  (requires True)
  (ensures fun q -> length q % 16 == 0 /\ length q <= length p + 15)
  =
  let num_extra_bytes = length p % 16 in
  if num_extra_bytes = 0 then p
  else p @| (create (16 - num_extra_bytes) 0)

let gctr_encrypt_def (icb:quad32) (plain:seq nat8) (alg:algorithm) (key:seq nat32) : Pure (seq nat8)
  (requires is_gctr_plain plain /\ is_aes_key_word alg key)
  (ensures fun _ -> True)
  =
  let num_extra = (length plain) % 16 in

  if num_extra = 0 then
    let plain_quads = be_bytes_to_seq_quad32 plain in
    let cipher_quads = gctr_encrypt_recursive icb plain_quads alg key 0 in
    seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher_quads)
  else
    let full_bytes_len = (length plain) - num_extra in
    let full_blocks, final_block = split plain full_bytes_len in

    let full_quads = be_bytes_to_seq_quad32 full_blocks in
    let final_quad = be_bytes_to_quad32 (pad_to_128_bits final_block) in

    let cipher_quads = gctr_encrypt_recursive icb full_quads alg key 0 in
    let final_cipher_quad = gctr_encrypt_block icb final_quad alg key (full_bytes_len / 16) in

    let cipher_bytes_full = seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE cipher_quads) in
    let final_cipher_bytes = slice (be_quad32_to_bytes final_cipher_quad) 0 num_extra in

    cipher_bytes_full @| final_cipher_bytes
[@"opaque_to_smt"] let gctr_encrypt  = opaque_make gctr_encrypt_def
irreducible let gctr_encrypt_reveal = opaque_revealer (`%gctr_encrypt) gctr_encrypt gctr_encrypt_def
