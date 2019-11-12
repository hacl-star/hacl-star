module Vale.Wrapper.X64.AEShash

open Vale.X64.CPU_Features_s
open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module DV = LowStar.BufferView.Down
module UV = LowStar.BufferView.Up
open FStar.Mul
open Vale.Def.Words_s
open Vale.Def.Words.Seq_s
open Vale.AES.AES_s
open Vale.Interop.Base
open Vale.Def.Types_s
open Vale.AES.OptPublic

unfold
let uint8_p = B.buffer UInt8.t

let keyhash_init_st (a: algorithm { a = AES_128 \/ a = AES_256 }) =
  key:Ghost.erased (Seq.seq nat32) ->
  roundkeys_b:uint8_p ->
  hkeys_b:uint8_p ->
  Stack unit
    (requires fun h0 ->
      B.disjoint roundkeys_b hkeys_b /\

      B.live h0 roundkeys_b /\ B.live h0 hkeys_b /\

      B.length roundkeys_b = Vale.Wrapper.X64.AES.key_offset a /\
      B.length hkeys_b = 128 /\

      is_aes_key_LE a (Ghost.reveal key) /\
      (Seq.equal (B.as_seq h0 roundkeys_b)
        (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes (key_to_round_keys_LE a (Ghost.reveal key))))) /\

      aesni_enabled /\ pclmulqdq_enabled /\ avx_enabled /\ sse_enabled)
    (ensures fun h0 _ h1 ->
      B.modifies (B.loc_buffer hkeys_b) h0 h1 /\

      hkeys_reqs_pub (le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h1 hkeys_b)))
        (reverse_bytes_quad32 (aes_encrypt_LE a (Ghost.reveal key) (Mkfour 0 0 0 0))))

inline_for_extraction
val aes128_keyhash_init_stdcall: keyhash_init_st AES_128

inline_for_extraction
val aes256_keyhash_init_stdcall: keyhash_init_st AES_256
