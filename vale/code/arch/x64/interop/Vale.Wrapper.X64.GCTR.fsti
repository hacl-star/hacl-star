module Vale.Wrapper.X64.GCTR

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
open Vale.AES.GCTR
open Vale.AES.GCTR_s
open Vale.Interop.Base
open Vale.Def.Types_s

unfold
let uint8_p = B.buffer UInt8.t
let uint64 = UInt64.t

inline_for_extraction noextract
let gctr_bytes_st (a: algorithm { a = AES_128 \/ a = AES_256 }) =
 key:Ghost.erased (Seq.seq nat32) ->
 in_b:uint8_p ->
 num_bytes:uint64 ->
 out_b:uint8_p ->
 keys_b:uint8_p ->
 ctr_b:uint8_p ->
 Stack unit
   (requires fun h0 ->
     B.disjoint in_b out_b /\
     B.disjoint keys_b out_b /\
     B.disjoint in_b keys_b /\
     B.disjoint ctr_b in_b /\
     B.disjoint ctr_b out_b /\
     B.disjoint ctr_b keys_b /\

     B.live h0 keys_b /\ B.live h0 in_b /\
     B.live h0 out_b /\ B.live h0 ctr_b /\

     B.length in_b = UInt64.v num_bytes /\
     B.length out_b = B.length in_b /\
     B.length ctr_b = 16 /\
     B.length keys_b = Vale.Wrapper.X64.AES.key_offset a /\

     4096 * (UInt64.v num_bytes) < pow2_32 /\

     aesni_enabled /\ avx_enabled /\
     is_aes_key_LE a (Ghost.reveal key) /\
     (Seq.equal (B.as_seq h0 keys_b)
       (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes (key_to_round_keys_LE a (Ghost.reveal key)))))
   )
   (ensures fun h0 r h1 ->
     B.modifies (B.loc_buffer out_b) h0 h1 /\

     (let ctr = seq_uint8_to_seq_nat8 (B.as_seq h0 ctr_b) in
      let plain = seq_uint8_to_seq_nat8 (B.as_seq h0 in_b) in
      let cipher = seq_uint8_to_seq_nat8 (B.as_seq h1 out_b) in
      Seq.equal
        (gctr_encrypt_LE (le_bytes_to_quad32 ctr) (make_gctr_plain_LE plain) a (Ghost.reveal key))
        cipher
      )
   )

inline_for_extraction
val gctr_bytes_stdcall128: gctr_bytes_st AES_128

inline_for_extraction
val gctr_bytes_stdcall256: gctr_bytes_st AES_256
