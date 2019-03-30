module GCMencrypt_stdcalls

open X64.CPU_Features_s
open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module DV = LowStar.BufferView.Down
module UV = LowStar.BufferView.Up
open FStar.Mul
open Words_s
open Words.Seq_s
open GCM_helpers
open AES_s
open GCM_s
open Interop.Base

let uint8_p = B.buffer UInt8.t
let uint64 = UInt64.t

let length_aux (b:uint8_p) : Lemma
  (requires B.length b = 176)
  (ensures DV.length (get_downview b) % 16 = 0) = 
    let db = get_downview b in
    DV.length_eq db

let length_aux2 (b:uint8_p) : Lemma
  (requires B.length b = 240)
  (ensures DV.length (get_downview b) % 16 = 0) = 
    let db = get_downview b in
    DV.length_eq db

inline_for_extraction
val gcm128_encrypt:
  key:Ghost.erased (Seq.seq nat32) ->
  plain_b:uint8_p ->
  plain_num:uint64 ->
  auth_b:uint8_p ->
  auth_num:uint64 ->
  iv_b:uint8_p ->
  out_b:uint8_p ->
  tag_b:uint8_p ->
  keys_b:uint8_p ->
  Stack unit
    (requires fun h0 ->
      B.disjoint plain_b out_b /\ B.disjoint auth_b out_b /\
      B.disjoint keys_b out_b /\ B.disjoint tag_b out_b /\

      (B.disjoint plain_b auth_b \/ plain_b == auth_b) /\
      (B.disjoint plain_b iv_b \/ plain_b == iv_b) /\
      (B.disjoint plain_b tag_b \/ plain_b == tag_b) /\
      (B.disjoint plain_b keys_b \/ plain_b == keys_b) /\
      (B.disjoint auth_b iv_b \/ auth_b == iv_b) /\      
      (B.disjoint auth_b tag_b \/ auth_b == tag_b) /\
      (B.disjoint auth_b keys_b \/ auth_b == keys_b) /\
      (B.disjoint iv_b out_b \/ iv_b == out_b) /\      
      (B.disjoint iv_b tag_b \/ iv_b == tag_b) /\
      (B.disjoint iv_b keys_b \/ iv_b == keys_b) /\     
      (B.disjoint tag_b keys_b \/ tag_b == keys_b) /\     
      
      B.live h0 keys_b /\ B.live h0 plain_b /\ B.live h0 iv_b /\ 
      B.live h0 out_b /\ B.live h0 tag_b /\ B.live h0 auth_b /\

      UInt64.v plain_num % 16 = 0 /\
      UInt64.v auth_num % 16 = 0 /\

      B.length plain_b = UInt64.v plain_num /\
      B.length auth_b = UInt64.v auth_num /\
      B.length iv_b = 16 /\
      B.length out_b = B.length plain_b /\
      B.length tag_b = 16 /\
      B.length keys_b = 176 /\

      4096 * (UInt64.v plain_num) < pow2_32 /\
      4096 * (UInt64.v auth_num) < pow2_32 /\
      
      aesni_enabled /\ pclmulqdq_enabled /\
      is_aes_key_LE AES_128 (Ghost.reveal key) /\
      (let db = get_downview keys_b in
      length_aux keys_b;
      let ub = UV.mk_buffer db Views.up_view128 in
      Seq.equal (UV.as_seq h0 ub) (key_to_round_keys_LE AES_128 (Ghost.reveal key)))
    )
    (ensures fun h0 _ h1 ->
      B.modifies (B.loc_union (B.loc_buffer out_b) (B.loc_buffer tag_b)) h0 h1 /\

      (let iv = seq_uint8_to_seq_nat8 (B.as_seq h0 iv_b) in
       let plain = seq_uint8_to_seq_nat8 (B.as_seq h0 plain_b) in
       let auth = seq_uint8_to_seq_nat8 (B.as_seq h0 auth_b) in
       let cipher, tag = gcm_encrypt_LE AES_128 (seq_nat32_to_seq_nat8_LE (Ghost.reveal key)) iv plain auth in
       Seq.equal (seq_uint8_to_seq_nat8 (B.as_seq h1 out_b)) cipher /\
       Seq.equal (seq_uint8_to_seq_nat8 (B.as_seq h1 tag_b)) tag)
    )

inline_for_extraction
val gcm256_encrypt:
  key:Ghost.erased (Seq.seq nat32) ->
  plain_b:uint8_p ->
  plain_num:uint64 ->
  auth_b:uint8_p ->
  auth_num:uint64 ->
  iv_b:uint8_p ->
  out_b:uint8_p ->
  tag_b:uint8_p ->
  keys_b:uint8_p ->
  Stack unit
    (requires fun h0 ->
      B.disjoint plain_b out_b /\ B.disjoint auth_b out_b /\
      B.disjoint keys_b out_b /\ B.disjoint tag_b out_b /\

      (B.disjoint plain_b auth_b \/ plain_b == auth_b) /\
      (B.disjoint plain_b iv_b \/ plain_b == iv_b) /\
      (B.disjoint plain_b tag_b \/ plain_b == tag_b) /\
      (B.disjoint plain_b keys_b \/ plain_b == keys_b) /\
      (B.disjoint auth_b iv_b \/ auth_b == iv_b) /\      
      (B.disjoint auth_b tag_b \/ auth_b == tag_b) /\
      (B.disjoint auth_b keys_b \/ auth_b == keys_b) /\
      (B.disjoint iv_b out_b \/ iv_b == out_b) /\      
      (B.disjoint iv_b tag_b \/ iv_b == tag_b) /\
      (B.disjoint iv_b keys_b \/ iv_b == keys_b) /\     
      (B.disjoint tag_b keys_b \/ tag_b == keys_b) /\     
      
      B.live h0 keys_b /\ B.live h0 plain_b /\ B.live h0 iv_b /\ 
      B.live h0 out_b /\ B.live h0 tag_b /\ B.live h0 auth_b /\

      UInt64.v plain_num % 16 = 0 /\
      UInt64.v auth_num % 16 = 0 /\

      B.length plain_b = UInt64.v plain_num /\
      B.length auth_b = UInt64.v auth_num /\
      B.length iv_b = 16 /\
      B.length out_b = B.length plain_b /\
      B.length tag_b = 16 /\
      B.length keys_b = 240 /\

      4096 * (UInt64.v plain_num) < pow2_32 /\
      4096 * (UInt64.v auth_num) < pow2_32 /\
      
      aesni_enabled /\ pclmulqdq_enabled /\
      is_aes_key_LE AES_256 (Ghost.reveal key) /\
      (let db = get_downview keys_b in
      length_aux2 keys_b;
      let ub = UV.mk_buffer db Views.up_view128 in
      Seq.equal (UV.as_seq h0 ub) (key_to_round_keys_LE AES_256 (Ghost.reveal key)))
    )
    (ensures fun h0 _ h1 ->
      B.modifies (B.loc_union (B.loc_buffer out_b) (B.loc_buffer tag_b)) h0 h1 /\

      (let iv = seq_uint8_to_seq_nat8 (B.as_seq h0 iv_b) in
       let plain = seq_uint8_to_seq_nat8 (B.as_seq h0 plain_b) in
       let auth = seq_uint8_to_seq_nat8 (B.as_seq h0 auth_b) in
       let cipher, tag = gcm_encrypt_LE AES_256 (seq_nat32_to_seq_nat8_LE (Ghost.reveal key)) iv plain auth in
       Seq.equal (seq_uint8_to_seq_nat8 (B.as_seq h1 out_b)) cipher /\
       Seq.equal (seq_uint8_to_seq_nat8 (B.as_seq h1 tag_b)) tag)
    )
