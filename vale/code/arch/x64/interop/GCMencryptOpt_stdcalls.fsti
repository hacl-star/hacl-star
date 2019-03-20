module GCMencryptOpt_stdcalls

open X64.CPU_Features_s
open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module DV = LowStar.BufferView.Down
module UV = LowStar.BufferView.Up
open Vale.AsLowStar.MemoryHelpers
open FStar.Mul
open Words_s
open Words.Seq_s
open Types_s
open GCM_helpers
open AES_s
open GCM_s
open GHash_s
open GCTR_s
open GCTR
open Interop.Base

let uint8_p = B.buffer UInt8.t
let uint64 = UInt64.t

let disjoint_or_eq (b1 b2:uint8_p) = B.disjoint b1 b2 \/ b1 == b2

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

let length_aux3 (b:uint8_p) (n:nat) : Lemma
  (requires B.length b = 16 * n)
  (ensures DV.length (get_downview b) % 16 = 0) =
    let db = get_downview b in
    DV.length_eq db;
    FStar.Math.Lemmas.cancel_mul_mod n 16

let length_aux4 (b:uint8_p) : Lemma
  (requires B.length b = 16)
  (ensures DV.length (get_downview b) % 16 = 0) =
    let db = get_downview b in
    DV.length_eq db

let length_aux5 (b:uint8_p) : Lemma
  (requires B.length b = 160)
  (ensures DV.length (get_downview b) % 16 = 0) =
    let db = get_downview b in
    DV.length_eq db

val gcm128_encrypt:
  key:Ghost.erased (Seq.seq nat32) ->
  auth_b:uint8_p ->
  auth_bytes:uint64 ->
  auth_num:uint64 ->
  keys_b:uint8_p ->
  iv_b:uint8_p ->
  hkeys_b:uint8_p ->
  abytes_b:uint8_p ->
  in128x6_b:uint8_p ->
  out128x6_b:uint8_p ->
  len128x6:uint64 ->
  in128_b:uint8_p ->
  out128_b:uint8_p ->
  len128_num:uint64 ->
  inout_b:uint8_p ->
  plain_num:uint64 ->

  scratch_b:uint8_p ->
  tag_b:uint8_p ->

  Stack unit
    (requires fun h0 ->
      B.disjoint tag_b out128x6_b /\ B.disjoint tag_b out128_b /\
      B.disjoint tag_b inout_b /\ B.disjoint tag_b hkeys_b /\
      disjoint_or_eq tag_b auth_b /\ disjoint_or_eq tag_b iv_b /\
      disjoint_or_eq tag_b keys_b /\ disjoint_or_eq tag_b abytes_b /\
      disjoint_or_eq tag_b in128x6_b /\ disjoint_or_eq tag_b in128_b /\
      disjoint_or_eq tag_b scratch_b /\

      B.disjoint iv_b keys_b /\ B.disjoint iv_b scratch_b /\ B.disjoint iv_b in128x6_b /\
      B.disjoint iv_b out128x6_b /\ B.disjoint iv_b hkeys_b /\ B.disjoint iv_b in128_b /\
      B.disjoint iv_b out128_b /\ B.disjoint iv_b inout_b /\
      disjoint_or_eq iv_b auth_b /\ disjoint_or_eq iv_b abytes_b /\

      B.disjoint scratch_b keys_b /\ B.disjoint scratch_b in128x6_b /\
      B.disjoint scratch_b out128x6_b /\ B.disjoint scratch_b in128_b /\
      B.disjoint scratch_b out128_b /\ B.disjoint scratch_b inout_b /\
      B.disjoint scratch_b hkeys_b /\
      disjoint_or_eq scratch_b auth_b /\ disjoint_or_eq scratch_b abytes_b /\

      B.disjoint out128x6_b keys_b /\ B.disjoint out128x6_b hkeys_b /\
      B.disjoint out128x6_b in128_b /\ B.disjoint out128x6_b inout_b /\
      B.disjoint out128x6_b out128_b /\
      disjoint_or_eq out128x6_b in128x6_b /\
      disjoint_or_eq out128x6_b auth_b /\ disjoint_or_eq out128x6_b abytes_b /\

      B.disjoint out128_b keys_b /\ B.disjoint out128_b hkeys_b /\
      B.disjoint out128_b inout_b /\
      disjoint_or_eq out128_b in128_b /\ disjoint_or_eq out128_b in128x6_b /\
      disjoint_or_eq out128_b auth_b /\ disjoint_or_eq out128_b abytes_b /\

      B.disjoint inout_b keys_b /\ B.disjoint inout_b hkeys_b /\
      disjoint_or_eq inout_b in128_b /\ disjoint_or_eq inout_b in128x6_b /\
      disjoint_or_eq inout_b auth_b /\ disjoint_or_eq inout_b abytes_b /\

      disjoint_or_eq keys_b hkeys_b /\ 
      disjoint_or_eq keys_b in128x6_b /\ disjoint_or_eq keys_b in128_b /\
      disjoint_or_eq keys_b auth_b /\ disjoint_or_eq keys_b abytes_b /\

      disjoint_or_eq hkeys_b in128_b /\ disjoint_or_eq hkeys_b in128x6_b /\
      disjoint_or_eq hkeys_b auth_b /\ disjoint_or_eq hkeys_b abytes_b /\

      disjoint_or_eq in128_b in128x6_b /\ disjoint_or_eq in128_b auth_b /\
      disjoint_or_eq in128_b abytes_b /\
      
      disjoint_or_eq in128x6_b auth_b /\ disjoint_or_eq in128x6_b abytes_b /\
      
      disjoint_or_eq auth_b abytes_b /\

      B.live h0 auth_b /\ B.live h0 abytes_b /\ B.live h0 keys_b /\
      B.live h0 iv_b /\ B.live h0 hkeys_b /\
      B.live h0 in128x6_b /\ B.live h0 out128x6_b /\
      B.live h0 in128_b /\ B.live h0 out128_b /\
      B.live h0 inout_b /\ B.live h0 tag_b /\ B.live h0 scratch_b /\

      B.length auth_b = 16 * UInt64.v auth_num /\
      B.length abytes_b == 16 /\
      B.length iv_b = 16 /\
      B.length in128x6_b == 16 * UInt64.v len128x6 /\
      B.length out128x6_b == B.length in128x6_b /\
      B.length in128_b == 16 * UInt64.v len128_num /\
      B.length out128_b == B.length in128_b /\
      B.length inout_b == 16 /\
      B.length scratch_b == 128 /\
      B.length hkeys_b = 160 /\
      B.length tag_b == 16 /\
      B.length keys_b = 176 /\

      8 * (UInt64.v plain_num) < pow2_32 /\
      4096 * 16 * (UInt64.v len128x6) < pow2_32 /\
      4096 * (UInt64.v len128_num) < pow2_32 /\
      4096 * (UInt64.v auth_bytes) < pow2_32 /\

      UInt64.v len128x6 % 6 == 0 /\
      UInt64.v len128x6 >= 18 /\
      12 + UInt64.v len128x6 + 6 < pow2_32 /\

      aesni_enabled /\ pclmulqdq_enabled /\
      is_aes_key_LE AES_128 (Ghost.reveal key) /\
      (let db = get_downview keys_b in
      length_aux keys_b;
      let ub = UV.mk_buffer db Views.up_view128 in
      Seq.equal (UV.as_seq h0 ub) (key_to_round_keys_LE AES_128 (Ghost.reveal key)))
    )
    (ensures fun h0 _ h1 ->
      B.modifies (B.loc_union (B.loc_buffer tag_b)
                  (B.loc_union (B.loc_buffer iv_b)
                  (B.loc_union (B.loc_buffer scratch_b)
                  (B.loc_union (B.loc_buffer out128x6_b)
                  (B.loc_union (B.loc_buffer out128_b)
                  (B.loc_buffer inout_b)))))) h0 h1 /\
      (8 * (UInt64.v plain_num) < pow2_32 /\
       8 * (UInt64.v auth_bytes) < pow2_32 /\ (
       let in128x6_d = get_downview in128x6_b in
       length_aux3 in128x6_b (UInt64.v len128x6);
       let in128x6_u = UV.mk_buffer in128x6_d Views.up_view128 in
       let in128_d = get_downview in128_b in
       length_aux3 in128_b (UInt64.v len128_num);
       let in128_u = UV.mk_buffer in128_d Views.up_view128 in
       let inout_d = get_downview inout_b in
       length_aux3 inout_b 1;      
       let inout_u = UV.mk_buffer inout_d Views.up_view128 in       
       let out128x6_d = get_downview out128x6_b in
       length_aux3 out128x6_b (UInt64.v len128x6);
       let out128x6_u = UV.mk_buffer out128x6_d Views.up_view128 in
       let out128_d = get_downview out128_b in
       length_aux3 out128_b (UInt64.v len128_num);
       let out128_u = UV.mk_buffer out128_d Views.up_view128 in       
       length_aux4 iv_b;
       DV.length_eq (get_downview iv_b);
       let iv_LE = low_buffer_read TUInt8 TUInt128 h0 iv_b 0 in
       let iv_BE = reverse_bytes_quad32 iv_LE in
       let ctr_BE_1 = Mkfour 1 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3 in
       let ctr_BE_2 = Mkfour 2 iv_BE.lo1 iv_BE.hi2 iv_BE.hi3 in
       let plain_in =
         if (UInt64.v plain_num > (UInt64.v len128x6 + UInt64.v len128_num) * 128/8) then
           Seq.append (Seq.append (UV.as_seq h0 in128x6_u) (UV.as_seq h0 in128_u))
                      (UV.as_seq h0 inout_u)
         else Seq.append (UV.as_seq h0 in128x6_u) (UV.as_seq h0 in128_u)
       in let cipher_out =
         if (UInt64.v plain_num > (UInt64.v len128x6 + UInt64.v len128_num) * 128/8) then
           Seq.append (Seq.append (UV.as_seq h1 out128x6_u) (UV.as_seq h1 out128_u))
                      (UV.as_seq h1 inout_u)
         else Seq.append (UV.as_seq h1 out128x6_u) (UV.as_seq h1 out128_u)
       in gctr_partial AES_128 (UInt64.v len128x6 + UInt64.v len128_num + 1) plain_in cipher_out (Ghost.reveal key) ctr_BE_2 /\ (
       DV.length_eq (get_downview hkeys_b);
       let h = reverse_bytes_quad32 (low_buffer_read TUInt8 TUInt128 h1 hkeys_b 0) in
       let length_quad = reverse_bytes_quad32 (Mkfour (8 * UInt64.v plain_num) 0 (8 * UInt64.v auth_bytes) 0) in
       let auth_d = get_downview auth_b in
       length_aux3 auth_b (UInt64.v auth_num);
       let auth_u = UV.mk_buffer auth_d Views.up_view128 in
       let abytes_d = get_downview abytes_b in
       length_aux3 abytes_b 1;      
       let abytes_u = UV.mk_buffer abytes_d Views.up_view128 in        
       let cipher_bytes =
         if UInt64.v plain_num > (UInt64.v len128x6 + UInt64.v len128_num) * 128/8 then
           UV.as_seq h1 inout_u
         else Seq.empty
       in let auth_in =
         if UInt64.v auth_bytes > UInt64.v auth_num * 128 / 8 then
           Seq.append (Seq.append (Seq.append (Seq.append (Seq.append
             (UV.as_seq h0 auth_u) (UV.as_seq h0 abytes_u))
             (UV.as_seq h1 out128x6_u))
             (UV.as_seq h1 out128_u))
             cipher_bytes)
             (Seq.create 1 length_quad)
         else
           Seq.append (Seq.append (Seq.append (Seq.append
             (UV.as_seq h0 auth_u) (UV.as_seq h1 out128x6_u))
             (UV.as_seq h1 out128_u))
             cipher_bytes)
             (Seq.create 1 length_quad)
       in
       DV.length_eq (get_downview tag_b);
       low_buffer_read TUInt8 TUInt128 h1 tag_b 0 ==
         gctr_encrypt_block ctr_BE_1 (ghash_LE h auth_in) AES_128 (Ghost.reveal key) 0
         )
         ))
    )
