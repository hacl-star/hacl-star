module Gctr_extra_stdcall

open LowStar.Buffer
module B = LowStar.Buffer
module BV = LowStar.BufferView
open LowStar.Modifies
module M = LowStar.Modifies
open LowStar.ModifiesPat
open FStar.HyperStack.ST
module HS = FStar.HyperStack
open Interop
open Types_s
open Words_s
open AES_s
open GCTR_s
open GCTR
open GCM_s
open GCM_helpers
open GHash
open X64.CPU_Features_s

let buffer_to_seq_quad32 (b:s8{ B.length b % 16 == 0 }) (h:HS.mem) : GTot (s:Seq.seq quad32 {Seq.length s == B.length b / 16} ) =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  (BV.as_seq h b128)

let buffer_to_quad32 (b:s8 { B.length b % 16 == 0 /\ B.length b > 0 }) (h:HS.mem) : GTot quad32 =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  assert (B.length b >= 16);
  assert (BV.length b128 > 0);
  BV.sel h b128 0

let keys_match (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:s8 { B.length keys_b % 16 == 0 }) (h:HS.mem) =
  let keys128_b = BV.mk_buffer_view keys_b Views.view128 in
  let round_keys = key_to_round_keys_LE AES_128 (Ghost.reveal key) in
  BV.as_seq h keys128_b == round_keys

let pre_cond (h:HS.mem) (plain_b:s8) (num_bytes:nat64) (iv_old:Ghost.erased (quad32)) (iv_b:s8) (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:s8) (cipher_b:s8) = 
  aesni_enabled /\

  live h plain_b /\ live h iv_b /\ live h keys_b /\ live h cipher_b /\ 
  disjoint plain_b iv_b /\ 
  disjoint plain_b keys_b /\ 
  disjoint plain_b cipher_b /\ 
  disjoint iv_b keys_b /\ 
  disjoint iv_b cipher_b /\ 
  disjoint keys_b cipher_b /\ 
length plain_b % 16 == 0 /\ length iv_b % 16 == 0 /\ length keys_b % 16 == 0 /\ length cipher_b % 16 == 0 /\

  length plain_b == bytes_to_quad_size num_bytes `op_Multiply` 16 /\
  length cipher_b == length plain_b /\
  length iv_b == 16 /\

  4096 `op_Multiply` num_bytes < pow2_32 /\
  256 `op_Multiply` bytes_to_quad_size num_bytes < pow2_32 /\

  // AES reqs
  length keys_b == (nr AES_128 + 1) `op_Multiply` 16 /\
  length keys_b % 16 == 0 /\  // REVIEW: Should be derivable from line above :(
  keys_match key keys_b h /\

  // Extra reqs
  (let num_bytes = num_bytes in
   let num_blocks = num_bytes / 16 in
   let iv = buffer_to_quad32 iv_b h in
   num_bytes % 16 <> 0 /\
   0 < num_bytes /\ num_bytes < 16 `op_Multiply` bytes_to_quad_size num_bytes /\
   16 `op_Multiply` (bytes_to_quad_size num_bytes - 1) < num_bytes /\
   gctr_partial AES_128
                num_blocks
                (buffer_to_seq_quad32 plain_b h)
                (buffer_to_seq_quad32  cipher_b h)
                (Ghost.reveal key)
                (Ghost.reveal iv_old) /\
   iv == inc32 (Ghost.reveal iv_old) num_blocks)
   

let post_cond (h:HS.mem) (h':HS.mem) (plain_b:s8) (num_bytes:nat64) (iv_old:Ghost.erased (quad32)) (iv_b:s8) (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:s8) (cipher_b:s8) = 
  live h plain_b /\ live h iv_b /\ live h keys_b /\ live h cipher_b /\ 
  live h' plain_b /\ live h' iv_b /\ live h' keys_b /\ live h' cipher_b /\ 
  length plain_b % 16 == 0 /\ length iv_b % 16 == 0 /\ length keys_b % 16 == 0 /\ length cipher_b % 16 == 0 /\

  length plain_b  == bytes_to_quad_size num_bytes `op_Multiply` 16 /\
  length cipher_b == length plain_b /\
  length iv_b == 16 /\
  length plain_b % 16 == 0 /\
  length keys_b == (nr AES_128 + 1) `op_Multiply` 16 /\

  (let num_bytes = num_bytes in
   let num_blocks = num_bytes / 16 in
   let iv_new = buffer_to_quad32 iv_b h in

   // We modified cipher_b, but we didn't disrupt the work that was previously done
   let cipher_blocks  = Seq.slice (buffer_to_seq_quad32 cipher_b h)  0 num_blocks in
   let cipher_blocks' = Seq.slice (buffer_to_seq_quad32 cipher_b h') 0 num_blocks in
   cipher_blocks == cipher_blocks' /\

   // GCTR
   (let plain  = Seq.slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32  plain_b h))  0 num_bytes in
    let cipher = Seq.slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32 cipher_b h')) 0 num_bytes in
    cipher == gctr_encrypt_LE (Ghost.reveal iv_old) (make_gctr_plain_LE plain) AES_128 (Ghost.reveal key))
    )
  
let full_post_cond (h:HS.mem) (h':HS.mem) (plain_b:s8) (num_bytes:nat64) (iv_old:Ghost.erased (quad32)) (iv_b:s8) (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:s8) (cipher_b:s8)  =
  post_cond h h' plain_b num_bytes iv_old iv_b key keys_b cipher_b  /\
  M.modifies (M.loc_buffer cipher_b) h h'

val gctr_bytes_extra_stdcall: plain_b:s8 -> num_bytes:nat64 -> iv_old:Ghost.erased (quad32) -> iv_b:s8 -> key:Ghost.erased (aes_key_LE AES_128) -> keys_b:s8 -> cipher_b:s8 -> Stack unit
	(requires (fun h -> pre_cond h plain_b num_bytes iv_old iv_b key keys_b cipher_b ))
	(ensures (fun h0 _ h1 -> full_post_cond h0 h1 plain_b num_bytes iv_old iv_b key keys_b cipher_b ))
