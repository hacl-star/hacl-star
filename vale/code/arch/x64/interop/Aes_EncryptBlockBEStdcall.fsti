module Aes_EncryptBlockBEStdcall

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
open AES_s
open GCTR
open X64.CPU_Features_s

let keys_match (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:s8 { B.length keys_b % 16 == 0 }) (h:HS.mem) =
  let keys128_b = BV.mk_buffer_view keys_b Views.view128 in
  let round_keys = key_to_round_keys_LE AES_128 (Ghost.reveal key) in
  BV.as_seq h keys128_b == round_keys

let pre_cond (h:HS.mem) (output_b:s8) (input_b:s8) (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:s8) = 
  live h output_b /\ live h input_b /\ live h keys_b /\  
  disjoint_or_eq output_b input_b /\ 
  disjoint output_b keys_b /\ 
  disjoint input_b keys_b /\ 
  length output_b % 16 == 0 /\ length input_b % 16 == 0 /\ length keys_b % 16 == 0 /\
  length keys_b == (nr AES_128 + 1) `op_Multiply` 16 /\
  keys_match key keys_b h /\
  length output_b >= 1 /\ length input_b >= 1 /\
  aesni_enabled

let post_cond (h:HS.mem) (h':HS.mem) (output_b:s8) (input_b:s8) (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:s8) = 
  live h output_b /\ live h input_b /\ live h keys_b /\ 
  live h' output_b /\ live h' input_b /\ live h' keys_b /\ 
  length output_b % 16 == 0 /\ length input_b % 16 == 0 /\ length keys_b % 16 == 0 /\
  (let  input128_b = BV.mk_buffer_view  input_b Views.view128 in
   let output128_b = BV.mk_buffer_view output_b Views.view128 in
   BV.length input128_b >= 1 /\ BV.length output128_b >= 1 /\
  (let  input_q = Seq.index (BV.as_seq h input128_b) 0 in
   let output_q = Seq.index (BV.as_seq h' output128_b) 0 in
   output_q == aes_encrypt_BE AES_128 (Ghost.reveal key) input_q))  

let full_post_cond (h:HS.mem) (h':HS.mem) (output_b:s8) (input_b:s8) (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:s8)  =
  post_cond h h' output_b input_b key keys_b  /\
  M.modifies (M.loc_buffer output_b) h h'

val aes_EncryptBlockBEStdcall: output_b:s8 -> input_b:s8 -> key:Ghost.erased (aes_key_LE AES_128) -> keys_b:s8 -> Stack unit
	(requires (fun h -> pre_cond h output_b input_b key keys_b ))
	(ensures (fun h0 _ h1 -> full_post_cond h0 h1 output_b input_b key keys_b ))
