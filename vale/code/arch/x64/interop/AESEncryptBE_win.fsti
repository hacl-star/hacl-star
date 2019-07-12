module AESEncryptBE_win

open LowStar.Buffer
module B = LowStar.Buffer
module BV = LowStar.BufferView
open LowStar.Modifies
module M = LowStar.Modifies
open LowStar.ModifiesPat
open FStar.HyperStack.ST
module HS = FStar.HyperStack
module S8 = SecretByte
open Interop
open Words_s
open Types_s
open X64.Machine_s
open X64.Memory_s
open X64.Vale.State
open X64.Vale.Decls
open AES_s
open GCTR

let s8 = B.buffer S8.t

let rec loc_locs_disjoint_rec (l:s8) (ls:list s8) : Type0 =
  match ls with
  | [] -> True
  | h::t -> M.loc_disjoint (M.loc_buffer l) (M.loc_buffer h) /\ loc_locs_disjoint_rec l t

let rec locs_disjoint_rec (ls:list s8) : Type0 =
  match ls with
  | [] -> True
  | h::t -> loc_locs_disjoint_rec h t /\ locs_disjoint_rec t

unfold
let bufs_disjoint (ls:list s8) : Type0 = normalize (locs_disjoint_rec ls)

unfold
let buf_disjoint_from (b:s8) (ls:list s8) : Type0 = normalize (loc_locs_disjoint_rec b ls)

unfold let disjoint_or_eq (#a:Type0) (b1:B.buffer a) (b2:B.buffer a) =
  M.(loc_disjoint (loc_buffer b1) (loc_buffer b2)) \/ b1 == b2

let keys_match (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:s8 { B.length keys_b % 16 == 0 }) (h:HS.mem) =
  let keys128_b = BV.mk_buffer_view keys_b Views.view128 in
  let round_keys = key_to_round_keys_LE AES_128 (Ghost.reveal key) in
  BV.as_seq h keys128_b == round_keys

open FStar.Mul

let pre_cond (h:HS.mem) (output_b:s8) (input_b:s8) (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:s8) =
live h output_b /\ live h input_b /\ live h keys_b /\
    disjoint_or_eq input_b output_b /\
    bufs_disjoint [keys_b;input_b] /\
    bufs_disjoint [keys_b;output_b] /\ length output_b % 16 == 0 /\ length input_b % 16 == 0 /\ length keys_b % 16 == 0 /\ B.length keys_b == (nr AES_128 + 1) * 16 /\
  keys_match key keys_b h
  /\ B.length output_b >= 1 /\ B.length input_b >= 1




let post_cond (h0:HS.mem) (h1:HS.mem) (output_b:s8) (input_b:s8) (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:s8) =
  length input_b % 16 == 0 /\ length output_b % 16 == 0 /\ length keys_b % 16 == 0 /\
    B.live h1 input_b /\ B.live h1 keys_b /\
    M.modifies (M.loc_buffer output_b) h0 h1 /\
    (let  input128_b = BV.mk_buffer_view  input_b Views.view128 in
     let output128_b = BV.mk_buffer_view output_b Views.view128 in
     BV.length input128_b >= 1 /\ BV.length output128_b >= 1 /\
    (let  input_q = Seq.index (BV.as_seq h0 input128_b) 0 in
     let output_q = Seq.index (BV.as_seq h1 output128_b) 0 in
     output_q == aes_encrypt_BE AES_128 (Ghost.reveal key) input_q))

val aes128_encrypt_block_be_win: output_b:s8 -> input_b:s8 -> key:Ghost.erased (aes_key_LE AES_128) -> keys_b:s8 -> Stack unit
        (requires (fun h -> pre_cond h output_b input_b key keys_b ))
        (ensures (fun h0 _ h1 -> post_cond h0 h1 output_b input_b key keys_b ))
