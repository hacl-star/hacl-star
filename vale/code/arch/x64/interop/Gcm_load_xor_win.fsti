module Gcm_load_xor_win

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
open GCTR_s
open GCTR

let s8 = B.buffer S8.t

let buffer_to_quad32 (b:s8 { B.length b % 16 == 0 /\ B.length b > 0 }) (h:HS.mem) : GTot quad32 =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  assert (B.length b >= 16);
  assert (BV.length b128 > 0);
  BV.sel h b128 0
  //index (BV.as_seq h b128) 0

let buffer_to_seq_quad32 (b:s8{ B.length b % 16 == 0 }) (h:HS.mem) : GTot (s:Seq.seq quad32 {Seq.length s == B.length b / 16} ) =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  (BV.as_seq h b128)


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

open FStar.Mul

let pre_cond (h:HS.mem) (plain_b:s8) (mask_b:s8) (cipher_b:s8) (offset:nat64) (num_blocks:Ghost.erased (nat64)) (key:Ghost.erased (aes_key_LE AES_128)) (iv:Ghost.erased (quad32)) = live h plain_b /\ live h mask_b /\ live h cipher_b /\ bufs_disjoint [plain_b;mask_b;cipher_b] /\ length plain_b % 16 == 0 /\ length mask_b % 16 == 0 /\ length cipher_b % 16 == 0
 /\  ( let mods = M.loc_buffer cipher_b in
    B.live h plain_b /\ B.live h mask_b /\ B.live h cipher_b /\
    M.loc_disjoint (M.loc_buffer plain_b) mods /\
    M.loc_disjoint (M.loc_buffer mask_b)  mods /\
    B.length plain_b  >= (Ghost.reveal num_blocks) * 16 /\
    B.length cipher_b == B.length plain_b /\
    B.length mask_b == 16 /\
    B.length plain_b % 16 == 0 /\
    (let num_blocks = (Ghost.reveal num_blocks) in
     let mask   = buffer_to_quad32       mask_b h in
     let plain  = buffer_to_seq_quad32  plain_b h in
     let cipher = buffer_to_seq_quad32 cipher_b h in
     let key = Ghost.reveal key in
     let iv = Ghost.reveal iv in

     // gcm_body specific
     offset < num_blocks /\
     mask == aes_encrypt_BE AES_128 key (inc32 iv offset) /\
     gctr_partial AES_128 offset plain cipher key iv
    )
  )

let post_cond (h:HS.mem) (h':HS.mem) (plain_b:s8) (mask_b:s8) (cipher_b:s8) (offset:nat64) (num_blocks:Ghost.erased (nat64)) (key:Ghost.erased (aes_key_LE AES_128)) (iv:Ghost.erased (quad32)) = length plain_b % 16 == 0 /\ length mask_b % 16 == 0 /\ length cipher_b % 16 == 0 /\
    B.length plain_b  >= (Ghost.reveal num_blocks) * 16 /\
    B.length cipher_b == B.length plain_b /\
    B.length mask_b == 16 /\
   (   let mods = M.loc_buffer cipher_b in
    M.modifies mods h h' /\
    B.live h plain_b /\ B.live h mask_b /\ B.live h cipher_b /\
    (let num_blocks = (Ghost.reveal num_blocks) in
     let mask   = buffer_to_quad32  mask_b h in
     let plain  = buffer_to_seq_quad32  plain_b h' in
     let old_cipher = buffer_to_seq_quad32 cipher_b h in
     let cipher = buffer_to_seq_quad32 cipher_b h' in
     let key = Ghost.reveal key in
     let iv = Ghost.reveal iv in
     offset < num_blocks /\
     gctr_partial AES_128 (offset + 1) plain cipher key iv /\
     Seq.slice cipher 0 offset == Seq.slice old_cipher 0 offset  // We didn't disrupt earlier slots
    )
    )

val gcm_load_xor_store_buffer_win: plain_b:s8 -> mask_b:s8 -> cipher_b:s8 -> offset:UInt64.t -> num_blocks:Ghost.erased (nat64) -> key:Ghost.erased (aes_key_LE AES_128) -> iv:Ghost.erased (quad32) -> Stack unit
        (requires (fun h -> pre_cond h plain_b mask_b cipher_b (UInt64.v offset) num_blocks key iv ))
        (ensures (fun h0 _ h1 -> post_cond h0 h1 plain_b mask_b cipher_b (UInt64.v offset) num_blocks key iv ))
