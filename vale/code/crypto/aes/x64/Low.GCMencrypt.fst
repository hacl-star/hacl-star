module Low.GCMencrypt

open FStar.HyperStack.ST

module B = LowStar.Buffer
module BV = LowStar.BufferView
module M = LowStar.Modifies
open LowStar.ModifiesPat
module U8 = SecretByte
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module HST = FStar.HyperStack.ST

open Types_s
open Arch.Types
open Words_s
open Words.Seq_s
open AES_s
open GCTR_s
open GCTR
open GCM_s
open GCM_helpers
open GHash_s
open GHash
open X64.Memory_s
open BufferViewHelpers
open FStar.Seq

// Not sure how to define this after we open FStar.Mul
noextract
let quad32x3 = quad32 * quad32 * quad32

open FStar.Mul

(*** Useful specification abbreviations ***)
(*
let seq_U8_to_seq_nat8 (b:seq U8.t) : (seq nat8) =
  Seq.init (length b) (fun (i:nat { i < length b }) -> U8.v (index b i))
*)

let buffer_to_nat32 (b:B.buffer U8.t { B.length b % 4 == 0 /\ B.length b > 0 }) (h:HS.mem) : GTot nat32 =
  assert (B.length b % 4 == 0);
  assert (BV.View?.n Views.view32 == 4);
  let b32 = BV.mk_buffer_view b Views.view32 in
  BV.as_buffer_mk_buffer_view b Views.view32;
  BV.get_view_mk_buffer_view b Views.view32;
  BV.length_eq b32;
  //assert (B.length b >= 4);
  //assert (BV.length b32 > 0);
  U32.v (BV.sel h b32 0)
  //U32.v (index (BV.as_seq h b32) 0)

let buffer_to_quad32 (b:B.buffer U8.t { B.length b % 16 == 0 /\ B.length b > 0 }) (h:HS.mem) : GTot quad32 =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  assert (B.length b >= 16);
  assert (BV.length b128 > 0);
  BV.sel h b128 0
  //index (BV.as_seq h b128) 0

let buffer_to_seq_quad32 (b:B.buffer U8.t { B.length b % 16 == 0 }) (h:HS.mem) : GTot (s:seq quad32 {length s == B.length b / 16} ) =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  (BV.as_seq h b128)

let buffer_to_seq_quad32_0 (b:B.buffer U8.t { B.length b % 16 == 0 /\ B.length b > 0 }) (h:HS.mem) :
  Lemma (buffer_to_quad32 b h == index (buffer_to_seq_quad32 b h) 0)
  [SMTPatOr [
    [SMTPat (index (buffer_to_seq_quad32 b h) 0)];
    [SMTPat (index (BV.as_seq h (BV.mk_buffer_view b Views.view128)) 0)]
  ]]
  =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  BV.as_seq_sel h b128 0;
  ()

let keys_match (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:B.buffer U8.t { B.length keys_b % 16 == 0 }) (h:HS.mem) =
  let keys128_b = BV.mk_buffer_view keys_b Views.view128 in
  let round_keys = key_to_round_keys_LE AES_128 (Ghost.reveal key) in
  BV.as_seq h keys128_b == round_keys

unfold let disjoint_or_eq (#a:Type0) (b1:B.buffer a) (b2:B.buffer a) =
  M.(loc_disjoint (loc_buffer b1) (loc_buffer b2)) \/ b1 == b2

unfold let disjoint (#a:Type0) (b1:B.buffer a) (b2:B.buffer a) =
  M.(loc_disjoint (loc_buffer b1) (loc_buffer b2))

let rec loc_locs_disjoint_rec (l:B.buffer U8.t) (ls:list (B.buffer U8.t)) : Type0 =
  match ls with
  | [] -> True
  | h::t -> M.loc_disjoint (M.loc_buffer l) (M.loc_buffer h) /\ loc_locs_disjoint_rec l t

let rec locs_disjoint_rec (ls:list (B.buffer U8.t)) : Type0 =
  match ls with
  | [] -> True
  | h::t -> loc_locs_disjoint_rec h t /\ locs_disjoint_rec t

unfold
let buffers_disjoint (ls:list (B.buffer U8.t)) : Type0 = normalize (locs_disjoint_rec ls)


(*** Functionality imported from Vale ***)

let aes128_encrypt_block_buffer
             (input_b output_b:B.buffer U8.t)
             (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:B.buffer U8.t)
             : Stack unit
  (requires fun h ->
    B.live h input_b /\ B.live h keys_b /\ B.live h output_b /\
    B.length  input_b % 16 == 0 /\ B.length  input_b >= 16 /\
    B.length output_b % 16 == 0 /\ B.length output_b >= 16 /\
    // Required by interop layer; not actually needed here
    disjoint_or_eq input_b output_b /\
    disjoint keys_b input_b /\
    disjoint keys_b output_b /\
    // AES reqs
    B.length keys_b == (nr AES_128 + 1) * 16 /\
    B.length keys_b % 16 == 0 /\  // REVIEW: Should be derivable from line above :(
    keys_match key keys_b h
  )
  (ensures fun h () h' ->
    B.live h' input_b /\ B.live h' output_b /\ B.live h' keys_b /\
    M.modifies (M.loc_buffer output_b) h h' /\
    (let  input_q = buffer_to_quad32  input_b h in
     let output_q = buffer_to_quad32 output_b h' in
     output_q == aes_encrypt_LE AES_128 (Ghost.reveal key) input_q)
  )
  =
  AESEncryptBlock_win.aes128_encrypt_block_win output_b input_b key keys_b

let aes128_encrypt_block_BE_buffer
             (input_b output_b:B.buffer U8.t)
             (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:B.buffer U8.t)
             : Stack unit
  (requires fun h ->
    B.live h input_b /\ B.live h keys_b /\ B.live h output_b /\
    B.length  input_b % 16 == 0 /\ B.length  input_b >= 16 /\
    B.length output_b % 16 == 0 /\ B.length output_b >= 16 /\
    // Required by interop layer; not actually needed here
    disjoint_or_eq input_b output_b /\
    disjoint keys_b input_b /\
    disjoint keys_b output_b /\
    // AES reqs
    B.length keys_b == (nr AES_128 + 1) * 16 /\
    B.length keys_b % 16 == 0 /\  // REVIEW: Should be derivable from line above :(
    keys_match key keys_b h
  )
  (ensures fun h () h' ->
    B.live h' input_b /\ B.live h' output_b /\ B.live h' keys_b /\
    M.modifies (M.loc_buffer output_b) h h' /\
    (let  input_q = buffer_to_quad32  input_b h in
     let output_q = buffer_to_quad32 output_b h' in
     output_q == aes_encrypt_BE AES_128 (Ghost.reveal key) input_q)
  )
  =
  AESEncryptBE_win.aes128_encrypt_block_be_win output_b input_b key keys_b

let gctr_bytes_extra_buffer
             (plain_b:B.buffer U8.t) (num_bytes:U64.t)
             (iv_old:Ghost.erased quad32)
             (iv_b:B.buffer U8.t)
             (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:B.buffer U8.t)
             (cipher_b:B.buffer U8.t)
           : Stack unit
  (requires fun h ->
    let mods = M.loc_buffer cipher_b in
    B.live h plain_b /\ B.live h iv_b /\ B.live h keys_b /\ B.live h cipher_b /\
    disjoint plain_b cipher_b /\
    M.loc_disjoint (M.loc_buffer keys_b)  mods /\
    // Required by interop layer; not actually needed here
    buffers_disjoint [plain_b; iv_b; keys_b] /\
    disjoint iv_b cipher_b /\

    B.length plain_b  == bytes_to_quad_size (U64.v num_bytes) * 16 /\
    B.length cipher_b == B.length plain_b /\
    B.length iv_b == 16 /\
    B.length plain_b % 16 == 0 /\

    4096 * (U64.v num_bytes) < pow2_32 /\
    256 * bytes_to_quad_size (U64.v num_bytes) < pow2_32 /\

    // AES reqs
    B.length keys_b == (nr AES_128 + 1) * 16 /\
    B.length keys_b % 16 == 0 /\  // REVIEW: Should be derivable from line above :(
    keys_match key keys_b h /\

    // Extra reqs
    (let num_bytes = U64.v num_bytes in
     let num_blocks = num_bytes / 16 in
     let iv = buffer_to_quad32 iv_b h in
     num_bytes % 16 <> 0 /\
     0 < num_bytes /\ num_bytes < 16 * bytes_to_quad_size num_bytes /\
     16 * (bytes_to_quad_size num_bytes - 1) < num_bytes /\
     gctr_partial AES_128
                  num_blocks
                  (buffer_to_seq_quad32 plain_b h)
                  (buffer_to_seq_quad32  cipher_b h)
                  (Ghost.reveal key)
                  (Ghost.reveal iv_old) /\
     iv == inc32 (Ghost.reveal iv_old) num_blocks)
  )
  (ensures fun h () h' ->
    let mods = M.loc_buffer cipher_b in
    M.modifies mods h h' /\
    B.live h' plain_b /\ B.live h' iv_b /\ B.live h' keys_b /\ B.live h' cipher_b /\

    (let num_bytes = U64.v num_bytes in
     let num_blocks = num_bytes / 16 in
     let iv_new = buffer_to_quad32 iv_b h in

     // We modified cipher_b, but we didn't disrupt the work that was previously done
     let cipher_blocks  = slice (buffer_to_seq_quad32 cipher_b h)  0 num_blocks in
     let cipher_blocks' = slice (buffer_to_seq_quad32 cipher_b h') 0 num_blocks in
     cipher_blocks == cipher_blocks' /\

     // GCTR
     (let plain  = slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32  plain_b h))  0 num_bytes in
      let cipher = slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32 cipher_b h')) 0 num_bytes in
      cipher == gctr_encrypt_LE (Ghost.reveal iv_old) (make_gctr_plain_LE plain) AES_128 (Ghost.reveal key))
    )
  )
  =
  GCTR_win.gctr_bytes_extra_buffer_win plain_b num_bytes iv_old iv_b key keys_b cipher_b

let ghash_incremental_bytes_buffer (h_b hash_b input_b:B.buffer U8.t) (num_bytes:U64.t) : Stack unit
  (requires fun h ->
    B.live h h_b  /\ B.live h hash_b /\ B.live h input_b /\

    // Required by interop layer; not actually needed here
    buffers_disjoint [h_b; hash_b;input_b] /\

    B.length     h_b % 16 == 0 /\ B.length    h_b >= 16 /\
    B.length  hash_b % 16 == 0 /\ B.length hash_b >= 16 /\
    B.length input_b % 16 == 0 /\
    B.length input_b == 16 * (bytes_to_quad_size (U64.v num_bytes)) /\
    True
  )
  (ensures fun h () h' ->
    M.modifies (M.loc_buffer hash_b) h h' /\
    (let old_hash = buffer_to_quad32 hash_b h  in
     let new_hash = buffer_to_quad32 hash_b h' in
     let h_q      = buffer_to_quad32 h_b    h  in
     let num_bytes = U64.v num_bytes in
     (num_bytes == 0 ==> new_hash == old_hash) /\
     (let input_bytes = slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32 input_b h)) 0 num_bytes in
      let padded_bytes = pad_to_128_bits input_bytes in
      let input_quads = le_bytes_to_seq_quad32 padded_bytes in
      num_bytes > 0 ==>
        length input_quads > 0 /\
        new_hash == ghash_incremental h_q old_hash input_quads
     )
    )
  )
  =
  GHash_stdcall_win.ghash_incremental_bytes_stdcall_win h_b hash_b input_b num_bytes

let ghash_incremental_one_block_buffer (h_b hash_b input_b:B.buffer U8.t) (offset:U64.t) : Stack unit
  (requires fun h ->
    B.live h h_b  /\ B.live h hash_b /\ B.live h input_b /\

    // Required by interop layer; not actually needed here
    buffers_disjoint [h_b; hash_b;input_b] /\

    B.length     h_b % 16 == 0 /\ B.length    h_b >= 16 /\
    B.length  hash_b % 16 == 0 /\ B.length hash_b >= 16 /\
    B.length input_b % 16 == 0 /\
    B.length input_b >= 16 * (U64.v offset + 1) /\
    True
  )
  (ensures fun h () h' ->
    M.modifies (M.loc_buffer hash_b) h h' /\
    (let old_hash = buffer_to_quad32 hash_b h  in
     let new_hash = buffer_to_quad32 hash_b h' in
     let h_q      = buffer_to_quad32 h_b    h  in
     let offset   = U64.v offset in
     let input    = buffer_to_seq_quad32 input_b h in
     let input_quad = index input offset in
     new_hash == ghash_incremental h_q old_hash (create 1 input_quad)
    )
  )
  =
  GHash_one_block_win.ghash_incremental_one_block_buffer_win h_b hash_b input_b offset

let ghash_incremental_bytes_extra_buffer
             (in_b hash_b h_b:B.buffer U8.t) (num_bytes:U64.t)
             (orig_hash:Ghost.erased quad32)
           : Stack unit
  (requires fun h ->
    let mods = M.loc_buffer hash_b in
    B.live h in_b /\ B.live h hash_b /\ B.live h h_b /\

    buffers_disjoint [h_b; hash_b; in_b] /\

    B.length in_b  == bytes_to_quad_size (U64.v num_bytes) * 16 /\
    B.length in_b % 16 == 0 /\

    B.length h_b == 16 /\
    B.length hash_b == 16 /\

    4096 * (U64.v num_bytes) < pow2_32 /\
    256 * bytes_to_quad_size (U64.v num_bytes) < pow2_32 /\

    (let num_bytes = U64.v num_bytes in
     let num_blocks = num_bytes / 16 in
     let old_hash = buffer_to_quad32 hash_b h in
     //let new_hash = buffer_to_quad32 hash_b h' in
     let h_val = buffer_to_quad32 h_b h in

     // GHash reqs
     let input = slice (buffer_to_seq_quad32 in_b h) 0 num_blocks in
     old_hash == ghash_incremental0 h_val (Ghost.reveal orig_hash) input /\

     // Extra reqs
     num_bytes % 16 <> 0 /\
     0 < num_bytes /\ num_bytes < 16 * bytes_to_quad_size num_bytes /\
     16 * (bytes_to_quad_size num_bytes - 1) < num_bytes /\

     True
    )
  )
  (ensures fun h () h' ->
    let mods = M.loc_buffer hash_b in
    M.modifies mods h h' /\
    B.live h in_b /\ B.live h hash_b /\ B.live h h_b /\
    (let num_bytes = U64.v num_bytes in
     let num_blocks = num_bytes / 16 in
     let old_hash = buffer_to_quad32 hash_b h in
     let new_hash = buffer_to_quad32 hash_b h' in
     let h_val = buffer_to_quad32 h_b h in

     let input_bytes = slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32 in_b h')) 0 num_bytes in
     let padded_bytes = pad_to_128_bits input_bytes in
     let input_quads = le_bytes_to_seq_quad32 padded_bytes in
     (num_bytes > 0 ==> length input_quads > 0 /\
                       new_hash == ghash_incremental h_val (Ghost.reveal orig_hash) input_quads)
    )
  )
  =
  GHash_extra_win.ghash_incremental_extra_stdcall_win in_b hash_b h_b num_bytes orig_hash

let gcm_load_xor_store_buffer
       (plain_b mask_b cipher_b:B.buffer U8.t)
       (offset:U64.t)
       (num_blocks:(Ghost.erased U64.t))
       (key:Ghost.erased (aes_key_LE AES_128))
       (iv:(Ghost.erased quad32))
       : Stack unit
  (requires fun h ->
    B.live h plain_b /\ B.live h mask_b /\ B.live h cipher_b /\
    disjoint plain_b cipher_b /\
    disjoint mask_b  cipher_b /\

    // Required by interop layer; not actually needed here
    disjoint plain_b mask_b /\

    B.length plain_b  >= (U64.v (Ghost.reveal num_blocks)) * 16 /\
    B.length cipher_b == B.length plain_b /\
    B.length mask_b == 16 /\
    B.length plain_b % 16 == 0 /\
    (let offset = U64.v offset in
     let num_blocks = U64.v (Ghost.reveal num_blocks) in
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
  (ensures fun h () h' ->
    let mods = M.loc_buffer cipher_b in
    M.modifies mods h h' /\
    B.live h plain_b /\ B.live h mask_b /\ B.live h cipher_b /\
    (let offset = U64.v offset in
     let num_blocks = U64.v (Ghost.reveal num_blocks) in
     let mask   = buffer_to_quad32       mask_b h in
     let plain  = buffer_to_seq_quad32  plain_b h' in
     let old_cipher = buffer_to_seq_quad32 cipher_b h in
     let cipher = buffer_to_seq_quad32 cipher_b h' in
     let key = Ghost.reveal key in
     let iv = Ghost.reveal iv in
     gctr_partial AES_128 (offset + 1) plain cipher key iv /\
     slice cipher 0 offset == slice old_cipher 0 offset  // We didn't disrupt earlier slots
    )
  )
  =
  let num_blocks = Ghost.hide (U64.v (Ghost.reveal num_blocks)) in
  let h = ST.get() in
  Gcm_load_xor_win.gcm_load_xor_store_buffer_win plain_b mask_b cipher_b offset num_blocks key iv

let inc32_buffer (iv_b:B.buffer U8.t) : Stack unit
  (requires fun h ->
    B.live h iv_b /\
    B.length iv_b == 16
  )
  (ensures fun h () h' ->
    M.modifies (M.loc_buffer iv_b) h h' /\
    (let old_iv = buffer_to_quad32 iv_b h  in
     let new_iv = buffer_to_quad32 iv_b h' in
     new_iv == inc32 old_iv 1))
  =
  Inc32_win.inc32_buffer_win iv_b

let zero_quad32_buffer (b:B.buffer U8.t) : Stack unit
  (requires fun h ->
    B.live h b /\
    B.length b == 16
  )
  (ensures fun h () h' ->
    M.modifies (M.loc_buffer b) h h' /\
    (let new_b = buffer_to_quad32 b h' in
     new_b == Mkfour 0 0 0 0)
  )
  =
  Zero_quad32_win.zero_quad32_buffer_win b

let reverse_bytes_quad32_buffer (b:B.buffer U8.t) : Stack unit
  (requires fun h ->
    B.live h b /\
    B.length b == 16
  )
  (ensures fun h () h' ->
    M.modifies (M.loc_buffer b) h h' /\
    (let old_b = buffer_to_quad32 b h  in
     let new_b = buffer_to_quad32 b h' in
     new_b == reverse_bytes_quad32 old_b)
  )
  =
  Reverse_quad32_win.reverse_bytes_quad32_buffer_win b

let mk_quad32_lo0_be_1_buffer (b:B.buffer U8.t) : Stack unit
  (requires fun h ->
    B.live h b /\
    B.length b == 16
  )
  (ensures fun h () h' ->
    M.modifies (M.loc_buffer b) h h' /\
    (let old_b = buffer_to_quad32 b h  in
     let new_b = buffer_to_quad32 b h' in
     new_b == Mkfour 1 old_b.lo1 old_b.hi2 old_b.hi3)
  )
  =
  Mk_quad32_1_win.mk_quad32_lo0_be_1_buffer_win b

let gcm_make_length_quad_buffer
  (plain_num_bytes auth_num_bytes:U64.t)
  (b:B.buffer U8.t)
  : Stack unit
  (requires fun h ->
    B.live h b /\
    B.length b == 16 /\
    8 * (U64.v plain_num_bytes) < pow2_32 /\
    8 * (U64.v  auth_num_bytes) < pow2_32
  )
  (ensures fun h () h' ->
    M.modifies (M.loc_buffer b) h h' /\
    (let new_b = buffer_to_quad32 b h' in
     new_b == reverse_bytes_quad32 (Mkfour (8 * (U64.v plain_num_bytes)) 0 (8 * (U64.v auth_num_bytes)) 0))
  )
  =
  Gcm_make_length_win.gcm_make_length_quad_buffer_win plain_num_bytes auth_num_bytes b


let quad32_xor_buffer
  (src1 src2 dst:B.buffer U8.t)
  : Stack unit
  (requires fun h ->
    B.live h src1 /\ B.live h src2 /\ B.live h dst /\

    // Required by interop layer; not actually needed here
    disjoint_or_eq src1 src2 /\
    disjoint_or_eq src1 dst /\
    disjoint_or_eq src2 dst /\

    B.length src1 == 16 /\ B.length src2 == 16 /\ B.length dst == 16
  )
  (ensures fun h () h' ->
    M.modifies (M.loc_buffer dst) h h' /\
    (let src1 = buffer_to_quad32 src1 h  in
     let src2 = buffer_to_quad32 src2 h  in
     let dst  = buffer_to_quad32 dst  h' in
     dst = quad32_xor src1 src2)
  )
  =
  Quad32_xor_win.quad32_xor_buffer_win src1 src2 dst

(*** Actual Low* code ***)

#reset-options "--z3rlimit 150"
let gcm128_one_pass_blocks
             (plain_b:B.buffer U8.t) (num_blocks:U64.t)
             (iv_b:B.buffer U8.t)
             (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:B.buffer U8.t)
             (cipher_b:B.buffer U8.t)
             (h_b hash_b:B.buffer U8.t)
           : Stack unit
  (requires fun h ->
    let mods = M.(loc_union (loc_buffer cipher_b)
                 (loc_union (loc_buffer iv_b)
                            (loc_buffer hash_b))) in
    B.live h plain_b /\ B.live h iv_b /\ B.live h keys_b /\ B.live h cipher_b /\
    B.live h h_b /\ B.live h hash_b /\
    M.loc_disjoint (M.loc_buffer plain_b) mods /\
    M.loc_disjoint (M.loc_buffer keys_b)  mods /\
    M.loc_disjoint (M.loc_buffer h_b)  mods /\
    M.(loc_disjoint (loc_buffer cipher_b) (loc_buffer   iv_b)) /\
    M.(loc_disjoint (loc_buffer cipher_b) (loc_buffer hash_b)) /\
    M.(loc_disjoint (loc_buffer iv_b)     (loc_buffer hash_b)) /\

    B.length plain_b  >= U64.v num_blocks * 16 /\
    B.length cipher_b == B.length plain_b /\
    B.length iv_b == 16 /\
    B.length h_b == 16 /\
    B.length hash_b == 16 /\
    B.length plain_b % 16 == 0 /\

    // AES reqs
    B.length keys_b == (nr AES_128 + 1) * 16 /\
    B.length keys_b % 16 == 0 /\  // REVIEW: Should be derivable from line above :(
    keys_match key keys_b h
  )
  (ensures fun h () h' ->
    let mods = M.(loc_union (loc_buffer cipher_b)
                 (loc_union (loc_buffer iv_b)
                            (loc_buffer hash_b))) in
    M.modifies mods h h' /\
    B.live h' plain_b /\ B.live h' iv_b /\ B.live h' keys_b /\ B.live h' cipher_b /\
    B.live h' h_b /\ B.live h' hash_b /\
    (let num_blocks = U64.v num_blocks in
      gctr_partial AES_128 num_blocks (buffer_to_seq_quad32 plain_b h') (buffer_to_seq_quad32 cipher_b h') (Ghost.reveal key) (buffer_to_quad32 iv_b h) /\
      buffer_to_quad32 iv_b h' == inc32 (buffer_to_quad32 iv_b h) num_blocks /\
      (let old_hash = buffer_to_quad32 hash_b h in
       let new_hash = buffer_to_quad32 hash_b h' in
       let h_val = buffer_to_quad32 h_b h in
       (num_blocks == 0 ==> old_hash == new_hash) /\
       (num_blocks > 0 ==>
         (let out_s = buffer_to_seq_quad32 cipher_b h' in
           length out_s > 0 /\
           new_hash == ghash_incremental h_val old_hash (slice out_s 0 num_blocks)
         )
       )
      )
    )
  )
  =
  push_frame();
  let h0 = ST.get() in
  let enc_ctr_b = B.alloca (U8.uint_to_t 0) 16ul in
  let inv h (i:nat) =
    i <= U64.v num_blocks /\
    B.live h plain_b /\ B.live h iv_b /\ B.live h keys_b /\ B.live h cipher_b /\
    B.live h h_b /\ B.live h hash_b /\
    B.live h enc_ctr_b /\
    (let mods = M.(loc_union (loc_buffer cipher_b)
                  (loc_union (loc_buffer iv_b)
                  (loc_union (loc_buffer enc_ctr_b)
                             (loc_buffer hash_b)))) in

    M.modifies mods h0 h) /\

    // AES reqs
    B.length keys_b == (nr AES_128 + 1) * 16 /\
    B.length keys_b % 16 == 0 /\  // REVIEW: Should be derivable from line above :(
    keys_match key keys_b h /\

    // Interesting loop invariants
    (let old_iv = buffer_to_quad32 iv_b h0 in
     let new_iv = buffer_to_quad32 iv_b h in
     let plain  = buffer_to_seq_quad32  plain_b h in
     let cipher = buffer_to_seq_quad32 cipher_b h in
     let old_hash = buffer_to_quad32 hash_b h0 in
     let new_hash = buffer_to_quad32 hash_b h in
     let h_val = buffer_to_quad32 h_b h in
     let key = Ghost.reveal key in
     new_iv == inc32 old_iv i /\
     gctr_partial AES_128 i plain cipher key old_iv /\
     (i == 0 ==> new_hash == old_hash) /\
     (i  > 0 ==> new_hash == ghash_incremental h_val old_hash (slice cipher 0 i))
    )
  in
  (* This is the preferred style and useful for debugging the body.
     However, there's a "unification/delta_depth issue" somewhere, so we have to inline it below
  let body (i:U64.t{ U64.v 0UL <= U64.v i /\ U64.v i < U64.v num_blocks }) : Stack unit
    (requires (fun h -> inv h (U64.v i)))
    (ensures (fun h () h' -> inv h (U64.v i) /\ inv h' (U64.v i + 1)))
    =
     // Compute the encryption of the counter value
    aes128_encrypt_block_BE_buffer iv_b enc_ctr_b key keys_b;

    // Xor the encrypted counter to the plaintext, to make progress on the gctr computation
    let iv = Ghost.elift2 buffer_to_quad32 (Ghost.hide iv_b) (Ghost.hide h0) in
    gcm_load_xor_store_buffer plain_b enc_ctr_b cipher_b i (Ghost.hide num_blocks) key iv;

    // Update our hash
    ghash_incremental_one_block_buffer h_b hash_b cipher_b i;
    Opaque_s.reveal_opaque ghash_incremental_def;

    // Increment the ctr
    inc32_buffer iv_b;
    ()
  in *)
  C.Loops.for64 0UL num_blocks inv
    (fun (i:U64.t{ U64.v 0UL <= U64.v i /\ U64.v i < U64.v num_blocks }) ->
      // Compute the encryption of the counter value
      aes128_encrypt_block_BE_buffer iv_b enc_ctr_b key keys_b;

      // Xor the encrypted counter to the plaintext, to make progress on the gctr computation
      let iv = Ghost.elift2 buffer_to_quad32 (Ghost.hide iv_b) (Ghost.hide h0) in
      gcm_load_xor_store_buffer plain_b enc_ctr_b cipher_b i (Ghost.hide num_blocks) key iv;

      // Update our hash
      ghash_incremental_one_block_buffer h_b hash_b cipher_b i;
      Opaque_s.reveal_opaque ghash_incremental_def;

      // Increment the ctr
      inc32_buffer iv_b;
      ()
    )
  ;
  pop_frame();
  ()

#reset-options "--z3rlimit 20"
let gcm128_one_pass
             (plain_b:B.buffer U8.t) (num_bytes:U64.t)
             (iv_b:B.buffer U8.t)
             (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:B.buffer U8.t)
             (cipher_b:B.buffer U8.t)
             (h_b hash_b:B.buffer U8.t)
           : Stack unit
  (requires fun h ->
    let mods = M.(loc_union (loc_buffer cipher_b)
                 (loc_union (loc_buffer iv_b)
                            (loc_buffer hash_b))) in
    B.live h plain_b /\ B.live h iv_b /\ B.live h keys_b /\ B.live h cipher_b /\
    B.live h h_b /\ B.live h hash_b /\
    M.loc_disjoint (M.loc_buffer plain_b) mods /\
    M.loc_disjoint (M.loc_buffer keys_b)  mods /\
    M.loc_disjoint (M.loc_buffer h_b)     mods /\

    M.(loc_disjoint (loc_buffer iv_b) (loc_buffer cipher_b)) /\
    M.(loc_disjoint (loc_buffer hash_b) (loc_buffer cipher_b)) /\
    M.(loc_disjoint (loc_buffer hash_b) (loc_buffer iv_b)) /\

    // Required by interop layer; not actually needed here
    disjoint plain_b keys_b /\

    B.length plain_b  == bytes_to_quad_size (U64.v num_bytes) * 16 /\
    B.length cipher_b == B.length plain_b /\
    B.length iv_b == 16 /\
    B.length h_b == 16 /\
    B.length hash_b == 16 /\
    B.length plain_b % 16 == 0 /\

    4096 * (U64.v num_bytes) < pow2_32 /\
    256 * bytes_to_quad_size (U64.v num_bytes) < pow2_32 /\

    // AES reqs
    B.length keys_b == (nr AES_128 + 1) * 16 /\
    B.length keys_b % 16 == 0 /\  // REVIEW: Should be derivable from line above :(
    keys_match key keys_b h
  )
  (ensures fun h () h' ->
    let mods = M.(loc_union (loc_buffer cipher_b)
                 (loc_union (loc_buffer iv_b)
                            (loc_buffer hash_b))) in
    M.modifies mods h h' /\
    // REVIEW: Do we really need to relist all of these liveness predicates?
    B.live h' plain_b /\ B.live h' iv_b /\ B.live h' keys_b /\ B.live h' cipher_b /\
    B.live h' h_b /\ B.live h' hash_b /\
    (let num_bytes = U64.v num_bytes in
     let iv_old = buffer_to_quad32 iv_b h in
     let iv_new = buffer_to_quad32 iv_b h' in
     let old_hash = buffer_to_quad32 hash_b h in
     let new_hash = buffer_to_quad32 hash_b h' in
     let h_val = buffer_to_quad32 h_b h in

     // GCTR
     let plain  = slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32  plain_b h))  0 num_bytes in
     let cipher = slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32 cipher_b h')) 0 num_bytes in
     cipher == gctr_encrypt_LE iv_old (make_gctr_plain_LE plain) AES_128 (Ghost.reveal key) /\

     iv_new.lo1 == iv_old.lo1 /\
     iv_new.hi2 == iv_old.hi2 /\
     iv_new.hi3 == iv_old.hi3 /\

     // GHash
     (num_bytes == 0 ==> old_hash == new_hash) /\
     (let cipher_padded_bytes = pad_to_128_bits cipher in
      let cipher_padded_quads = le_bytes_to_seq_quad32 cipher_padded_bytes in
      (num_bytes > 0 ==>
        length cipher_padded_quads > 0 /\
        new_hash == ghash_incremental h_val old_hash cipher_padded_quads
      )
    )
   ) /\
  True)
  =
  let h0 = ST.get() in
  if UInt64.gt num_bytes 0UL then (
    let num_blocks = U64.div num_bytes 16UL in
    let num_extra = U64.rem num_bytes 16UL in
    gcm128_one_pass_blocks plain_b num_blocks iv_b key keys_b cipher_b h_b hash_b;
    let h1 = ST.get() in
    //assert (gctr_partial AES_128 (U64.v num_blocks) (buffer_to_seq_quad32 plain_b h1) (buffer_to_seq_quad32 cipher_b h1) (Ghost.reveal key) (buffer_to_quad32 iv_b h0));
    (*
    assert (let c = buffer_to_seq_quad32 cipher_b h1 in
            (U64.v num_blocks) > 0 ==> length c > 0 /\
            buffer_to_quad32 hash_b h1 ==
            ghash_incremental (buffer_to_quad32 h_b h0)
                              (buffer_to_quad32 hash_b h0)
                              (slice c 0 (U64.v num_blocks)));
    *)
    if num_extra = 0UL then (
      // No work to be done.  Just call a bunch of lemmas

      // From gctr_bytes_no_extra(), we get:
      gctr_partial_completed AES_128
                             (buffer_to_seq_quad32 plain_b h1)
                             (buffer_to_seq_quad32 cipher_b h1)
                             (Ghost.reveal key)
                             (buffer_to_quad32 iv_b h0);
      gctr_partial_to_full_basic (buffer_to_quad32 iv_b h0)
                                 (buffer_to_seq_quad32 plain_b h1)
                                 AES_128
                                 (Ghost.reveal key)
                                 (buffer_to_seq_quad32 cipher_b h1);
      no_extra_bytes_helper (buffer_to_seq_quad32 plain_b h1) (U64.v num_bytes);
      no_extra_bytes_helper (buffer_to_seq_quad32 cipher_b h1) (U64.v num_bytes);

      // From ghash_incremental_bytes_no_extra() we get the following,
      // after eliminating redundancies with lemma calls above):
      le_bytes_to_seq_quad32_to_bytes (buffer_to_seq_quad32 cipher_b h1);

      // From gcm_one_pass, we get:
      bytes_to_quad_size_no_extra_bytes (U64.v num_bytes);

      // Prove a property about le_bytes_to_seq_quad32 while trying to keep its definition hidden
      let length_helper (x:int) : Lemma (forall y . {:pattern length (le_bytes_to_seq_quad32 y)}
                                             length y > 0 ==> length (le_bytes_to_seq_quad32 y) > 0) =
        Opaque_s.reveal_opaque le_bytes_to_seq_quad32_def
      in
      length_helper 0;
      ()
    ) else (
      let iv_old = Ghost.elift2 buffer_to_quad32 (Ghost.hide iv_b) (Ghost.hide h0) in
      let hash_old = Ghost.elift2 buffer_to_quad32 (Ghost.hide hash_b) (Ghost.hide h0) in
      gctr_bytes_extra_buffer plain_b num_bytes iv_old iv_b key keys_b cipher_b;
      ghash_incremental_bytes_extra_buffer cipher_b hash_b h_b num_bytes hash_old;
      ()
    )
  ) else (
    // Wow, this is a painful way to handle ghost values :(
    let plain  = Ghost.elift2 buffer_to_seq_quad32  (Ghost.hide plain_b)  (Ghost.hide h0) in
    let cipher = Ghost.elift2 buffer_to_seq_quad32  (Ghost.hide cipher_b) (Ghost.hide h0) in
    let old_iv = Ghost.elift2 buffer_to_quad32      (Ghost.hide iv_b)     (Ghost.hide h0) in
    gctr_encrypt_empty (Ghost.reveal old_iv)
                       (Ghost.reveal plain)
                       (Ghost.reveal cipher)
                       AES_128
                       (Ghost.reveal key);
    ()
  );
  ()

#set-options "--z3rlimit 150"

let gcm_core_part1
    (plain_b:B.buffer U8.t) (plain_num_bytes:U64.t)
    (auth_b:B.buffer U8.t)  (auth_num_bytes:U64.t)
    (iv_b:B.buffer U8.t)
    (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:B.buffer U8.t)
    (cipher_b:B.buffer U8.t)
    (h_b hash_b:B.buffer U8.t)
    : ST (Ghost.erased quad32x3)
  (requires fun h ->
      let mods = M.((loc_union (loc_buffer cipher_b)
                    (loc_union (loc_buffer iv_b)
                    (loc_union (loc_buffer h_b)
                               (loc_buffer hash_b))))) in
      B.live h plain_b /\ B.live h auth_b /\ B.live h iv_b /\ B.live h keys_b /\ B.live h cipher_b /\
      B.live h h_b /\ B.live h hash_b /\

      M.loc_disjoint (M.loc_buffer plain_b) mods /\
      M.loc_disjoint (M.loc_buffer auth_b) mods /\
      M.loc_disjoint (M.loc_buffer keys_b)  mods /\

      M.(loc_disjoint (loc_buffer iv_b) (loc_buffer cipher_b)) /\
      M.(loc_disjoint (loc_buffer hash_b) (loc_buffer cipher_b)) /\
      M.(loc_disjoint (loc_buffer hash_b) (loc_buffer iv_b)) /\
      M.(loc_disjoint (loc_buffer h_b) (loc_buffer iv_b)) /\
      M.(loc_disjoint (loc_buffer h_b) (loc_buffer cipher_b)) /\
      M.(loc_disjoint (loc_buffer h_b) (loc_buffer hash_b)) /\

      // Required by interop layer; not actually needed here
      disjoint plain_b keys_b /\

      B.length plain_b  == bytes_to_quad_size (U64.v plain_num_bytes) * 16 /\
      B.length auth_b   == bytes_to_quad_size (U64.v auth_num_bytes) * 16 /\
      B.length cipher_b == B.length plain_b /\
      B.length iv_b     == 16 /\
      B.length h_b == 16 /\
      B.length hash_b == 16 /\

      4096 * (U64.v plain_num_bytes) < pow2_32 /\
      4096 * (U64.v auth_num_bytes)  < pow2_32 /\
      256 * bytes_to_quad_size (U64.v plain_num_bytes) < pow2_32 /\
      256 * bytes_to_quad_size (U64.v auth_num_bytes)  < pow2_32 /\

      // AES reqs
      B.length keys_b == (nr AES_128 + 1) * 16 /\
      B.length keys_b % 16 == 0 /\  // REVIEW: Should be derivable from line above :(
      keys_match key keys_b h
  )
  (ensures fun h q3 h' ->
    let mods = M.((loc_union (loc_buffer cipher_b)
                    (loc_union (loc_buffer iv_b)
                    (loc_union (loc_buffer h_b)
                               (loc_buffer hash_b))))) in
    B.live h plain_b /\ B.live h auth_b /\ B.live h iv_b /\ B.live h keys_b /\ B.live h cipher_b /\
    B.live h h_b /\ B.live h hash_b /\

    M.modifies mods h h' /\

    (let plain_num_bytes = U64.v plain_num_bytes in
     let auth_num_bytes = U64.v auth_num_bytes in
     let iv_old = reverse_bytes_quad32 (buffer_to_quad32 iv_b h) in
     let iv_new = buffer_to_quad32 iv_b h' in
     let old_hash = buffer_to_quad32 hash_b h in
     let new_hash = buffer_to_quad32 hash_b h' in
     let h_val = buffer_to_quad32 h_b h' in
     let auth   = slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32   auth_b h))  0 auth_num_bytes in
     let plain  = slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32  plain_b h))  0 plain_num_bytes in
     let cipher = slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32 cipher_b h')) 0 plain_num_bytes in
     let (y_0, y_auth, y_cipher) = (Ghost.reveal q3) in
     let auth_padded_bytes = pad_to_128_bits auth in
     let auth_padded_quads = le_bytes_to_seq_quad32 auth_padded_bytes in
     let cipher_padded_bytes = pad_to_128_bits cipher in
     let cipher_padded_quads = le_bytes_to_seq_quad32 cipher_padded_bytes in

     // GCTR
     let k = seq_nat32_to_seq_nat8_LE (Ghost.reveal key) in
     cipher == fst (gcm_encrypt_LE AES_128 k (be_quad32_to_bytes iv_old) plain auth) /\

     // Intermediate hash state needed for the next step
     y_0      == Mkfour 0 0 0 0 /\
     y_auth   == ghash_incremental0 h_val y_0    auth_padded_quads /\
     y_cipher == ghash_incremental0 h_val y_auth cipher_padded_quads /\
     new_hash == y_cipher /\
     h_val == aes_encrypt_LE AES_128 (Ghost.reveal key) y_0 /\

     // Intermediate IV state
     iv_new.lo1 == iv_old.lo1 /\
     iv_new.hi2 == iv_old.hi2 /\
     iv_new.hi3 == iv_old.hi3 /\
    True)
  )
  =
  let h0 = ST.get() in
  let iv_LE = Ghost.elift2 buffer_to_quad32 (Ghost.hide iv_b) (Ghost.hide h0) in
  let iv_BE = Ghost.hide (reverse_bytes_quad32 (Ghost.reveal iv_LE)) in
  push_frame ();
  zero_quad32_buffer h_b;
  zero_quad32_buffer hash_b;
  aes128_encrypt_block_buffer h_b h_b key keys_b;  // h = aes_encrypt_LE alg key (Mkfour 0 0 0 0)
  let h1 = ST.get() in
  let y_0 = Ghost.hide (Mkfour 0 0 0 0) in
  ghash_incremental_bytes_buffer h_b hash_b auth_b auth_num_bytes;
  let h2 = ST.get() in

  let y_auth = Ghost.elift2 buffer_to_quad32 (Ghost.hide hash_b) (Ghost.hide h2) in
  reverse_bytes_quad32_buffer iv_b;
  mk_quad32_lo0_be_1_buffer iv_b;
  inc32_buffer iv_b;  // iv_b == old(iv_b)[lo0 := 2]
  let h3 = ST.get() in

  let icb_enc = Ghost.elift2 buffer_to_quad32 (Ghost.hide iv_b) (Ghost.hide h3) in
  gcm128_one_pass plain_b plain_num_bytes iv_b key keys_b cipher_b h_b hash_b;
  let h4 = ST.get() in
  let y_cipher = Ghost.elift2 buffer_to_quad32 (Ghost.hide hash_b) (Ghost.hide h4) in
  GCM.gcm_encrypt_LE_fst_helper
    (Ghost.reveal icb_enc)
    (Ghost.reveal iv_BE)
    (slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32  plain_b h0)) 0 (U64.v plain_num_bytes))
    (slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32   auth_b h0)) 0 (U64.v auth_num_bytes))
    (slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32 cipher_b h4)) 0 (U64.v plain_num_bytes))
    AES_128
    (Ghost.reveal key);
  Opaque_s.reveal_opaque le_bytes_to_seq_quad32_def;
  pop_frame();
  Ghost.hide (Ghost.reveal y_0, Ghost.reveal y_auth, Ghost.reveal y_cipher)


#reset-options "--z3rlimit 50"
let gcm_core
    (plain_b:B.buffer U8.t) (plain_num_bytes:U64.t)
    (auth_b:B.buffer U8.t)  (auth_num_bytes:U64.t)
    (iv_b:B.buffer U8.t)
    (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:B.buffer U8.t)
    (cipher_b:B.buffer U8.t)
    (tag_b:B.buffer U8.t) : ST unit
  (requires fun h ->
      let mods = M.((loc_union (loc_buffer cipher_b)
                    (loc_union (loc_buffer iv_b)
                               (loc_buffer tag_b)))) in
      B.live h plain_b /\ B.live h auth_b /\ B.live h iv_b /\ B.live h keys_b /\
      B.live h cipher_b /\ B.live h tag_b /\

      M.loc_disjoint (M.loc_buffer plain_b) mods /\
      M.loc_disjoint (M.loc_buffer auth_b) mods /\
      M.loc_disjoint (M.loc_buffer keys_b)  mods /\

      M.(loc_disjoint (loc_buffer iv_b) (loc_buffer cipher_b)) /\
      M.(loc_disjoint (loc_buffer tag_b) (loc_buffer cipher_b)) /\
      M.(loc_disjoint (loc_buffer iv_b) (loc_buffer tag_b)) /\

      // Required by interop layer; not actually needed here
      disjoint plain_b keys_b /\

      B.length plain_b  == bytes_to_quad_size (U64.v plain_num_bytes) * 16 /\
      B.length auth_b   == bytes_to_quad_size (U64.v auth_num_bytes) * 16 /\
      B.length cipher_b == B.length plain_b /\
      B.length iv_b     == 16 /\
      B.length tag_b    == 16 /\

      4096 * (U64.v plain_num_bytes) < pow2_32 /\
      4096 * (U64.v auth_num_bytes)  < pow2_32 /\
      256 * bytes_to_quad_size (U64.v plain_num_bytes) < pow2_32 /\
      256 * bytes_to_quad_size (U64.v auth_num_bytes)  < pow2_32 /\

      // AES reqs
      B.length keys_b == (nr AES_128 + 1) * 16 /\
      B.length keys_b % 16 == 0 /\  // REVIEW: Should be derivable from line above :(
      keys_match key keys_b h
  )
  (ensures fun h () h' ->
    let mods = M.((loc_union (loc_buffer cipher_b)
                  (loc_union (loc_buffer iv_b)
                             (loc_buffer tag_b)))) in
    M.modifies mods h h' /\

    (let plain_num_bytes = U64.v plain_num_bytes in
     let auth_num_bytes = U64.v auth_num_bytes in
     let iv_old = be_quad32_to_bytes (reverse_bytes_quad32 (buffer_to_quad32 iv_b h)) in
     let tag = buffer_to_quad32 tag_b h' in
     let auth   = slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32   auth_b h))  0 auth_num_bytes in
     let plain  = slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32  plain_b h))  0 plain_num_bytes in
     let cipher = slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32 cipher_b h')) 0 plain_num_bytes in
     let k = seq_nat32_to_seq_nat8_LE (Ghost.reveal key) in

     cipher == fst (gcm_encrypt_LE AES_128 k iv_old plain auth) /\
     le_quad32_to_bytes tag == snd  (gcm_encrypt_LE AES_128 k iv_old plain auth)
    )
  )
  =
  let h0 = ST.get() in
  let iv_LE = Ghost.elift2 buffer_to_quad32 (Ghost.hide iv_b) (Ghost.hide h0) in
  let iv_BE = Ghost.hide (reverse_bytes_quad32 (Ghost.reveal iv_LE)) in
  push_frame ();
  let h_b = B.alloca (U8.uint_to_t 0) 16ul in
  let hash_b = B.alloca (U8.uint_to_t 0) 16ul in
  let h1 = ST.get() in
  let ys = gcm_core_part1 plain_b plain_num_bytes
                           auth_b  auth_num_bytes
                          iv_b
                          key keys_b
                          cipher_b
                          h_b hash_b in
  let h2 = ST.get() in
  let length_quad_b = B.alloca (U8.uint_to_t 0) 16ul in
  gcm_make_length_quad_buffer plain_num_bytes auth_num_bytes length_quad_b;
  let h3 = ST.get() in
  ghash_incremental_one_block_buffer h_b hash_b length_quad_b 0UL;
  let h4 = ST.get() in
  let y_final = Ghost.elift2 buffer_to_quad32 (Ghost.hide hash_b) (Ghost.hide h4) in

  // Invoke lemma showing that incremental hashing works
  let lemma_hash_works () :
    Lemma (let h_val = buffer_to_quad32 h_b h2 in
           let y_final = Ghost.reveal y_final in
           let auth = le_seq_quad32_to_bytes (buffer_to_seq_quad32 auth_b h0) in
           let auth_bytes = slice auth 0 (U64.v auth_num_bytes) in
           let auth_padded_quads = le_bytes_to_seq_quad32 (pad_to_128_bits auth_bytes) in
           let cipher = le_seq_quad32_to_bytes (buffer_to_seq_quad32 cipher_b h4) in
           let cipher_bytes = slice cipher 0 (U64.v plain_num_bytes) in
           let cipher_padded_quads = le_bytes_to_seq_quad32 (pad_to_128_bits cipher_bytes) in
           let length_quads = create 1 (buffer_to_quad32 length_quad_b h3) in
           y_final == ghash_LE h_val (append auth_padded_quads
                                             (append cipher_padded_quads length_quads)))
    =
    let h_val = buffer_to_quad32 h_b h2 in
    let y_final = Ghost.reveal y_final in
    let auth = le_seq_quad32_to_bytes (buffer_to_seq_quad32 auth_b h0) in
    let auth_bytes = slice auth 0 (U64.v auth_num_bytes) in
    let auth_padded_quads = le_bytes_to_seq_quad32 (pad_to_128_bits auth_bytes) in
    let cipher = le_seq_quad32_to_bytes (buffer_to_seq_quad32 cipher_b h4) in
    let cipher_bytes = slice cipher 0 (U64.v plain_num_bytes) in
    let cipher_padded_quads = le_bytes_to_seq_quad32 (pad_to_128_bits cipher_bytes) in
    let length_quads = create 1 (buffer_to_quad32 length_quad_b h3) in
    let (y_0, y_auth, y_cipher) = Ghost.reveal ys in
    buffer_to_seq_quad32_0 length_quad_b h3; // Prove the following:
    //assert (index (buffer_to_seq_quad32 length_quad_b h3) 0 == buffer_to_quad32 length_quad_b h3);

    lemma_hash_append3 h_val y_0 y_auth y_cipher y_final
                       auth_padded_quads cipher_padded_quads length_quads
  in
  lemma_hash_works();

  // Encrypt the hash to generate the tag
  mk_quad32_lo0_be_1_buffer iv_b;                       // Reset the IV
  let h5 = ST.get() in
  aes128_encrypt_block_BE_buffer iv_b iv_b key keys_b;  // Encrypt the IV
  quad32_xor_buffer hash_b iv_b tag_b;                  // Compute GCTR with hash as input
  let h6 = ST.get() in

  // Prove that we calculated the tag correctly
  gctr_encrypt_one_block (buffer_to_quad32 iv_b h5) (Ghost.reveal y_final) AES_128 (Ghost.reveal key);

  le_seq_quad32_to_bytes_of_singleton (buffer_to_quad32 tag_b h6);

  GCM.gcm_encrypt_LE_snd_helper
    (Ghost.reveal iv_BE)
    (buffer_to_quad32 length_quad_b h3)
    (Ghost.reveal y_final)
    (buffer_to_quad32 tag_b h6)
    (let plain = le_seq_quad32_to_bytes (buffer_to_seq_quad32 plain_b h0) in
     let plain_bytes = slice plain 0 (U64.v plain_num_bytes) in
     plain_bytes)
    (let auth = le_seq_quad32_to_bytes (buffer_to_seq_quad32 auth_b h0) in
     let auth_bytes = slice auth 0 (U64.v auth_num_bytes) in
     auth_bytes)
    (let cipher = le_seq_quad32_to_bytes (buffer_to_seq_quad32 cipher_b h4) in
     let cipher_bytes = slice cipher 0 (U64.v plain_num_bytes) in
     cipher_bytes)
    AES_128
    (Ghost.reveal key);
  pop_frame();
  ()
