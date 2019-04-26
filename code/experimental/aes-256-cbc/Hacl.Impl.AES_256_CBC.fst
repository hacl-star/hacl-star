module Hacl.Impl.AES_256_CBC

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.AES_256

#set-options "--max_fuel 0 --initial_fuel 0 --max_ifuel 0 --initial_ifuel 0"

val padPKCS: tmp:block -> len:size_t{v len <= v blocklen} -> idx:size_t{v idx <= v blocklen} -> Stack unit
	 (requires (fun h -> live h tmp))
	 (ensures (fun h0 _ h1 -> modifies1 tmp h0 h1))
	 (decreases (v blocklen - v idx))
let rec padPKCS tmp len idx =
    if idx = blocklen then ()
    else (tmp.(idx) <- cast U8 SEC len; padPKCS tmp len (idx +. size 1))

val padISO: tmp:block -> len:size_t{v len <= 16} -> idx:size_t{v idx < 16} -> Stack unit
	 (requires (fun h -> live h tmp))
	 (ensures (fun h0 _ h1 -> modifies1 tmp h0 h1))
let padISO tmp b idx =
    tmp.(idx) <- u8 0x80

val aes256_cbc_encrypt:
  out:buffer uint8 ->
  key:lbuffer uint8 keylen ->
  iv:block ->
  msg:buffer uint8{length msg + 16 == length out} ->
  msglen:size_t{v msglen = length msg /\ (v msglen / 16) * 16 + 16 <= max_size_t /\ v msglen > 0} ->
  Stack size_t
    (requires (fun h -> live h out /\ live h key /\ live h iv /\ live h msg /\
      disjoint out key /\ disjoint out iv /\ disjoint out msg
    ))
    (ensures (fun h0 _ h1 -> modifies1 out h0 h1))

#reset-options "--max_fuel 0 --initial_fuel 0 --max_ifuel 0 --initial_ifuel 0 --z3rlimit 50"

let aes256_cbc_encrypt out key iv msg msglen =
  push_frame ();
  let fullblocks = (msglen /. size 16) *. size 16 in
  let final_len = msglen %. size 16 in
  let padded_len = fullblocks +. size 16 in
  let msg_padded = create padded_len (u8 0) in
  update_sub #MUT #uint8 #padded_len msg_padded (size 0) msglen msg;
  let last_block = sub msg_padded fullblocks (size 16) in
  padPKCS last_block (size 16 -. final_len) final_len;
  let correct_out = sub #MUT #uint8 #(msglen +. size 16) out (size 0) padded_len in
  Hacl.Impl.AES_256.Bitsliced.encrypt_blocks_cbc
    correct_out
    key
    iv
    msg_padded
    padded_len;
  pop_frame ();
  padded_len

val aes256_cbc_decrypt:
  out:buffer uint8 ->
  key:lbuffer uint8 keylen ->
  iv:block ->
  cip:buffer uint8{length cip == length out} ->
  ciplen:size_t{v ciplen = length cip /\ (v ciplen / 16) * 16 + 16 <= max_size_t /\ v ciplen > 0 /\ v ciplen % 16 = 0} ->
  Stack size_t
    (requires (fun h -> live h out /\ live h key /\ live h iv /\ live h cip /\
      disjoint out key /\ disjoint out iv /\ disjoint out cip
    ))
    (ensures (fun h0 _ h1 -> modifies1 out h0 h1))


let aes256_cbc_decrypt out key iv cip ciplen =
  push_frame();
   Hacl.Impl.AES_256.Bitsliced.decrypt_blocks_cbc
    out
    key
    iv
    cip
    ciplen;
  let pad = index #MUT #uint8 #ciplen out (ciplen -. size 1) in
  let pad32 = Lib.RawIntTypes.size_from_UInt32
    (FStar.Int.Cast.uint8_to_uint32
      (Lib.RawIntTypes.u8_to_UInt8 pad))
  in
  let msglen = ciplen -. pad32 in
  pop_frame();
  msglen
