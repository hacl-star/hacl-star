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

(*

let aes256_cbc_encrypt out key iv msg msglen =
  push_frame();
  assert (16 <> 0);
  let fullblocks = (msglen /. size 16) *. size 16 in
  let final = msglen %. size 16 in
  let msg1 = sub #MUT #uint8 #msglen msg (size 0) fullblocks in
  let last = sub #MUT #uint8 #msglen msg fullblocks final in
  let out1 = sub #MUT #uint8 #(msglen +. size 16) out (size 0) fullblocks in
  let out2 = sub #MUT #uint8 #(msglen +. size 16) out fullblocks (size 16) in
  assert(disjoint out1 out2);
  let scratch = create (xkeylen +. size 48) (u8 0) in
  let kex = sub scratch (size 0) xkeylen in
  let tmp = sub scratch xkeylen (size 16) in
  let otmp = sub scratch (xkeylen +. size 16) (size 16) in
  let ltmp = sub scratch (xkeylen +. size 32) (size 16) in
  keyExpansion key kex;
  cbc_encrypt_blocks out1 kex iv msg1 fullblocks (size 0) tmp;
  let lastfull = if (fullblocks <>. size 0) then sub out1 (fullblocks -. size 16) (size 16)
                 else iv in
  update_sub ltmp (size 0) final (sub last (size 0) final);//blit last 0ul ltmp 0ul final;
  padPKCS ltmp (size 16 -. final) final;
  xor_block ltmp ltmp lastfull (size 0);
  cipher otmp ltmp kex;
  copy out2 otmp;//blit otmp 0ul out2 0ul 16ul;
  pop_frame()
*)

(*
val cbc_decrypt_blocks:
  out:buffer uint8 ->
  kex:xkey ->
  prev:block ->
  cip:buffer uint8{length cip == length out} ->
  len:size_t{v len = length cip /\ v len % 16 = 0} ->
  curr:size_t{v curr <= v len /\ v curr % 16 = 0} ->
  tmp:block ->
  Stack unit
    (requires (fun h -> live h out /\ live h kex /\ live h prev /\ live h cip /\ live h tmp /\
      disjoint out kex /\ disjoint out prev /\ disjoint out cip /\ disjoint out tmp /\
      disjoint tmp kex /\ disjoint tmp prev /\ disjoint tmp cip
    ))
    (ensures (fun h0 _ h1 -> modifies2 tmp out h0 h1))
    (decreases (v len - v curr))

let rec cbc_decrypt_blocks out kex prev cip len curr tmp =
  if curr = len then ()
  else (
    assert(v curr < v len /\ v curr % 16 = 0);
    let cblock = sub #MUT #uint8 #len cip curr (size 16) in
    let oblock = sub #MUT #uint8 #len out curr (size 16) in
    inv_cipher tmp cblock kex;
    xor_block oblock tmp prev (size 0);
    cbc_decrypt_blocks out kex cblock cip len (curr +. size 16) tmp
  )


val unpadPKCS:
  tmp:block ->
  idx:size_t{v idx <= v blocklen} ->
  Stack (len:size_t{v len <= v blocklen})
	 (requires (fun h -> live h tmp))
	 (ensures (fun h0 _ h1 -> modifies1 tmp h0 h1))
let rec unpadPKCS tmp idx =
  let pad = tmp.(blocklen -. size 1) in
  (* Reading the padding is inherently non constant *)
  let pad32 = Lib.RawIntTypes.size_from_UInt32
    (FStar.Int.Cast.uint8_to_uint32
      (Lib.RawIntTypes.u8_to_UInt8 pad))
   in
  if pad32 <=. blocklen then pad32
  else size 0

val unpadISO:
  tmp:block ->
  idx:size_t{v idx < v blocklen} ->
  Stack (len:size_t{v len < v blocklen})
	 (requires (fun h -> live h tmp))
	 (ensures (fun h0 _ h1 -> modifies1 tmp h0 h1))
let rec unpadISO tmp idx =
   let t = tmp.(idx) in
   (* Reading the padding is inherently non constant *)
   if
     Lib.RawIntTypes.u8_to_UInt8 t =
       Lib.RawIntTypes.u8_to_UInt8 (u8 0x80)
   then idx
   else if Lib.RawIntTypes.u8_to_UInt8 t <>
      Lib.RawIntTypes.u8_to_UInt8 (u8 0x00)
   then 0ul
   else if idx = 0x0ul then 0ul
   else unpadISO tmp (idx -. size 1)

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
  let kex = create xkeylen (u8 0) in
  let tmp = create (size 16) (u8 0) in
  keyExpansion key kex;
  cbc_decrypt_blocks out kex iv cip ciplen 0ul tmp;
  let pad = index #MUT #uint8 #ciplen out (ciplen -. size 1) in
  let pad32 = Lib.RawIntTypes.size_from_UInt32
    (FStar.Int.Cast.uint8_to_uint32
      (Lib.RawIntTypes.u8_to_UInt8 pad))
  in
  let msglen = ciplen -. pad32 in
  pop_frame();
  msglen

val aes256_cbc_decrypt_no_pad:
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

let aes256_cbc_decrypt_no_pad out key iv cip ciplen =
  push_frame();
  let kex = create xkeylen (u8 0) in
  let tmp = create (size 16) (u8 0) in
  keyExpansion key kex;
  cbc_decrypt_blocks out kex iv cip ciplen (size 0) tmp;
  pop_frame();
  ciplen
*)
