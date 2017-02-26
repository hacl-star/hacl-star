module Hacl.AEAD.Chacha20Poly1305

open FStar.Buffer
open FStar.ST
open Hacl.Constants
open Hacl.Policies
open Hacl.Cast
open Hacl.Endianness

(* Module abbreviations *)

module HS  = FStar.HyperStack
module B   = FStar.Buffer
module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32
module H64 = Hacl.UInt64

(* The following values should point to Spec.Chacha20Poly1305 *)
let noncelen = 12
let keylen = 32
let maclen = 16

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50"

val aead_encrypt:
  c:uint8_p ->
  mac:uint8_p{length mac = maclen /\ disjoint mac c} ->
  m:uint8_p ->
  mlen:u32{let len = U32.v mlen in len = length m /\ len = length c}  ->
  aad:uint8_p ->
  aadlen:u32{let len = U32.v aadlen in len = length aad}  ->
  k:uint8_p{length k = keylen} ->
  n:uint8_p{length n = noncelen} ->
  Stack u32
    (requires (fun h -> live h c /\ live h mac /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_2 c mac h0 h1 /\ live h1 c /\ live h1 mac))
let aead_encrypt c mac m mlen aad aadlen k n =
  push_frame();
  Chacha20.chacha20 c m mlen k n 1ul;
  let b = create (uint8_to_sint8 0uy) 64ul in
  Chacha20.chacha20_key_block b k n 0ul;
  let mk = Buffer.sub b 0ul 32ul in
  let key_s = Buffer.sub mk 16ul 16ul in

  let st = Poly1305_64.alloc () in
  let lb = create (uint8_to_sint8 0uy) 16ul in
  Poly1305_64.poly1305_blocks_init st aad aadlen mk;
  Poly1305_64.poly1305_blocks_continue st c mlen;
  hstore64_le (Buffer.sub lb 0ul 8ul) (uint32_to_sint64 aadlen);
  hstore64_le (Buffer.sub lb 8ul 8ul) (uint32_to_sint64 mlen);
  Poly1305_64.poly1305_blocks_finish st lb mac key_s;
  pop_frame();
  0ul


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 200"

val aead_decrypt:
  m:uint8_p ->
  c:uint8_p ->
  mlen:u32{let len = U32.v mlen in len = length m /\ len = length c}  ->
  mac:uint8_p{length mac = maclen /\ disjoint mac c} ->
  aad:uint8_p ->
  aadlen:u32{let len = U32.v aadlen in len = length aad}  ->
  k:uint8_p{length k = keylen} ->
  n:uint8_p{length n = noncelen} ->
  Stack u32
    (requires (fun h -> live h c /\ live h mac /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_2 c mac h0 h1 /\ live h1 c /\ live h1 mac))
let aead_decrypt m c mlen mac aad aadlen k n =
  push_frame();
  let b = create (uint8_to_sint8 0uy) 64ul in
  Chacha20.chacha20_key_block b k n 0ul;
  let mk = Buffer.sub b 0ul 32ul in
  let key_s = Buffer.sub mk 16ul 16ul in

  let rmac = create (uint8_to_sint8 0uy) 16ul in
  let st = Poly1305_64.alloc () in
  let lb = create (uint8_to_sint8 0uy) 16ul in
  Poly1305_64.poly1305_blocks_init st aad aadlen mk;
  Poly1305_64.poly1305_blocks_continue st c mlen;
  hstore64_le (Buffer.sub lb 0ul 8ul) (uint32_to_sint64 aadlen);
  hstore64_le (Buffer.sub lb 8ul 8ul) (uint32_to_sint64 mlen);
  Poly1305_64.poly1305_blocks_finish st lb rmac key_s;
  let verify = cmp_bytes mac rmac 16ul in
  let res = 
    if U8.(verify =^ 0uy) then (
      	 Chacha20.chacha20 m c mlen k n 1ul;
	 0ul
  	 ) else 1ul in
  pop_frame();
  res

