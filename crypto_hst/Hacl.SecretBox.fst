module Hacl.SecretBox

open FStar.Buffer
open FStar.HST
open Hacl.Constants
open Hacl.Policies

(* Module abbreviations *)
module HS  = FStar.HyperStack
module B   = FStar.Buffer
module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

(* TODO:
   disjointness clauses
*)


val crypto_secretbox_detached:
  c:uint8_p ->
  mac:uint8_p{length mac = crypto_secretbox_MACBYTES} ->
  m:uint8_p ->
  mlen:u64{let len = U64.v mlen in len = length m /\ len = length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h mac /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_2 c mac h0 h1 /\ live h1 c /\ live h1 mac))
let crypto_secretbox_detached c mac m mlen n k =
  let mlen = Int.Cast.uint64_to_uint32 mlen in
  Hacl.Symmetric.Chacha20.chacha20_encrypt c k (Hacl.Cast.uint32_to_sint32 1ul) n m mlen;
  Hacl.Symmetric.Poly1305.poly1305_mac mac c mlen k;
  0ul


val crypto_secretbox_open_detached:
  m:uint8_p ->
  c:uint8_p ->
  mac:uint8_p{length mac = crypto_secretbox_MACBYTES /\ declassifiable mac} ->
  clen:u64{let len = U64.v clen in len = length m /\ len = length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h m /\ live h c /\ live h mac /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_1 m h0 h1 /\ live h1 m))
let crypto_secretbox_open_detached m c mac clen n k =
  push_frame();
  let clen = Int.Cast.uint64_to_uint32 clen in
  let tmp_mac = create (Hacl.Cast.uint8_to_sint8 0uy) 16ul in
  Hacl.Symmetric.Poly1305.poly1305_mac tmp_mac c clen k;
  assume (Hacl.Policies.declassifiable tmp_mac);
  let verify = cmp_bytes mac tmp_mac 16ul in
  if U8 (verify =^ 0uy) then (
    Hacl.Symmetric.Chacha20.chacha20_encrypt m k (Hacl.Cast.uint32_to_sint32 1ul) n c clen;
    pop_frame();
    0x0ul
  )
  else (
    pop_frame();
    0xfffffffful
  )


val crypto_secretbox_easy:
  c:uint8_p ->
  m:uint8_p ->
  mlen:u64{let len = U64.v mlen in len <= length m /\ len + crypto_secretbox_MACBYTES <= length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_1 c h0 h1 /\ live h1 c))
let crypto_secretbox_easy c m mlen n k =
  let mlen_ = FStar.Int.Cast.uint64_to_uint32 mlen in
  let c = sub c 0ul mlen_ in
  let mac = sub c mlen_ 16ul in
  crypto_secretbox_detached c mac m mlen n k


val crypto_secretbox_open_easy:
  m:uint8_p ->
  c:uint8_p ->
  clen:u64{let len = U64.v clen in len = length m + crypto_secretbox_MACBYTES /\ len = length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_1 m h0 h1 /\ live h1 m))
let crypto_secretbox_open_easy m c clen n k =
  let clen_ = FStar.Int.Cast.uint64_to_uint32 clen in
  let c = sub c 0ul clen_ in
  let mac = sub c clen_ 16ul in
  crypto_secretbox_open_detached m c mac clen n k
