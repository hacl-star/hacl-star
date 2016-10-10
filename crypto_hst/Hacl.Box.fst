module Hacl.Box

open FStar.Buffer
open FStar.HST

open Hacl.Constants
open Hacl.SecretBox

(* Module abbreviations *)
module HS  = FStar.HyperStack
module B   = FStar.Buffer
module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64



val crypto_box_easy:
  c:uint8_p ->
  m:uint8_p ->
  mlen:u64{let len = U64.v mlen in length c = len + crypto_box_MACBYTES /\ len = length m}  ->
  n:uint8_p{length n = crypto_box_NONCEBYTES} ->
  pk:uint8_p{length pk = crypto_box_PUBLICKEYBYTES} ->
  sk:uint8_p{length sk = crypto_box_SECRETKEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h pk /\ live h sk))
    (ensures  (fun h0 z h1 -> modifies_1 c h0 h1 /\ live h1 c))
let crypto_box_easy c m mlen n pk sk =
  push_frame();
  let key = create (Hacl.Cast.uint8_to_sint8 0uy) 32ul in
  (* Compute shared key *)
  Hacl.EC.Curve25519.exp key pk sk;
  let z = crypto_secretbox_easy c m mlen n key in
  pop_frame();
  z


val crypto_box_open_easy:
  m:uint8_p ->
  c:uint8_p ->
  mlen:u64{let len = U64.v mlen in length m = len - crypto_box_MACBYTES /\ len = length c}  ->
  n:uint8_p{length n = crypto_box_NONCEBYTES} ->
  pk:uint8_p{length pk = crypto_box_PUBLICKEYBYTES} ->
  sk:uint8_p{length sk = crypto_box_SECRETKEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h pk /\ live h sk))
    (ensures  (fun h0 z h1 -> modifies_1 c h0 h1 /\ live h1 c))
let crypto_box_open_easy m c mlen n pk sk =
  push_frame();
  let key = create (Hacl.Cast.uint8_to_sint8 0uy) 32ul in
  (* Compute shared key *)
  Hacl.EC.Curve25519.exp key pk sk;
  let z = crypto_secretbox_open_easy m c mlen n key in
  pop_frame();
  z


val crypto_box_detached:
  c:uint8_p ->
  mac:uint8_p{length mac = crypto_box_MACBYTES} ->
  m:uint8_p ->
  mlen:u64{let len = U64.v mlen in length c = len /\ len = length m}  ->
  n:uint8_p{length n = crypto_box_NONCEBYTES} ->
  pk:uint8_p{length pk = crypto_box_PUBLICKEYBYTES} ->
  sk:uint8_p{length sk = crypto_box_SECRETKEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h pk /\ live h sk))
    (ensures  (fun h0 z h1 -> modifies_1 c h0 h1 /\ live h1 c))
let crypto_box_detached c mac m mlen n pk sk =
  push_frame();
  let key = create (Hacl.Cast.uint8_to_sint8 0uy) 32ul in
  (* Compute shared key *)
  Hacl.EC.Curve25519.exp key pk sk;
  let z = crypto_secretbox_detached c mac m mlen n key in
  pop_frame();
  z


val crypto_box_open_detached:
  m:uint8_p ->
  c:uint8_p ->
  mac:uint8_p{length mac = crypto_box_MACBYTES} ->
  mlen:u64{let len = U64.v mlen in length m = len /\ len = length c}  ->
  n:uint8_p{length n = crypto_box_NONCEBYTES} ->
  pk:uint8_p{length pk = crypto_box_PUBLICKEYBYTES} ->
  sk:uint8_p{length sk = crypto_box_SECRETKEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h pk /\ live h sk))
    (ensures  (fun h0 z h1 -> modifies_1 c h0 h1 /\ live h1 c))
let crypto_box_open_detached m c mac mlen n pk sk =
  push_frame();
  let key = create (Hacl.Cast.uint8_to_sint8 0uy) 32ul in
  (* Compute shared key *)
  Hacl.EC.Curve25519.exp key pk sk;
  let z = crypto_secretbox_open_detached m c mac mlen n key in
  pop_frame();
  z
