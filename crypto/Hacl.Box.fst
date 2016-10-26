module Hacl.Box

open FStar.Buffer
open FStar.ST

open Hacl.Constants
open Hacl.SecretBox


(* Module abbreviations *)
module HS  = FStar.HyperStack
module B   = FStar.Buffer
module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64


val crypto_box_beforenm:
  k:uint8_p{length k = crypto_box_PUBLICKEYBYTES} ->
  pk:uint8_p{length pk = crypto_box_PUBLICKEYBYTES /\ disjoint k pk} ->
  sk:uint8_p{length sk = crypto_box_SECRETKEYBYTES /\ disjoint k sk} ->
  Stack u32
    (requires (fun h -> live h k /\ live h pk /\ live h sk))
    (ensures  (fun h0 _ h1 -> modifies_1 k h0 h1))
let crypto_box_beforenm k pk sk =
  push_frame();
  let tmp = create (Hacl.Cast.uint8_to_sint8 0uy) 48ul in
  let hsalsa_k = sub tmp 0ul 32ul in
  let hsalsa_n = sub tmp 32ul 16ul in
  (* Compute shared key *)
  Hacl.EC.Curve25519.exp hsalsa_k pk sk;
  Hacl.Symmetric.HSalsa20.crypto_core_hsalsa20 k hsalsa_n hsalsa_k;
  pop_frame();
  0ul


val crypto_box_detached_afternm:
  c:uint8_p ->
  mac:uint8_p{length mac = crypto_secretbox_MACBYTES} ->
  m:uint8_p ->
  mlen:u64{let len = U64.v mlen in len = length m /\ len = length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h mac /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_2 c mac h0 h1 /\ live h1 c /\ live h1 mac))
let crypto_box_detached_afternm c mac m mlen n k =
  crypto_secretbox_detached c mac m mlen n k


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
  let key = create (Hacl.Cast.uint8_to_sint8 0uy) 80ul in
  let k = sub key 0ul 32ul in
  let subkey = sub key 32ul 32ul in
  let hsalsa_n = sub key 64ul 16ul in
  (* Compute shared key *)
  Hacl.EC.Curve25519.exp k pk sk;
  Hacl.Symmetric.HSalsa20.crypto_core_hsalsa20 subkey hsalsa_n k;
  let z = crypto_secretbox_detached c mac m mlen n subkey in
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
  let key = create (Hacl.Cast.uint8_to_sint8 0uy) 80ul in
  let k = sub key 0ul 32ul in
  let subkey = sub key 32ul 32ul in
  let hsalsa_n = sub key 64ul 16ul in
  (* Compute shared key *)
  Hacl.EC.Curve25519.exp k pk sk;
  Hacl.Symmetric.HSalsa20.crypto_core_hsalsa20 subkey hsalsa_n k;
  let z = crypto_secretbox_open_detached m c mac mlen n subkey in
  pop_frame();
  z


val crypto_box_easy_afternm:
  c:uint8_p ->
  m:uint8_p ->
  mlen:u64{let len = U64.v mlen in len <= length m /\ len + crypto_secretbox_MACBYTES <= length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_1 c h0 h1 /\ live h1 c))
let crypto_box_easy_afternm c m mlen n k =
  crypto_box_detached_afternm (offset c 16ul) (sub c 0ul 16ul) m mlen n k


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
  crypto_box_detached (offset c 16ul) c m mlen n pk sk


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
  crypto_box_open_detached m (offset c 16ul) c (U64 (mlen -^ 16uL)) n pk sk
