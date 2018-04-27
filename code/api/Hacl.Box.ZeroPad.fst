module Hacl.Box.ZeroPad

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Buffer
open FStar.HyperStack.ST
open Hacl.Cast

open Hacl.Constants
open Hacl.SecretBox.ZeroPad


(* Module abbreviations *)
module HS  = FStar.HyperStack
module B   = FStar.Buffer
module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val crypto_box_beforenm:
  k:uint8_p{length k = crypto_box_PUBLICKEYBYTES} ->
  pk:uint8_p{length pk = crypto_box_PUBLICKEYBYTES /\ disjoint k pk} ->
  sk:uint8_p{length sk = crypto_box_SECRETKEYBYTES /\ disjoint k sk /\ disjoint pk sk} ->
  Stack u32
    (requires (fun h -> live h k /\ live h pk /\ live h sk))
    (ensures  (fun h0 _ h1 -> modifies_1 k h0 h1))
let crypto_box_beforenm k pk sk =
  push_frame();
  let h0 = ST.get() in
  let tmp = create (Hacl.Cast.uint8_to_sint8 0uy) 48ul in
  let hsalsa_k = sub tmp 0ul 32ul in
  let hsalsa_n = sub tmp 32ul 16ul in
  (* Compute shared key *)
  Hacl.Curve25519.crypto_scalarmult hsalsa_k sk pk;
  Hacl.Salsa20.hsalsa20 k hsalsa_k hsalsa_n;
  pop_frame();
  0ul


#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

val crypto_box_detached_afternm:
  c:uint8_p ->
  mac:uint8_p{length mac = crypto_secretbox_MACBYTES /\ disjoint c mac} ->
  m:uint8_p{disjoint m c} ->
  mlen:u64{let len = U64.v mlen in len + 32 = length m /\ len + 32 = length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h mac /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_2 c mac h0 h1 /\ live h1 c /\ live h1 mac))
let crypto_box_detached_afternm c mac m mlen n k =
  crypto_secretbox_detached c mac m mlen n k


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

let lemma_modifies_3_2 (c:uint8_p) (mac:uint8_p) h0 h1 h2 : Lemma
  (requires (live h0 c /\ live h0 mac /\ live h1 mac /\ live h1 c /\ live h2 c /\ live h2 mac
    /\ modifies_0 h0 h1 /\ modifies_2 c mac h1 h2))
  (ensures  (modifies_3_2 c mac h0 h2))
  = lemma_reveal_modifies_0 h0 h1; lemma_reveal_modifies_2 c mac h1 h2; lemma_intro_modifies_3_2 c mac h0 h2


#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 200"

val crypto_box_detached:
  c:uint8_p ->
  mac:uint8_p{length mac = crypto_box_MACBYTES /\ disjoint c mac} ->
  m:uint8_p{disjoint m c} ->
  mlen:u64{let len = U64.v mlen in length c = len + 32 /\ len + 32 = length m}  ->
  n:uint8_p{length n = crypto_box_NONCEBYTES} ->
  pk:uint8_p{length pk = crypto_box_PUBLICKEYBYTES} ->
  sk:uint8_p{length sk = crypto_box_SECRETKEYBYTES /\ disjoint pk sk} ->
  Stack u32
    (requires (fun h -> live h c /\ live h mac /\ live h m /\ live h n /\ live h pk /\ live h sk))
    (ensures  (fun h0 z h1 -> modifies_2 c mac h0 h1 /\ live h1 c /\ live h1 mac))
let crypto_box_detached c mac m mlen n pk sk =
  push_frame();
  let h0 = ST.get() in
  let key = create (Hacl.Cast.uint8_to_sint8 0uy) 80ul in
  let h0' = ST.get() in
  let k = sub key 0ul 32ul in
  let subkey = sub key 32ul 32ul in
  let hsalsa_n = sub key 64ul 16ul in
  (* Compute shared key *)
  Hacl.Curve25519.crypto_scalarmult k sk pk;
  let h1 = ST.get() in
  cut (modifies_0 h0 h1);
  Hacl.Salsa20.hsalsa20 subkey k hsalsa_n;
  let h2 = ST.get() in
  cut (modifies_0 h0 h2);
  let z = crypto_secretbox_detached c mac m mlen n subkey in
  let h3 = ST.get() in
  cut (modifies_2 c mac h2 h3);
  lemma_modifies_3_2 c mac h0 h2 h3;
  pop_frame();
  z


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val crypto_box_open_detached:
  m:uint8_p ->
  c:uint8_p{disjoint m c} ->
  mac:uint8_p{length mac = crypto_box_MACBYTES} ->
  mlen:u64{let len = U64.v mlen in len + 32 = length m /\ len + 32 = length c}  ->
  n:uint8_p{length n = crypto_box_NONCEBYTES} ->
  pk:uint8_p{length pk = crypto_box_PUBLICKEYBYTES} ->
  sk:uint8_p{length sk = crypto_box_SECRETKEYBYTES /\ disjoint sk pk} ->
  Stack u32
    (requires (fun h -> live h c /\ live h mac /\ live h m /\ live h n /\ live h pk /\ live h sk))
    (ensures  (fun h0 z h1 -> modifies_1 m h0 h1 /\ live h1 m))
let crypto_box_open_detached m c mac mlen n pk sk =
  push_frame();
  let key = create (Hacl.Cast.uint8_to_sint8 0uy) 80ul in
  let k = sub key 0ul 32ul in
  let subkey = sub key 32ul 32ul in
  let hsalsa_n = sub key 64ul 16ul in
  (* Compute shared key *)
  Hacl.Curve25519.crypto_scalarmult k sk pk;
  Hacl.Salsa20.hsalsa20 subkey k hsalsa_n;
  let z = crypto_secretbox_open_detached m c mac mlen n subkey in
  pop_frame();
  z


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 40"

val crypto_box_easy_afternm:
  c:uint8_p ->
  m:uint8_p{disjoint m c} ->
  mlen:u64{let len = U64.v mlen in len + 32 = length m /\ len + 32 = length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_1 c h0 h1 /\ live h1 c))
let crypto_box_easy_afternm c m mlen n k =
  let mlen' = Int.Cast.uint64_to_uint32 mlen in
  push_frame();
  let cmac = Buffer.create (uint8_to_sint8 0uy) 16ul in
  Math.Lemmas.modulo_lemma (U64.v mlen) (pow2 32);
  let z = crypto_box_detached_afternm c cmac m mlen n k in
  blit cmac 0ul c 16ul 16ul;
  pop_frame();
  z


val crypto_box_easy:
  c:uint8_p ->
  m:uint8_p{disjoint c m} ->
  mlen:u64{let len = U64.v mlen in len + 32 = length c /\ len + 32 = length m}  ->
  n:uint8_p{length n = crypto_box_NONCEBYTES} ->
  pk:uint8_p{length pk = crypto_box_PUBLICKEYBYTES} ->
  sk:uint8_p{length sk = crypto_box_SECRETKEYBYTES /\ disjoint sk pk} ->
  Stack u32
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h pk /\ live h sk))
    (ensures  (fun h0 z h1 -> modifies_1 c h0 h1 /\ live h1 c))
let crypto_box_easy c m mlen n pk sk =
  push_frame ();
  let mlen' = Int.Cast.uint64_to_uint32 mlen in
  Math.Lemmas.modulo_lemma (U64.v mlen) (pow2 32);
  let cmac   = create (uint8_to_sint8 0uy) 16ul in
  let res = crypto_box_detached c cmac m mlen n pk sk in
  blit cmac 0ul c 16ul 16ul;
  pop_frame();
  res



val crypto_box_open_easy:
  m:uint8_p ->
  c:uint8_p{disjoint c m} ->
  mlen:u64{let len = U64.v mlen in length m = len + 32 /\ len + 32 = length c}  ->
  n:uint8_p{length n = crypto_box_NONCEBYTES} ->
  pk:uint8_p{length pk = crypto_box_PUBLICKEYBYTES} ->
  sk:uint8_p{length sk = crypto_box_SECRETKEYBYTES /\ disjoint sk pk} ->
  Stack u32
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h pk /\ live h sk))
    (ensures  (fun h0 z h1 -> modifies_1 m h0 h1 /\ live h1 m))
let crypto_box_open_easy m c mlen n pk sk =
  let mlen' = Int.Cast.uint64_to_uint32 mlen in
  Math.Lemmas.modulo_lemma (U64.v mlen) (pow2 32);
  let mac = sub c 16ul 16ul in
  crypto_box_open_detached m c mac mlen n pk sk


val crypto_box_open_detached_afternm:
  m:uint8_p ->
  c:uint8_p{disjoint m c} ->
  mac:uint8_p{length mac = crypto_secretbox_MACBYTES} ->
  mlen:u64{let len = U64.v mlen in len + 32 = length m /\ len + 32 = length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h mac /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_1 m h0 h1 /\ live h1 m))
let crypto_box_open_detached_afternm m c mac mlen n k =
  crypto_secretbox_open_detached m c mac mlen n k


val crypto_box_open_easy_afternm:
  m:uint8_p ->
  c:uint8_p{disjoint c m} ->
  mlen:u64{let len = U64.v mlen in len + 32 = length m /\ len + 32 = length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_1 m h0 h1 /\ live h1 c /\ live h1 k))
let crypto_box_open_easy_afternm m c mlen n k =
  let mlen' = Int.Cast.uint64_to_uint32 mlen in
  Math.Lemmas.modulo_lemma (U64.v mlen) (pow2 32);
  let mac = sub c 16ul 16ul in
  let h0 = ST.get () in
  let t = crypto_box_open_detached_afternm m c mac mlen n k in
  let h1 = ST.get () in
  lemma_reveal_modifies_1 m h0 h1;
  t
