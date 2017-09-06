module NaCl

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Buffer
open FStar.HyperStack.ST
open Hacl.Constants
open Hacl.Policies
open Hacl.Cast

module HS  = FStar.HyperStack
module B   = FStar.Buffer
module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

let crypto_box_NONCEBYTES     = 24
let crypto_box_PUBLICKEYBYTES = 32
let crypto_box_SECRETKEYBYTES = 32
let crypto_box_MACBYTES       = 16

let crypto_secretbox_NONCEBYTES = 24
let crypto_secretbox_KEYBYTES   = 32
let crypto_secretbox_MACBYTES   = 16

val crypto_secretbox_detached:
  c:uint8_p ->
  mac:uint8_p{length mac = crypto_secretbox_MACBYTES /\ disjoint mac c} ->
  m:uint8_p ->
  mlen:u64{let len = U64.v mlen in len = length m /\ len = length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h mac /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_2 c mac h0 h1 /\ live h1 c /\ live h1 mac))

val crypto_secretbox_open_detached:
  m:uint8_p ->
  c:uint8_p ->
  mac:uint8_p{length mac = crypto_secretbox_MACBYTES} ->
  clen:u64{let len = U64.v clen in len = length m /\ len = length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h m /\ live h c /\ live h mac /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_1 m h0 h1 /\ live h1 m))

val crypto_secretbox_easy:
  c:uint8_p ->
  m:uint8_p ->
  mlen:u64{let len = U64.v mlen in len <= length m /\ len + crypto_secretbox_MACBYTES <= length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_1 c h0 h1 /\ live h1 c))

val crypto_secretbox_open_easy:
  m:uint8_p ->
  c:uint8_p ->
  clen:u64{let len = U64.v clen in len = length m + crypto_secretbox_MACBYTES /\ len = length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_1 m h0 h1 /\ live h1 m))

val crypto_box_beforenm:
  k:uint8_p{length k = crypto_box_PUBLICKEYBYTES} ->
  pk:uint8_p{length pk = crypto_box_PUBLICKEYBYTES /\ disjoint k pk} ->
  sk:uint8_p{length sk = crypto_box_SECRETKEYBYTES /\ disjoint k sk /\ disjoint pk sk} ->
  Stack u32
    (requires (fun h -> live h k /\ live h pk /\ live h sk))
    (ensures  (fun h0 _ h1 -> modifies_1 k h0 h1))

val crypto_box_detached_afternm:
  c:uint8_p ->
  mac:uint8_p{length mac = crypto_secretbox_MACBYTES /\ disjoint c mac} ->
  m:uint8_p ->
  mlen:u64{let len = U64.v mlen in len = length m /\ len = length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h mac /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_2 c mac h0 h1 /\ live h1 c /\ live h1 mac))

val crypto_box_detached:
  c:uint8_p ->
  mac:uint8_p{length mac = crypto_box_MACBYTES /\ disjoint c mac} ->
  m:uint8_p ->
  mlen:u64{let len = U64.v mlen in length c = len /\ len = length m}  ->
  n:uint8_p{length n = crypto_box_NONCEBYTES} ->
  pk:uint8_p{length pk = crypto_box_PUBLICKEYBYTES} ->
  sk:uint8_p{length sk = crypto_box_SECRETKEYBYTES /\ disjoint pk sk} ->
  Stack u32
    (requires (fun h -> live h c /\ live h mac /\ live h m /\ live h n /\ live h pk /\ live h sk))
    (ensures  (fun h0 z h1 -> modifies_2 c mac h0 h1 /\ live h1 c /\ live h1 mac))

val crypto_box_open_detached:
  m:uint8_p ->
  c:uint8_p ->
  mac:uint8_p{length mac = crypto_box_MACBYTES} ->
  mlen:u64{let len = U64.v mlen in length m = len /\ len = length c}  ->
  n:uint8_p{length n = crypto_box_NONCEBYTES} ->
  pk:uint8_p{length pk = crypto_box_PUBLICKEYBYTES} ->
  sk:uint8_p{length sk = crypto_box_SECRETKEYBYTES /\ disjoint sk pk} ->
  Stack u32
    (requires (fun h -> live h c /\ live h mac /\ live h m /\ live h n /\ live h pk /\ live h sk))
    (ensures  (fun h0 z h1 -> modifies_1 m h0 h1 /\ live h1 m))

val crypto_box_easy_afternm:
  c:uint8_p ->
  m:uint8_p ->
  mlen:u64{let len = U64.v mlen in len <= length m /\ len + crypto_secretbox_MACBYTES <= length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_1 c h0 h1 /\ live h1 c))

val crypto_box_easy:
  c:uint8_p ->
  m:uint8_p ->
  mlen:u64{let len = U64.v mlen in length c = len + crypto_box_MACBYTES /\ len = length m}  ->
  n:uint8_p{length n = crypto_box_NONCEBYTES} ->
  pk:uint8_p{length pk = crypto_box_PUBLICKEYBYTES} ->
  sk:uint8_p{length sk = crypto_box_SECRETKEYBYTES /\ disjoint sk pk} ->
  Stack u32
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h pk /\ live h sk))
    (ensures  (fun h0 z h1 -> modifies_1 c h0 h1 /\ live h1 c))

val crypto_box_open_easy:
  m:uint8_p ->
  c:uint8_p ->
  mlen:u64{let len = U64.v mlen in length m = len - crypto_box_MACBYTES /\ len = length c}  ->
  n:uint8_p{length n = crypto_box_NONCEBYTES} ->
  pk:uint8_p{length pk = crypto_box_PUBLICKEYBYTES} ->
  sk:uint8_p{length sk = crypto_box_SECRETKEYBYTES /\ disjoint sk pk} ->
  Stack u32
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h pk /\ live h sk))
    (ensures  (fun h0 z h1 -> modifies_1 m h0 h1 /\ live h1 m))

val crypto_box_open_detached_afternm:
  m:uint8_p ->
  c:uint8_p ->
  mac:uint8_p{length mac = crypto_secretbox_MACBYTES} ->
  mlen:u64{let len = U64.v mlen in len = length m /\ len = length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h mac /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_1 m h0 h1 /\ live h1 m))


val crypto_box_open_easy_afternm:
  m:uint8_p ->
  c:uint8_p ->
  mlen:u64{let len = U64.v mlen in len = length m + 16 /\ len = length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_1 m h0 h1 /\ live h1 c /\ live h1 k))
