module Libsodium

open FStar.Buffer
open FStar.UInt8
open Hacl.Constants

(* For test purpose only (no specification associated) *)

val crypto_box_beforenm:
  k:uint8_p ->
  pk:uint8_p ->
  sk:uint8_p ->
  Stack u32
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))

val crypto_box_detached:
  c:uint8_p ->
  mac:uint8_p ->
  m:uint8_p ->
  mlen:u64 ->
  n:uint8_p ->
  pk:uint8_p ->
  sk:uint8_p ->
  Stack u32
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))

val crypto_box_open_detached:
  m:uint8_p ->
  c:uint8_p ->
  mac:uint8_p ->
  mlen:u64 ->
  n:uint8_p ->
  pk:uint8_p ->
  sk:uint8_p ->
  Stack u32
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))

val crypto_box_easy:
  c:uint8_p ->
  m:uint8_p ->
  mlen:u64 ->
  n:uint8_p ->
  pk:uint8_p ->
  sk:uint8_p ->
  Stack u32
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))

val crypto_box_open_easy:
  m:uint8_p ->
  c:uint8_p ->
  mlen:u64 ->
  n:uint8_p ->
  pk:uint8_p ->
  sk:uint8_p ->
  Stack u32
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))

val crypto_box_keypair:
  pk:uint8_p ->
  sk:uint8_p ->
  Stack unit
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))

val crypto_box_easy_afternm:
  c:uint8_p ->
  m:uint8_p ->
  mlen:u64 ->
  n:uint8_p ->
  k:uint8_p ->
  Stack unit
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))

val randombytes_buf:
  b:uint8_p ->
  blen:u64 ->
  Stack unit
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))
