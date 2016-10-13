module Hacl.Policies

open FStar.HST
open FStar.Buffer

open Hacl.Types

(* Module abbreviations *)
module HS  = FStar.HyperStack
module B   = FStar.Buffer
module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module H8  = Hacl.UInt8

assume new type declassifiable (b:uint8_p)

assume val leak_byte:
  b:uint8_p ->
  n:u32{U32.v n < length b} ->
  Stack u8
    (requires (fun h -> declassifiable b /\ live h b))
    (ensures  (fun h0 z h1 -> live h0 b /\ h0 == h1 /\ U8.v z = H8.v (get h0 b (U32.v n))))


val cmp_bytes_:
  b:uint8_p{declassifiable b} ->
  b':uint8_p{declassifiable b'} ->
  len:u32{U32.v len <= length b /\ U32.v len <= length b'} ->
  tmp:u8 ->
  Stack u8
    (requires (fun h -> live h b /\ live h b'))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ (U8.v z = 0 ==> as_seq h0 b == as_seq h0 b')))
let rec cmp_bytes_ b b' len tmp =
  if U32(len =^ 0ul) then U8.lognot tmp
  else (
    let i = U32 (len -^ 1ul) in
    let bi = leak_byte b i in
    let bi' = leak_byte b' i in
    let tmp = U8 (eq_mask bi bi' &^ tmp) in
    cmp_bytes_ b b' i tmp
  )

val cmp_bytes:
  b:uint8_p{declassifiable b} ->
  b':uint8_p{declassifiable b'} ->
  len:u32{U32.v len <= length b /\ U32.v len <= length b'} ->
  Stack u8
    (requires (fun h -> live h b /\ live h b'))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ (U8.v z = 0 ==> as_seq h0 b == as_seq h0 b')))
let cmp_bytes b b' len =
  cmp_bytes_ b b' len 255uy

