module Hacl.Hash

open FStar.Buffer
open FStar.HyperStack.ST
open Hacl.Cast
open Hacl.Constants


(* Module abbreviations *)
module HS  = FStar.HyperStack
module B   = FStar.Buffer
module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val crypto_hash:
  output:uint8_p{length output = crypto_hash_BYTES} ->
  input:uint8_p{disjoint output input} ->
  inlen:u32{U32.v inlen = length input} ->
  Stack u32
    (requires (fun h -> live h output /\ live h input))
    (ensures  (fun h0 _ h1 -> modifies_1 output h0 h1))

let crypto_hash output input inlen =
  SHA2_512.hash output input inlen;
  0ul
