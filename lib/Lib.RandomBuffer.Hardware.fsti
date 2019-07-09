module Lib.RandomBuffer.Hardware

open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.IntVector.Random


(* Get a N random bytes (public or secret) from the CPU *)
val random_bytes:
    #s: secrecy_level
  -> n: size_t
  -> rand: lbuffer (uint_t U8 s) n ->
  Stack unit (requires (fun h -> live h rand))
             (ensures  (fun h0 _ h1 -> live h1 rand /\ modifies1 rand h0 h1))


val random_uint32: unit ->
  Stack uint32 (requires (fun h -> True))
               (ensures  (fun h0 _ h1 -> True))


val random_uint64: unit ->
  Stack uint64 (requires (fun h -> True))
               (ensures  (fun h0 _ h1 -> True))


val random_pub_uint32: unit ->
  Stack pub_uint32 (requires (fun h -> True))
                   (ensures  (fun h0 _ h1 -> True))


val random_pub_uint64: unit ->
  Stack pub_uint64 (requires (fun h -> True))
                   (ensures  (fun h0 _ h1 -> True))


val randseed_pub_uint32: unit ->
  Stack pub_uint32 (requires (fun h -> True))
                   (ensures  (fun h0 _ h1 -> True))


val randseed_pub_uint64: unit ->
  Stack pub_uint64 (requires (fun h -> True))
                   (ensures  (fun h0 _ h1 -> True))
