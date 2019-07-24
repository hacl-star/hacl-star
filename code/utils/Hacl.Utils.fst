module Hacl.Utils

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

module B  = LowStar.Buffer
module LBS = Lib.ByteSequence



inline_for_extraction
val secure_compare:
    b1: buffer uint8
  -> b2: buffer uint8
  -> len: size_t{v len = length b1 /\ v len = length b2} ->
  Stack bool
    (requires fun h -> live h b1 /\ live h b2)
    (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == LBS.lbytes_eq #(v len) (B.as_seq #uint8 h0 b1) (B.as_seq #uint8 h0 b2))

let secure_compare b1 b2 len = Lib.ByteBuffer.lbytes_eq #len b1 b2
