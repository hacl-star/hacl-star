module Lib.ByteBuffer.Tuples

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.ByteSequence.Tuples


let size_t_tuple = len:size_t{2 <= v len /\ v len <= 14}


inline_for_extraction
val expand: #a:Type0 -> #len:size_nat_tuple -> b:lbuffer a (size len) ->
  Stack (ltuple a len)
  (requires (fun h -> live h b))
  (ensures  (fun h0 r h1 -> r == Lib.ByteSequence.Tuples.expand (as_seq h0 b)))

inline_for_extraction
val collapse: #a:Type0 -> #len:size_nat_tuple -> b:lbuffer a (size len) -> zero:a -> lt:ltuple a len ->
  Stack unit
  (requires (fun h -> 0 < len /\ live h b))
  (ensures  (fun h0 _ h1 ->
    modifies1 b h0 h1 /\ as_seq h1 b == Lib.ByteSequence.Tuples.collapse zero lt))
