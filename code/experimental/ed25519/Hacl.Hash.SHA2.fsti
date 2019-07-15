module Hacl.Hash.SHA2

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

val hash_512:
    m:buffer uint8
  -> len:size_t{v len == length m}
  -> mHash:lbuffer uint8 64ul ->
  Stack unit
  (requires fun h -> live h mHash /\ live h m /\ disjoint m mHash)
  (ensures  fun h0 _ h1 -> modifies (loc mHash) h0 h1)
