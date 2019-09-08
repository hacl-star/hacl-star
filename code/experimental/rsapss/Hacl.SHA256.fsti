module Hacl.SHA256

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

(* SHA 256 *)
inline_for_extraction
let hLen = 32ul

val hash:
    mHash:lbuffer uint8 hLen
  -> len:size_t
  -> m:lbuffer uint8 len
  -> Stack unit
    (requires fun h -> live h mHash /\ live h m /\ disjoint m mHash)
    (ensures  fun h0 _ h1 -> modifies (loc mHash) h0 h1)
