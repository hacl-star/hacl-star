module Hacl.Impl.BignumQ.Mul

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

inline_for_extraction noextract
let qelemB = lbuffer uint64 5ul

val barrett_reduction:
    z:qelemB
  -> t:lbuffer uint64 10ul ->
  Stack unit
    (requires fun h -> live h z /\ live h t)
    (ensures  fun h0 _ h1 -> modifies (loc z) h0 h1)

val mul_modq:
    z:qelemB
  -> x:qelemB
  -> y:qelemB ->
  Stack unit
    (requires fun h -> live h z /\ live h x /\ live h y)
    (ensures  fun h0 _ h1 -> modifies (loc z) h0 h1)

val add_modq:
    z:qelemB
  -> x:qelemB
  -> y:qelemB ->
  Stack unit
    (requires fun h ->
      live h z /\ live h x /\ live h y)
    (ensures fun h0 _ h1 -> modifies (loc z) h0 h1)
