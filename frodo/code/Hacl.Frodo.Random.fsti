module Hacl.Frodo.Random

open FStar.HyperStack.All

open LowStar.Buffer

open Lib.IntTypes
open Lib.PQ.Buffer

open Hacl.Impl.PQ.Lib

val randombytes_init_:
    entropy_input:lbytes (size 48)
  -> Stack unit
    (requires fun h -> live h entropy_input)
    (ensures  fun h0 _ h1 -> live h1 entropy_input)

val randombytes_:
    len:size_t
  -> res:lbytes len
  -> Stack unit
    (requires fun h -> live h res)
    (ensures  fun h0 _ h1 -> live h1 res /\ modifies (loc_buffer res) h0 h1)
