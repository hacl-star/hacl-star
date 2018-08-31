module Hacl.Frodo.Random

open FStar.HyperStack.All

open LowStar.Buffer

open Lib.IntTypes
open Lib.PQ.Buffer

val randombytes_init_:
    entropy_input:lbuffer uint8 48
  -> Stack unit
    (requires fun h -> live h entropy_input)
    (ensures  fun h0 _ h1 -> live h1 entropy_input)

val randombytes_:
    len:size_t
  -> res:lbuffer uint8 (v len)
  -> Stack unit
    (requires fun h -> live h res)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer res) h0 h1 /\
      as_seq h1 res == Spec.Frodo.Random.randombytes_ (v len))
