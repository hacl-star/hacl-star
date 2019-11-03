module Hacl.Frodo.Random

open FStar.HyperStack.All

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer

module S = Spec.Frodo.Random

val state: b:lbuffer uint8 48ul{ recallable b }

val randombytes_init_:
    entropy_input:lbuffer uint8 48ul
  -> Stack unit
    (requires fun h -> live h entropy_input)
    (ensures  fun h0 _ h1 -> 
      modifies1 state h0 h1 /\
      as_seq h1 state == S.randombytes_init_ (as_seq h0 entropy_input))

val randombytes_:
    len:size_t
  -> res:lbuffer uint8 len
  -> Stack unit
    (requires fun h -> live h res)
    (ensures  fun h0 _ h1 ->
      modifies2 res state h0 h1 /\
      (let r, st = S.randombytes_ (as_seq h0 state) (v len) in
       r == as_seq h1 res /\ st == as_seq h1 state))
