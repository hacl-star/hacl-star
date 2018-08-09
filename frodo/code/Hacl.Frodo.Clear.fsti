module Hacl.Frodo.Clear

open FStar.HyperStack.All
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.PQ.Buffer

val clear_words_u16:
    len:size_t
  -> b:lbuffer uint16 (v len)
  -> Stack unit
    (requires fun h -> live h b)
    (ensures  fun h0 _ h1 -> live h1 b /\ modifies (loc_buffer b) h0 h1)

val clear_words_u8:
    len:size_t
  -> b:lbuffer uint8 (v len)
  -> Stack unit
    (requires fun h -> live h b)
    (ensures  fun h0 _ h1 -> live h1 b /\ modifies (loc_buffer b) h0 h1)
