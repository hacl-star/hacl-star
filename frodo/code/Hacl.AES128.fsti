module Hacl.AES128

open FStar.HyperStack.All

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer

module B = LowStar.Buffer
//module S = Spec.AES128

// TODO: add functional specification
val aes128_key_expansion:
    key:lbuffer uint8 16
  -> expanded_key:lbuffer uint8 176
  -> Stack unit
  (requires fun h0 -> B.live h0 key /\ B.live h0 expanded_key /\ B.disjoint key expanded_key)
  (ensures  fun h0 _ h1 -> modifies (loc_buffer expanded_key) h0 h1)

val aes128_encrypt_block:
    cipher:lbuffer uint16 8
  -> plain:lbuffer uint16 8
  -> expanded_key:lbuffer uint8 176
  -> Stack unit
  (requires fun h0 -> B.live h0 cipher /\ B.live h0 plain /\ B.live h0 expanded_key)
  (ensures  fun h0 _ h1 -> modifies (loc_buffer cipher) h0 h1)
