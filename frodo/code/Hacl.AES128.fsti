module Hacl.AES128

open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.Buffer
open Lib.IntTypes
open Lib.ByteSequence
open Lib.Sequence

module B = LowStar.Buffer
module S = Spec.AES

val aes128_key_expansion:
    key:lbuffer uint8 16
  -> expanded_key:lbuffer uint8 176
  -> Stack unit
    (requires fun h0 -> B.live h0 key /\ B.live h0 expanded_key /\ B.disjoint key expanded_key)
    (ensures  fun h0 _ h1 ->
      modifies (loc_buffer expanded_key) h0 h1 /\
      as_seq h1 expanded_key == S.aes128_key_expansion (as_seq h0 key))

val aes128_encrypt_block:
    cipher:lbuffer uint16 8
  -> plain:lbuffer uint16 8
  -> expanded_key:lbuffer uint8 176
  -> Stack unit
    (requires fun h0 -> B.live h0 cipher /\ B.live h0 plain /\ B.live h0 expanded_key)
    (ensures  fun h0 _ h1 ->
      let c = S.block_cipher (as_seq h0 expanded_key) (uints_to_bytes_le (as_seq h0 plain)) in
      let c' = as_seq h1 cipher in
      modifies (loc_buffer cipher) h0 h1 /\
      (forall (i:nat{i < 8}). c'.[i] == uint_from_bytes_le (Lib.Sequence.sub c (i * 2) 2)))
