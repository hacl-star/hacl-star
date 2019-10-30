module EverCrypt.Cipher

open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

module Spec = Spec.Chacha20

val chacha20:
    len:size_t
  -> out:lbuffer uint8 len
  -> text:lbuffer uint8 len
  -> key:lbuffer uint8 32ul
  -> n:lbuffer uint8 12ul
  -> ctr:size_t ->
  Stack unit
  (requires fun h ->
    live h key /\ live h n /\ live h text /\ live h out /\ eq_or_disjoint text out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.chacha20_encrypt_bytes (as_seq h0 key) (as_seq h0 n) (v ctr) (as_seq h0 text))
