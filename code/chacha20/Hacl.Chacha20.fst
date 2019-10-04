module Hacl.Chacha20

open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer


val chacha20_encrypt:
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
    as_seq h1 out == Spec.Chacha20.chacha20_encrypt_bytes (as_seq h0 key) (as_seq h0 n) (v ctr) (as_seq h0 text))

let chacha20_encrypt len out text key n ctr =
  Hacl.Impl.Chacha20.chacha20_encrypt len out text key n ctr


val chacha20_decrypt:
    len:size_t
  -> out:lbuffer uint8 len
  -> cipher:lbuffer uint8 len
  -> key:lbuffer uint8 32ul
  -> n:lbuffer uint8 12ul
  -> ctr:size_t ->
  Stack unit
  (requires fun h ->
    live h key /\ live h n /\ live h cipher /\ live h out /\ eq_or_disjoint cipher out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.Chacha20.chacha20_decrypt_bytes (as_seq h0 key) (as_seq h0 n) (v ctr) (as_seq h0 cipher))

let chacha20_decrypt len out cipher key n ctr =
  Hacl.Impl.Chacha20.chacha20_decrypt len out cipher key n ctr
