module Hacl.Salsa20

open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer

module Spec = Spec.Salsa20


val salsa20_encrypt:
    len:size_t
  -> out:lbuffer uint8 len
  -> text:lbuffer uint8 len
  -> key:lbuffer uint8 32ul
  -> n:lbuffer uint8 8ul
  -> ctr:size_t ->
  Stack unit
  (requires fun h -> live h key /\ live h n /\ live h text /\ live h out /\ eq_or_disjoint text out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.salsa20_encrypt_bytes (as_seq h0 key) (as_seq h0 n) (v ctr) (as_seq h0 text))

let salsa20_encrypt len out text key n ctr =
  Hacl.Impl.Salsa20.salsa20_encrypt len out text key n ctr


val salsa20_decrypt:
    len:size_t
  -> out:lbuffer uint8 len
  -> cipher:lbuffer uint8 len
  -> key:lbuffer uint8 32ul
  -> n:lbuffer uint8 8ul
  -> ctr:size_t ->
  Stack unit
  (requires fun h -> live h key /\ live h n /\ live h cipher /\ live h out /\ eq_or_disjoint cipher out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.salsa20_decrypt_bytes (as_seq h0 key) (as_seq h0 n) (v ctr) (as_seq h0 cipher))

let salsa20_decrypt len out cipher key n ctr =
  Hacl.Impl.Salsa20.salsa20_decrypt len out cipher key n ctr


val salsa20_key_block0:
    out:lbuffer uint8 64ul
  -> key:lbuffer uint8 32ul
  -> n:lbuffer uint8 8ul ->
  Stack unit
  (requires fun h -> live h key /\ live h n /\ live h out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.Salsa20.salsa20_key_block0 (as_seq h0 key) (as_seq h0 n))

let salsa20_key_block0 out key n =
  Hacl.Impl.Salsa20.salsa20_key_block0 out key n


val hsalsa20:
    out:lbuffer uint8 32ul
  -> key:lbuffer uint8 32ul
  -> n:lbuffer uint8 16ul ->
  Stack unit
  (requires fun h -> live h key /\ live h n /\ live h out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.hsalsa20 (as_seq h0 key) (as_seq h0 n))

let hsalsa20 out key n =
  Hacl.Impl.HSalsa20.hsalsa20 out key n
