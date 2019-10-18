module EverCrypt.Ed25519

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

/// This module multiplexes transparently between various implementations of
/// Ed25519 depending on one's CPU capabilities.

val sign:
    signature:lbuffer uint8 64ul
  -> secret:lbuffer uint8 32ul
  -> len:size_t{v len + 64 <= max_size_t}
  -> msg:lbuffer uint8 len ->
  Stack unit
    (requires fun h -> live h signature /\ live h msg /\ live h secret)
    (ensures  fun h0 _ h1 -> modifies (loc signature) h0 h1)

val verify:
    output:lbuffer uint8 32ul
  -> len:size_t{v len + 64 <= max_size_t}
  -> msg:lbuffer uint8 len
  -> signature:lbuffer uint8 64ul ->
  Stack bool
    (requires fun h -> live h output /\ live h msg /\ live h signature)
    (ensures  fun h0 b h1 -> modifies0 h0 h1)

val secret_to_public:
    output:lbuffer uint8 32ul
  -> secret:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h -> live h output /\ live h secret /\ disjoint output secret)
    (ensures  fun h0 _ h1 -> modifies (loc output) h0 h1)

val expand_keys:
    ks:lbuffer uint8 96ul
  -> secret:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h -> live h ks /\ live h secret /\ disjoint ks secret)
    (ensures  fun h0 _ h1 -> modifies (loc ks) h0 h1)

val sign_expanded:
    signature:lbuffer uint8 64ul
  -> ks:lbuffer uint8 96ul
  -> len:size_t{v len + 64 <= max_size_t}
  -> msg:lbuffer uint8 len ->
  Stack unit
    (requires fun h -> live h signature /\ live h msg /\ live h ks)
    (ensures  fun h0 _ h1 -> modifies (loc signature) h0 h1)
