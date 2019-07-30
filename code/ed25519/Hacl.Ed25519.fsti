module Hacl.Ed25519

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

val sign:
    signature:lbuffer uint8 64ul
  -> secret:lbuffer uint8 32ul
  -> len:size_t{v len + 64 <= max_size_t}
  -> msg:lbuffer uint8 len ->
  Stack unit
    (requires fun h -> live h signature /\ live h msg /\ live h secret)
    (ensures  fun h0 _ h1 -> modifies (loc signature) h0 h1 /\
      as_seq h1 signature == Spec.Ed25519.sign (as_seq h0 secret) (as_seq h0 msg))

val verify:
    output:lbuffer uint8 32ul
  -> len:size_t{v len + 64 <= max_size_t}
  -> msg:lbuffer uint8 len
  -> signature:lbuffer uint8 64ul ->
  Stack bool
    (requires fun h -> live h output /\ live h msg /\ live h signature)
    (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
      b == Spec.Ed25519.verify (as_seq h0 output) (as_seq h0 msg) (as_seq h0 signature)
    )

val secret_to_public:
    output:lbuffer uint8 32ul
  -> secret:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h -> live h output /\ live h secret /\ disjoint output secret)
    (ensures  fun h0 _ h1 -> modifies (loc output) h0 h1 /\
      as_seq h1 output == Spec.Ed25519.secret_to_public (as_seq h0 secret)
    )

val expand_keys:
    ks:lbuffer uint8 96ul
  -> secret:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h -> live h ks /\ live h secret /\ disjoint ks secret)
    (ensures  fun h0 _ h1 -> modifies (loc ks) h0 h1 /\
      (let pub, s, prefix = Spec.Ed25519.expand_keys (as_seq h0 secret) in
      as_seq h1 (gsub ks 0ul 32ul) == pub /\
      as_seq h1 (gsub ks 32ul 32ul) == s /\
      as_seq h1 (gsub ks 64ul 32ul) == prefix)
    )

val sign_expanded:
    signature:lbuffer uint8 64ul
  -> ks:lbuffer uint8 96ul
  -> len:size_t{v len + 64 <= max_size_t}
  -> msg:lbuffer uint8 len ->
  Stack unit
    (requires fun h -> live h signature /\ live h msg /\ live h ks)
    (ensures  fun h0 _ h1 -> modifies (loc signature) h0 h1 /\
      as_seq h1 signature == Spec.Ed25519.sign_expanded
        (as_seq h0 (gsub ks 0ul 32ul))
        (as_seq h0 (gsub ks 32ul 32ul))
        (as_seq h0 (gsub ks 64ul 32ul))
        (as_seq h0 msg)
    )
