module Hacl.Ed25519

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

val sign:
    signature:lbuffer uint8 64ul
  -> priv:lbuffer uint8 32ul
  -> len:size_t{v len + 64 <= max_size_t}
  -> msg:lbuffer uint8 len ->
  Stack unit
    (requires fun h -> live h signature /\ live h msg /\ live h priv)
    (ensures  fun h0 _ h1 -> modifies (loc signature) h0 h1 /\
      as_seq h1 signature == Spec.Ed25519.sign (as_seq h0 priv) (as_seq h0 msg))

val verify:
    pub:lbuffer uint8 32ul
  -> len:size_t{v len + 64 <= max_size_t}
  -> msg:lbuffer uint8 len
  -> signature:lbuffer uint8 64ul ->
  Stack bool
    (requires fun h -> live h pub /\ live h msg /\ live h signature)
    (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
      b == Spec.Ed25519.verify (as_seq h0 pub) (as_seq h0 msg) (as_seq h0 signature)
    )

val secret_to_public:
    pub:lbuffer uint8 32ul
  -> priv:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h -> live h pub /\ live h priv /\ disjoint pub priv)
    (ensures  fun h0 _ h1 -> modifies (loc pub) h0 h1 /\
      as_seq h1 pub == Spec.Ed25519.secret_to_public (as_seq h0 priv)
    )

val expand_keys:
    ks:lbuffer uint8 96ul
  -> priv:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h -> live h ks /\ live h priv /\ disjoint ks priv)
    (ensures  fun h0 _ h1 -> modifies (loc ks) h0 h1 /\
      (let pub, s, prefix = Spec.Ed25519.expand_keys (as_seq h0 priv) in
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
