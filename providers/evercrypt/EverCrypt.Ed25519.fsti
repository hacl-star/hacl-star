module EverCrypt.Ed25519

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

/// This module multiplexes transparently between various implementations of
/// Ed25519 depending on one's CPU capabilities.

val secret_to_public:
    public_key:lbuffer uint8 32ul
  -> private_key:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h ->
      live h public_key /\ live h private_key /\ disjoint public_key private_key)
    (ensures  fun h0 _ h1 -> modifies (loc public_key) h0 h1 /\
      as_seq h1 public_key == Spec.Ed25519.secret_to_public (as_seq h0 private_key))


val expand_keys:
    expanded_keys:lbuffer uint8 96ul
  -> private_key:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h ->
      live h expanded_keys /\ live h private_key /\ disjoint expanded_keys private_key)
    (ensures  fun h0 _ h1 -> modifies (loc expanded_keys) h0 h1 /\
     (let public_key, s, prefix = Spec.Ed25519.expand_keys (as_seq h0 private_key) in
      as_seq h1 (gsub expanded_keys 0ul 32ul) == public_key /\
      as_seq h1 (gsub expanded_keys 32ul 32ul) == s /\
      as_seq h1 (gsub expanded_keys 64ul 32ul) == prefix))


val sign_expanded:
    signature:lbuffer uint8 64ul
  -> expanded_keys:lbuffer uint8 96ul
  -> msg_len:size_t
  -> msg:lbuffer uint8 msg_len ->
  Stack unit
    (requires fun h ->
      live h signature /\ live h msg /\ live h expanded_keys /\
      disjoint signature msg /\ disjoint signature expanded_keys)
    (ensures  fun h0 _ h1 -> modifies (loc signature) h0 h1 /\
      as_seq h1 signature == Spec.Ed25519.sign_expanded
        (as_seq h0 (gsub expanded_keys 0ul 32ul))
        (as_seq h0 (gsub expanded_keys 32ul 32ul))
        (as_seq h0 (gsub expanded_keys 64ul 32ul))
        (as_seq h0 msg))


val sign:
    signature:lbuffer uint8 64ul
  -> private_key:lbuffer uint8 32ul
  -> msg_len:size_t
  -> msg:lbuffer uint8 msg_len ->
  Stack unit
    (requires fun h ->
      live h signature /\ live h msg /\ live h private_key /\
      disjoint signature msg /\ disjoint signature private_key)
    (ensures  fun h0 _ h1 -> modifies (loc signature) h0 h1 /\
      as_seq h1 signature == Spec.Ed25519.sign (as_seq h0 private_key) (as_seq h0 msg))


val verify:
    public_key:lbuffer uint8 32ul
  -> msg_len:size_t
  -> msg:lbuffer uint8 msg_len
  -> signature:lbuffer uint8 64ul ->
  Stack bool
    (requires fun h -> live h public_key /\ live h msg /\ live h signature)
    (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
      b == Spec.Ed25519.verify (as_seq h0 public_key) (as_seq h0 msg) (as_seq h0 signature))
