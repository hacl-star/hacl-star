module EverCrypt.Curve25519

/// A multiplexed frontend for Curve25519.

module ST = FStar.HyperStack.ST

open FStar.HyperStack.ST

open Lib.Buffer
open Lib.IntTypes

// We can't re-export this signature with a standard ulib type because of secret
// integers. So, for now, the type is done using HACL* types.
(** @type: true
*)
val secret_to_public:
    pub:lbuffer uint8 32ul
  -> priv:lbuffer uint8 32ul
  -> Stack unit
    (requires fun h0 ->
      live h0 pub /\ live h0 priv /\ disjoint pub priv)
    (ensures  fun h0 _ h1 -> modifies (loc pub) h0 h1 /\
      as_seq h1 pub == Spec.Curve25519.secret_to_public (as_seq h0 priv))

(** @type: true
*)
val ecdh:
    shared:lbuffer uint8 32ul
  -> my_priv:lbuffer uint8 32ul
  -> their_pub:lbuffer uint8 32ul
  -> Stack unit
    (requires fun h0 ->
      live h0 shared /\ live h0 my_priv /\ live h0 their_pub /\
      disjoint shared my_priv /\ disjoint shared their_pub)
    (ensures  fun h0 _ h1 -> modifies (loc shared) h0 h1 /\
      as_seq h1 shared == Spec.Curve25519.scalarmult (as_seq h0 my_priv) (as_seq h0 their_pub))
