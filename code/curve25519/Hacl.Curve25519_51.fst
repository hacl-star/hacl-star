module Hacl.Curve25519_51

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Curve25519.Fields
open Hacl.Impl.Curve25519.Generic

module S = Spec.Curve25519

val secret_to_public:
    pub:lbuffer uint8 32ul
  -> priv:lbuffer uint8 32ul
  -> Stack unit
    (requires fun h0 ->
      live h0 pub /\ live h0 priv /\ disjoint pub priv)
    (ensures  fun h0 _ h1 -> modifies (loc pub) h0 h1 /\
      as_seq h1 pub == S.secret_to_public (as_seq h0 priv))
let secret_to_public pub priv =
  secret_to_public #M51 pub priv


val ecdh:
    shared:lbuffer uint8 32ul
  -> my_priv:lbuffer uint8 32ul
  -> their_pub:lbuffer uint8 32ul
  -> Stack unit
    (requires fun h0 ->
      live h0 shared /\ live h0 my_priv /\ live h0 their_pub /\
      disjoint shared my_priv /\ disjoint shared their_pub)
    (ensures  fun h0 _ h1 -> modifies (loc shared) h0 h1 /\
      as_seq h1 shared == S.scalarmult (as_seq h0 my_priv) (as_seq h0 their_pub))
let ecdh shared my_priv their_pub =
  scalarmult #M51 shared my_priv their_pub
