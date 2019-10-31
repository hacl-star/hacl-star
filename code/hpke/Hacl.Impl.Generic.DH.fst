module Hacl.Impl.Generic.DH

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.Buffer
open Lib.IntTypes

module DH = Spec.Agile.DH
module S = Spec.Agile.HPKE

#set-options "--z3rlimit 20 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"

unfold noextract
let nsize_key (a:DH.algorithm) =
  match a with
  | DH.DH_Curve25519 -> 32ul
  | DH.DH_Curve448 -> 56ul
  | DH.DH_P256 -> 32ul

unfold noextract
let nsize_public (a:DH.algorithm) =
  match a with
  | DH.DH_Curve25519 -> 32ul
  | DH.DH_Curve448 -> 56ul
  | DH.DH_P256 -> 64ul

inline_for_extraction noextract
let scalarmult_st (a:DH.algorithm) =
     k:lbuffer uint8 (nsize_key a)
  -> i:lbuffer uint8 (nsize_public a)
  -> o:lbuffer uint8 (nsize_public a)
  -> ST unit
     (requires fun h0 ->
       live h0 o /\ live h0 k /\ live h0 i /\
       disjoint o i /\ disjoint o k)
     (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\
       as_seq h1 o == DH.scalarmult a (as_seq h0 k) (as_seq h0 i))

[@ Meta.Attribute.specialize]
assume val scalarmult: #a:S.ciphersuite -> scalarmult_st (S.curve_of_cs a)

inline_for_extraction noextract
let secret_to_public_st (a: DH.algorithm) =
    o:lbuffer uint8 (nsize_public a)
  -> i:lbuffer uint8 (nsize_key a)
  -> Stack unit
    (requires fun h0 ->
      live h0 o /\ live h0 i /\ disjoint o i)
    (ensures  fun h0 _ h1 -> modifies (loc o) h0 h1 /\
      as_seq h1 o == DH.secret_to_public a (as_seq h0 i))

[@ Meta.Attribute.specialize]
assume val secret_to_public: #a:S.ciphersuite -> secret_to_public_st (S.curve_of_cs a)
