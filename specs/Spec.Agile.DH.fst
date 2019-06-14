module Spec.DH

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence


/// Constants

type algorithm =
  | DH_Curve25519
  | DH_Curve448

inline_for_extraction
let size_key (a:algorithm) : Tot size_nat =
  match a with
  | DH_Curve25519 -> 32
  | DH_Curve448 -> 56


/// Types

type key (a:algorithm) = lbytes (size_key a)
type scalar (a:algorithm) = lbytes (size_key a)
type serialized_point (a:algorithm) = lbytes (size_key a)


/// Functions

val scalarmult:
    a:algorithm{a == DH_Curve25519 \/ a == DH_Curve448}
  -> k:scalar a
  -> u:serialized_point a ->
  Tot (serialized_point a)

let scalarmult a k u =
  match a with
  | DH_Curve25519 -> Spec.Curve25519.scalarmult k u
  | DH_Curve448 -> Spec.Curve448.scalarmult k u


val dh: a:algorithm -> k0:key a -> k1:key a -> Tot (option (key a))
let dh a k0 k1 =
  let secret =
    match a with
    | DH_Curve25519 -> scalarmult a k0 k1
    | DH_Curve448 -> scalarmult a k0 k1
  in
  let result : bool = not (lbytes_eq (create (size_key a) (u8 0)) secret) in
  if result then Some secret else None


val secret_to_public: a:algorithm -> key a -> Tot (key a)
let secret_to_public a kpriv =
  match a with
  | DH_Curve25519 -> Spec.Curve25519.secret_to_public kpriv
  | DH_Curve448 -> Spec.Curve448.secret_to_public kpriv
