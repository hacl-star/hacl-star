module Spec.Agile.DH

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence


/// Constants

type algorithm =
  | DH_Curve25519
  | DH_Curve448
  | DH_P256

inline_for_extraction
let size_key (a:algorithm) : Tot size_nat =
  match a with
  | DH_Curve25519 -> 32
  | DH_Curve448 -> 56
  | DH_P256 -> 32

inline_for_extraction
let size_public (a:algorithm) : Tot size_nat =
  match a with
  | DH_Curve25519 -> 32
  | DH_Curve448 -> 56
  | DH_P256 -> 64

/// Types

type scalar (a:algorithm) = lbytes (size_key a)
type serialized_point (a:algorithm) = lbytes (size_public a)


/// Functions

val scalarmult:
    a:algorithm
  -> k:scalar a
  -> u:serialized_point a ->
  Tot (serialized_point a)

let scalarmult a k u =
  match a with
  | DH_Curve25519 -> Spec.Curve25519.scalarmult k u
  | DH_Curve448 -> Spec.Curve448.scalarmult k u
  | DH_P256 -> Spec.P256.scalarmult k u

#set-options "--z3rlimit 50"

val dh: a:algorithm -> s:scalar a -> p:serialized_point a -> Tot (option (serialized_point a))
let dh a s p =
  let output = scalarmult a s p in
  let result : bool =
    match a with
    | DH_Curve25519 | DH_Curve448 -> not (lbytes_eq (create (size_public a) (u8 0)) output)
    | DH_P256 ->
      let r = Spec.P256.serialized_to_point output in
      (Spec.P256.isPointOnCurve r && (not (Spec.P256.isPointAtInfinity r)))
  in
  if result then Some output else None


val secret_to_public: a:algorithm -> scalar a -> Tot (serialized_point a)
let secret_to_public a kpriv =
  match a with
  | DH_Curve25519 -> Spec.Curve25519.secret_to_public kpriv
  | DH_Curve448 -> Spec.Curve448.secret_to_public kpriv
  | DH_P256 -> Spec.P256.secret_to_public kpriv
