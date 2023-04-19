module Spec.Agile.DH

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence


/// Constants

type algorithm =
  | DH_Curve25519
  | DH_P256

inline_for_extraction
let size_key (a:algorithm) : Tot size_nat =
  match a with
  | DH_Curve25519 -> 32
  | DH_P256 -> 32

inline_for_extraction
let size_public (a:algorithm) : Tot size_nat =
  match a with
  | DH_Curve25519 -> 32
  | DH_P256 -> 64

inline_for_extraction
let prime (a:algorithm) =
  match a with
  | DH_Curve25519 -> Spec.Curve25519.prime
  | DH_P256 -> Spec.P256.prime

/// Types

type scalar (a:algorithm) = lbytes (size_key a)
type serialized_point (a:algorithm) = lbytes (size_public a)


/// Functions

val clamp: alg:algorithm{alg = DH_Curve25519} -> scalar alg -> Tot (scalar alg)
let clamp a k =
  match a with
  | DH.DH_Curve25519 -> Spec.Curve25519.decodeScalar k

#set-options "--z3rlimit 50"

val dh: a:algorithm -> s:scalar a -> p:serialized_point a -> Tot (option (serialized_point a))
let dh a s p =
  match a with
  | DH_Curve25519 ->
    let output = Spec.Curve25519.scalarmult s p in
    let is_valid = not (lbytes_eq (create (size_public a) (u8 0)) output) in
    if is_valid then Some output else None
  | DH_P256 ->
    Spec.P256.ecdh p s

val secret_to_public: a:algorithm -> scalar a -> Tot (option (serialized_point a))
let secret_to_public a kpriv =
  match a with
  | DH_Curve25519 -> Some (Spec.Curve25519.secret_to_public kpriv)
  | DH_P256 -> Spec.P256.secret_to_public kpriv
