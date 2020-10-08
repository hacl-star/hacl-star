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
  let result, output : bool & serialized_point a =
    match a with
    | DH_Curve25519 ->
        let output = Spec.Curve25519.scalarmult s p in
        not (lbytes_eq (create (size_public a) (u8 0)) output), output
    | DH_P256 ->
        let xN, yN, res = Spec.DH.ecp256_dh_r (sub p 0 32) (sub p 32 32) s in
        res, xN @| yN
  in
  if result then Some output else None

val secret_to_public: a:algorithm -> scalar a -> Tot (option (serialized_point a))
let secret_to_public a kpriv =
  match a with
  | DH_Curve25519 -> Some (Spec.Curve25519.secret_to_public kpriv)
  | DH_P256 ->
      let xN, yN, res = Spec.DH.ecp256_dh_i kpriv in
      if res then Some (xN @| yN) else None
