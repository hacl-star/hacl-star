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

inline_for_extraction
let order (a:algorithm) =
  match a with
  | DH_Curve25519 -> pow2 252 + 0x14def9dea2f79cd65812631a5cf5d3ed
  | DH_P256 -> pow2 256 - 432420386565659656852420866394968145599


/// Types

type scalar (a:algorithm) = lbytes (size_key a)
type serialized_point (a:algorithm) = lbytes (size_public a)


/// Functions

val clamp: alg:algorithm{alg <> DH_P256} -> scalar alg -> Tot (scalar alg)
let clamp a k =
  match a with
  | DH.DH_Curve25519 -> Spec.Curve25519.decodeScalar k

val scalarmult:
    a:algorithm{a <> DH_P256}
  -> k:scalar a
  -> u:serialized_point a ->
  Tot (serialized_point a)

let scalarmult a k u =
  match a with
  | DH_Curve25519 -> Spec.Curve25519.scalarmult k u


val dh: a:algorithm -> s:scalar a -> p:serialized_point a -> Tot (option (serialized_point a))
let dh a s p =
    match a with
    | DH_Curve25519 -> (
      let output = Spec.Curve25519.scalarmult s p in
      if lbytes_eq (create (size_public a) (u8 0)) output then None else Some output)
    | DH_P256 -> (
      let py = sub p 32 32 in
      let px = sub p 0 32 in
      let (rx,ry,res) = Spec.DH.ecp256_dh_r px py s in
      if v res = 0xFFFFFFFFFFFFFFFF then None else Some (concat rx ry))

#set-options "--z3rlimit 50"

val secret_to_public: a:algorithm -> scalar a -> Tot (option (serialized_point a))
let secret_to_public a kpriv =
  match a with
  | DH_Curve25519 -> (
    let output = Spec.Curve25519.secret_to_public kpriv in
    if lbytes_eq (create (size_public a) (u8 0)) output then Some output else None)
  | DH_P256 -> (
    let (rx,ry,res) = Spec.DH.ecp256_dh_i kpriv in
    if v res = 0xFFFFFFFFFFFFFFFF then None else Some (concat rx ry))
