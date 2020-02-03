module Hacl.Impl.ECDSA

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence

open FStar.Mul
open FStar.Math.Lemmas

open Hacl.Hash.SHA2

open Hacl.Spec.P256
open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.Definitions

open Hacl.Spec.ECDSAP256.Definition

open Hacl.Impl.LowLevel

open Hacl.Impl.P256

open Hacl.Impl.ECDSA.MM.Exponent
open Hacl.Impl.ECDSA.MontgomeryMultiplication

open Hacl.Impl.P256.Signature.Common

open Hacl.Impl.ECDSA.P256SHA256.KeyGeneration
open Hacl.Impl.ECDSA.P256SHA256.Signature
open Hacl.Impl.ECDSA.P256SHA256.Verification

let ecdsa_p256_sha2_keyGen result privKey = key_gen result privKey

let ecdsa_p256_sha2_sign result mLen m privKey k = ecdsa_signature result mLen m privKey k

let ecdsa_p256_sha2_sign_nist result m privKey k = ecdsa_signature_nist_compliant result m privKey k

let ecdsa_p256_sha2_verify mLen m pubKey r s =
  ecdsa_verification pubKey r s mLen m

let ecdsa_p256_sha2_verify_u8 mLen m pubKey r s =
  ecdsa_verification_u8 pubKey r s mLen m
