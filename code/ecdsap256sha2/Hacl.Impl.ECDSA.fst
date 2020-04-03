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

open Spec.P256
open Spec.P256.Lemmas
open Spec.P256.Definitions

open Spec.ECDSAP256.Definition

open Hacl.Impl.LowLevel

open Hacl.Impl.P256

open Hacl.Impl.ECDSA.MM.Exponent
open Hacl.Impl.ECDSA.MontgomeryMultiplication

open Hacl.Impl.P256.Signature.Common


open Hacl.Impl.ECDSA.P256SHA256.Signature.Agile
open Hacl.Impl.ECDSA.P256SHA256.Signature.Blake2

open Hacl.Impl.ECDSA.P256SHA256.Verification.Agile
open Hacl.Impl.ECDSA.P256SHA256.Verification.Blake2

open Hacl.Impl.P256.Compression

open Spec.Hash.Definitions
open Hacl.Hash.Definitions


let ecdsa_sign_p256_sha2 result mLen m privKey k = 
  ecdsa_signature SHA2_256 result mLen m privKey k

let ecdsa_sign_p256_blake2 result mLen m privKey k = 
  ecdsa_signature_blake2 result mLen m privKey k

let ecdsa_sign_p256_without_hash result m privKey k = 
  Hacl.Impl.ECDSA.P256SHA256.Signature.Hashless.ecdsa_signature_without_hash result m privKey k


let ecdsa_verif_p256_sha2 mLen m pubKey r s = 
  Hacl.Impl.ECDSA.P256SHA256.Verification.Agile.ecdsa_verification SHA2_256 pubKey r s mLen m

let ecdsa_verif_blake2 mLen m pubKey r s =
  Hacl.Impl.ECDSA.P256SHA256.Verification.Blake2.ecdsa_verification_blake2 pubKey r s mLen m

let ecdsa_verif_without_hash m pubKey r s =
  Hacl.Impl.ECDSA.P256SHA256.Verification.Hashless.ecdsa_verification_without_hash pubKey r s m



let decompressionNotCompressedForm b result = 
  Hacl.Impl.P256.Compression.decompressionNotCompressedForm b result

let decompressionCompressedForm b result = 
  Hacl.Impl.P256.Compression.decompressionCompressedForm b result



let compressionNotCompressedForm b result = 
  Hacl.Impl.P256.Compression.compressionNotCompressedForm b result

let compressionCompressedForm b result = 
  Hacl.Impl.P256.Compression.compressionCompressedForm b result

 
