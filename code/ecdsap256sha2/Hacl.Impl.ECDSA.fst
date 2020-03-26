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

open Hacl.Impl.ECDSA.P256SHA256.Signature
open Hacl.Impl.ECDSA.P256SHA256.Verification

open Hacl.Impl.P256.Compression

open Spec.Hash.Definitions
open Hacl.Hash.Definitions


let ecdsa_p256_sha2_sign result mLen m privKey k = 
  ecdsa_signature SHA2_256 result mLen m privKey k

let ecdsa_p256_sha2_verify mLen m pubKey r s =
  ecdsa_verification pubKey r s mLen m


let decompressionNotCompressedForm b result = 
  Hacl.Impl.P256.Compression.decompressionNotCompressedForm b result

let decompressionCompressedForm b result = 
  Hacl.Impl.P256.Compression.decompressionCompressedForm b result


let compressionNotCompressedForm b result = 
  Hacl.Impl.P256.Compression.compressionNotCompressedForm b result


let compressionCompressedForm b result = 
  Hacl.Impl.P256.Compression.compressionCompressedForm b result

 
