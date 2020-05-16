module Hacl.Interface.P256.ECDSA

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
open Spec.ECDSA

open Spec.ECDSAP256.Definition

open Hacl.Impl.P256.LowLevel 

open Hacl.Impl.P256.Core

open Hacl.Impl.ECDSA.MM.Exponent
open Hacl.Impl.ECDSA.MontgomeryMultiplication

open Hacl.Impl.P256.Signature.Common

open Hacl.Impl.ECDSA.P256SHA256.Signature.Agile

open Hacl.Impl.ECDSA.P256SHA256.Verification.Agile

open Hacl.Impl.P256.Compression

open Spec.Hash.Definitions
open Hacl.Hash.Definitions


let ecdsa_sign_p256_sha2 result mLen m privKey k = 
  ecdsa_signature (Hash SHA2_256) result mLen m privKey k

let ecdsa_sign_p256_sha384 result mLen m privKey k = 
  ecdsa_signature (Hash SHA2_384) result mLen m privKey k

let ecdsa_sign_p256_sha512 result mLen m privKey k = 
  ecdsa_signature (Hash SHA2_512) result mLen m privKey k

let ecdsa_sign_p256_without_hash result mLen m privKey k = 
  ecdsa_signature NoHash result mLen m privKey k


let ecdsa_verif_p256_sha2 mLen m pubKey r s = 
  ecdsa_verification (Hash SHA2_256) pubKey r s mLen m

let ecdsa_verif_p256_sha384 mLen m pubKey r s = 
  ecdsa_verification (Hash SHA2_384) pubKey r s mLen m

let ecdsa_verif_p256_sha512 mLen m pubKey r s = 
  ecdsa_verification (Hash SHA2_512) pubKey r s mLen m

let ecdsa_verif_without_hash mLen m pubKey r s =
   ecdsa_verification NoHash pubKey r s mLen m



let verifyQ pubKey = 
    Hacl.Impl.P256.Signature.Common.verifyQ pubKey


let decompressionNotCompressedForm b result = 
  Hacl.Impl.P256.Compression.decompressionNotCompressedForm b result

let decompressionCompressedForm b result = 
  Hacl.Impl.P256.Compression.decompressionCompressedForm b result



let compressionNotCompressedForm b result = 
  Hacl.Impl.P256.Compression.compressionNotCompressedForm b result

let compressionCompressedForm b result = 
  Hacl.Impl.P256.Compression.compressionCompressedForm b result

 

let reduction_8_32 x result = Hacl.Impl.ECDSA.Reduction.reduction_8_32 x result 
