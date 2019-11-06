module Spec.HMAC_DRBG

open Lib.IntTypes
open FStar.Seq
open FStar.Mul

open Spec.Hash.Definitions
open Spec.Agile.HMAC

/// HMAC-DRBG
///
/// See 10.1.2 in
/// https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-90Ar1.pdf
///

#set-options "--max_fuel 0 --max_ifuel 0"

let supported_alg = a:hash_alg{ is_supported_alg a }

let reseed_interval                   = pow2 10
let max_output_length                 = pow2 16
let max_length                        = pow2 16
let max_personalization_string_length = pow2 16
let max_additional_input_length       = pow2 16

/// See p.54
/// https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-57pt1r4.pdf
let min_length (a:supported_alg) =
  match a with
  | SHA1 -> 16
  | SHA2_256 | SHA2_384 | SHA2_512 -> 32

val state: supported_alg -> Type0

val hmac_input_bound: a:supported_alg -> Lemma
  (hash_length a + pow2 32 + pow2 32
    + 1 + block_length a + block_length a <= max_input_length a)

val instantiate: #a:supported_alg
  -> entropy_input:bytes
  -> nonce:bytes
  -> personalization_string:bytes
  -> Pure (state a)
  (requires
    hash_length a
    + Seq.length entropy_input
    + Seq.length nonce
    + Seq.length personalization_string
    + 1 + block_length a <= max_input_length a)
  (ensures fun _ -> True)

val reseed: #a:supported_alg
  -> state a
  -> entropy_input:bytes
  -> additional_input:bytes
  -> Pure (state a)
  (requires
    hash_length a +
    Seq.length entropy_input +
    Seq.length additional_input +
    1 + block_length a <= max_input_length a)
  (ensures fun _ -> True)

(* n is the number of **bytes** requested *)
val generate: #a:supported_alg
  -> state a
  -> n:nat
  -> additional_input:bytes
  -> Pure (option (lbytes n & state a))
  (requires
    n <= max_output_length /\
    hash_length a + Seq.length additional_input
      + 1 + block_length a <= max_input_length a)
  (ensures fun _ -> True)
