module Hacl.Agile.Hash

open FStar.HyperStack.ST
open FStar.Integers
open Spec.Hash.Definitions
open Hacl.Hash.Definitions

module HS = FStar.HyperStack
module B = LowStar.Buffer
module M = LowStar.Modifies
module G = FStar.Ghost

open LowStar.BufferOps

friend EverCrypt.Hash

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

let _sync_decl = ()

let freeable_s (#i: impl) =
  EverCrypt.Hash.freeable_s #(dfst i)

let footprint_s #i = EverCrypt.Hash.footprint_s #(dfst i)
let invariant_s #i = EverCrypt.Hash.invariant_s #(dfst i)
let repr #i = EverCrypt.Hash.repr #(dfst i)

let alg_of_state i s =
  let open EverCrypt.Hash in
  allow_inversion Hacl.Impl.Blake2.Core.m_spec;
  match !*s with
  | MD5_s _ -> md5
  | SHA1_s _ -> sha1
  | SHA2_224_s _ -> sha2_224
  | SHA2_256_s _ -> sha2_256
  | SHA2_384_s _ -> sha2_384
  | SHA2_512_s _ -> sha2_512
  | SHA3_224_s _ -> sha3_224
  | SHA3_256_s _ -> sha3_256
  | SHA3_384_s _ -> sha3_384
  | SHA3_512_s _ -> sha3_512
  | Blake2S_s _ -> admit (); blake2s_32
  | Blake2S_128_s _ _ -> admit (); blake2s_128
  | Blake2B_s _ -> admit (); blake2b_32
  | Blake2B_256_s _ _ -> admit (); blake2b_256
