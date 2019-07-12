module Hacl.HKDF_SHA2_256

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.LoopCombinators

module ST = FStar.HyperStack.ST
module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators

module SpecSHA2 = Spec.SHA2
module SpecHash = Spec.Hash
module SpecHMAC = Spec.HMAC

module Hash = Hacl.Impl.SHA2_256
module HMAC = Hacl.Impl.HMAC_SHA2_256


module Impl = Hacl.Impl.HKDF_SHA2_256


inline_for_extraction noextract
let a = Spec.SHA2.SHA2_256



val hkdf_extract:
    output: buffer uint8{length output == Spec.SHA2.size_hash a}
  -> salt: buffer uint8 {length salt <= Spec.SHA2.max_input a}
  -> slen: size_t{v slen == length salt}
  -> ikm: buffer uint8
  -> ilen: size_t{ v ilen == length ikm
                /\ length salt + length ikm + Spec.SHA2.size_block a <= Spec.SHA2.max_input a
                /\ Spec.SHA2.size_hash a + length ikm + Spec.SHA2.size_block a <= Spec.SHA2.max_input a} ->
  Stack unit
  (requires (fun h -> live h output /\ live h salt /\ live h ikm
                 /\ disjoint output salt /\ disjoint output ikm))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let hkdf_extract output salt slen ikm ilen = Impl.hkdf_extract output salt slen ikm ilen




val hkdf_expand:
    output: buffer uint8
  -> prk: buffer uint8
  -> plen: size_t{v plen == length prk /\ length prk <= Spec.SHA2.max_input a}
  -> info: buffer uint8
  -> ilen: size_t{ v ilen == length info
                /\ length info + Spec.SHA2.size_hash a + 1 <= max_size_t
                /\ length prk + length info + 1 + Spec.SHA2.size_hash a + Spec.SHA2.size_block a <= Spec.SHA2.max_input a}
  -> len: size_t{ v len == length output
               /\ v len + Spec.SHA2.size_hash a <= max_size_t
               /\ v len / (Spec.SHA2.size_hash a) + 2 <= 255} ->
  Stack unit
  (requires (fun h -> live h output /\ live h prk /\ live h info
                 /\ disjoint output prk /\ disjoint output info))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let hkdf_expand output prk plen info ilen len = Impl.hkdf_expand output prk plen info ilen len
