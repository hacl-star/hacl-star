module Hacl.Hash.Blake2

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

module M = LowStar.Modifies
module B = LowStar.Buffer
module Spec = Spec.Hash.PadFinish
module Blake2 = Hacl.Impl.Blake2.Core

open Lib.IntTypes
open Spec.Hash.Definitions
open FStar.Mul

open Spec.Hash.Definitions
open Hacl.Hash.Definitions

include Hacl.Hash.Core.Blake2

(* The stateful signature for [Spec.Blake2.blake2_update_last], but where
 * the input is actually the remaining data (smaller than a block) *)
noextract inline_for_extraction
let blake2_update_last_block (a : hash_alg{is_blake a}) =
  s:state a ->
  ev:extra_state a ->
  input:B.buffer uint8 ->
  input_len:size_t { B.length input == v input_len /\ v input_len <= block_length a /\
                     (v #U64 #SEC ev) + v input_len <= max_input a } ->
  ST.Stack (extra_state a)
    (requires (fun h ->
      B.live h s /\ B.live h input /\ B.disjoint s input))
    (ensures (fun h0 ev' h1 ->
      B.(modifies (loc_buffer s) h0 h1) /\
      as_seq h1 s ==
        Spec.Blake2.blake2_update_last (to_blake_alg a) (v #U64 #SEC ev)
                                       (v input_len) (B.as_seq h0 input) (as_seq h0 s)))

val update_multi_blake2s: update_multi_st Blake2S
val update_multi_blake2b: update_multi_st Blake2B

val update_last_blake2s: update_last_st Blake2S
val update_last_blake2b: update_last_st Blake2B

val hash_blake2s: hash_st Blake2S
val hash_blake2b: hash_st Blake2B
