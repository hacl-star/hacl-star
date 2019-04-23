module Hacl.Hash.SHA2

open Hacl.Hash.Definitions
open Spec.Hash.Definitions

include Hacl.Hash.Core.SHA2

val update_multi_224: update_multi_st SHA2_224
val update_multi_256: update_multi_st SHA2_256
val update_multi_384: update_multi_st SHA2_384
val update_multi_512: update_multi_st SHA2_512

val update_last_224: update_last_st SHA2_224
val update_last_256: update_last_st SHA2_256
val update_last_384: update_last_st SHA2_384
val update_last_512: update_last_st SHA2_512

val hash_224: hash_st SHA2_224
val hash_256: hash_st SHA2_256
val hash_384: hash_st SHA2_384
val hash_512: hash_st SHA2_512

// Interface that exposes a sha2-512 signature suitable for calling from HACL-lib code.
module BF = Arch.BufferFriend

open Lib.IntTypes
open Lib.Sequence
open Lib.Buffer

noextract inline_for_extraction
val hash_512_lib:
  input_len:size_t ->
  input:lbuffer uint8 input_len ->
  dst:lbuffer uint8 64ul ->
  HyperStack.ST.Stack unit
    (requires (fun h ->
      live h input /\
      live h dst /\
      disjoint input dst /\
      length input < max_input_length SHA2_512))
    (ensures (fun h0 _ h1 ->
      modifies1 dst h0 h1 /\
      as_seq h1 dst ==
      Spec.Hash.hash SHA2_512 (as_seq h0 input)))






