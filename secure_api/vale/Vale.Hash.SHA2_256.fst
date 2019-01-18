module Vale.Hash.SHA2_256

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer

open C.Compat.Loops

open Hacl.Spec.Endianness
open Hacl.Cast
open Hacl.UInt8
open Hacl.UInt32
open FStar.UInt32

open Hacl.Hash.Lib.Create
open Hacl.Hash.Lib.LoadStore


(* Definition of aliases for modules *)
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

module H32 = Hacl.UInt32
module H64 = Hacl.UInt64

module HS = FStar.HyperStack
module Buffer = FStar.Buffer
module Cast = Hacl.Cast

module Spec = Spec.SHA2_256
module Lemmas = Hacl.Hash.SHA2_256.Lemmas


(* Definition of base types *)
private let uint8_t   = FStar.UInt8.t
private let uint32_t  = FStar.UInt32.t
private let uint64_t  = FStar.UInt64.t

private let uint8_ht  = Hacl.UInt8.t
private let uint32_ht = Hacl.UInt32.t
private let uint64_ht = Hacl.UInt64.t

private let uint32_p = Buffer.buffer uint32_ht
private let uint8_p  = Buffer.buffer uint8_ht

#reset-options "--max_fuel 0  --z3rlimit 10"

//
// SHA-256
//

(* Define word size *)
inline_for_extraction let word_length = 4ul // Size of the word in bytes

(* Define algorithm parameters *)
inline_for_extraction let state_word_length   = 8ul // 8 words (Final hash output size)
inline_for_extraction let block_word_length  = 16ul  // 16 words (Working data block size)
inline_for_extraction let hash_length     = word_length *^ state_word_length
inline_for_extraction let block_length    = word_length *^ block_word_length
inline_for_extraction let max_input_len = 2305843009213693952uL // 2^61 Bytes

(* Sizes of objects in the state *)
inline_for_extraction let size_k_w     = 64ul  // 2048 bits = 64 words of 32 bits (block_length)
inline_for_extraction let size_ws_w    = size_k_w
inline_for_extraction let size_whash_w = state_word_length
inline_for_extraction let size_count_w = 1ul  // 1 word
inline_for_extraction let len_length   = 2ul *^ word_length

inline_for_extraction let size_state   = size_k_w +^ size_ws_w +^ size_whash_w +^ size_count_w

(* Positions of objects in the state *)
inline_for_extraction let pos_k_w      = 0ul
inline_for_extraction let pos_ws_w     = size_k_w
inline_for_extraction let pos_whash_w  = size_k_w +^ size_ws_w
inline_for_extraction let pos_count_w  = size_k_w +^ size_ws_w +^ size_whash_w

open Hacl.Hash.SHA2_256.PrePost

assume val init:
  state:uint32_p{length state = v size_state} ->
  Stack unit
    (requires (fun h0 -> init_pre h0 state))
    (ensures  (fun h0 r h1 -> init_post h0 r h1 state))

assume val update:
  state :uint32_p {length state = v size_state} ->
  data  :uint8_p  {length data = v block_length /\ disjoint state data} ->
  Stack unit
        (requires (fun h0 -> update_pre h0 state data))
        (ensures  (fun h0 r h1 -> update_post h0 r h1 state data))

assume val update_last:
  state :uint32_p {length state = v size_state} ->
  data  :uint8_p  {disjoint state data} ->
  len   :uint32_t {v len = length data /\ (length data + v len_length + 1) < 2 * v block_length} ->
  Stack unit
        (requires (fun h0 -> update_last_pre h0 state data len))
        (ensures  (fun h0 r h1 -> update_last_post h0 r h1 state data len))

assume val finish:
  state :uint32_p{length state = v size_state} ->
  hash  :uint8_p{length hash = v hash_length /\ disjoint state hash} ->
  Stack unit
        (requires (fun h0 -> finish_pre h0 state hash))
        (ensures  (fun h0 r h1 -> finish_post h0 r h1 state hash))
