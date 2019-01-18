module Hacl.SHA2_256

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HyperStack.All
open FStar.HyperStack.ST
open FStar.Buffer

open Hacl.Cast
open Hacl.UInt8
open Hacl.UInt32
open FStar.UInt32


(* Definition of aliases for modules *)
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module H8 = Hacl.UInt8
module H32 = Hacl.UInt32
module H64 = Hacl.UInt64

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module Buffer = FStar.Buffer
module Cast = Hacl.Cast

module Spec = Spec.SHA2_256


#reset-options "--max_fuel 0  --z3rlimit 100"


(* Definition of base types *)
private let uint8_t   = FStar.UInt8.t
private let uint32_t  = FStar.UInt32.t
private let uint64_t  = FStar.UInt64.t

private let uint8_ht  = Hacl.UInt8.t
private let uint32_ht = Hacl.UInt32.t

private let uint32_p = Buffer.buffer uint32_ht
private let uint8_p  = Buffer.buffer uint8_ht


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

type state = s:uint32_p{length s = v size_state}

let slice_k (h: HS.mem) (state: state) =
  Hacl.Spec.Endianness.reveal_h32s
    (Seq.slice (as_seq h state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)))
let slice_hash (h: HS.mem) (state: state) =
  Hacl.Spec.Endianness.reveal_h32s
    (Seq.slice (as_seq h state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)))
let seq_counter (h: HS.mem) (state: state) =
  Seq.slice (as_seq h state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w))
let counter (h: HS.mem) (state: state) =
  U32.v (Seq.index (seq_counter h state) 0)

[@"c_inline"]
val alloc:
  unit ->
  StackInline (state:uint32_p{length state = v size_state})
    (requires (fun h0 -> True))
    (ensures (fun h0 st h1 -> (st `unused_in` h0) /\ live h1 st /\ modifies_0 h0 h1 /\
      frameOf st == HS.get_tip h1 /\
      Map.domain (HS.get_hmap h1) == Map.domain (HS.get_hmap h0)))


val init:
  state:uint32_p{length state = v size_state} ->
  Stack unit
    (requires (fun h0 -> live h0 state))
    (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1 /\
      slice_k h1 state == Spec.k /\ slice_hash h1 state == Spec.h_0 /\
      counter h1 state = 0))

val update:
  state :uint32_p {length state = v size_state} ->
  data  :uint8_p  {length data = v block_length /\ disjoint state data} ->
  Stack unit
    (requires (fun h0 ->
      live h0 state /\ live h0 data /\
      slice_k h0 state == Spec.k /\ counter h0 state < pow2 32 - 1))
    (ensures (fun h0 r h1 ->
      let seq_data = Hacl.Spec.Endianness.reveal_sbytes (as_seq h0 data) in
      live h1 state /\ modifies_1 state h0 h1 /\
      slice_k h0 state == slice_k h1 state /\
      slice_hash h1 state == Spec.update (slice_hash h0 state) seq_data /\
      counter h1 state = counter h0 state + 1 /\
      counter h1 state < pow2 32))

val update_multi:
  state :uint32_p{length state = v size_state} ->
  data  :uint8_p {length data % v block_length = 0 /\ disjoint state data} ->
  n     :uint32_t{v n * v block_length = length data} ->
  Stack unit
    (requires (fun h0 ->
      live h0 state /\ live h0 data /\
      slice_k h0 state == Spec.k /\
      counter h0 state < pow2 32 - v n))
    (ensures  (fun h0 _ h1 ->
      let seq_data = Hacl.Spec.Endianness.reveal_sbytes (as_seq h0 data) in
      live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1 /\
      slice_k h1 state == Spec.k /\
      counter h1 state = counter h0 state + v n /\
      slice_hash h1 state == Spec.update_multi (slice_hash h0 state) seq_data))

val update_last:
  state :uint32_p {length state = v size_state} ->
  data  :uint8_p  {disjoint state data} ->
  len   :uint32_t {v len = length data /\ (length data + v len_length + 1) < 2 * v block_length} ->
  Stack unit
    (requires (fun h0 ->
      live h0 state /\ live h0 data /\
      counter h0 state < pow2 32 - 2 /\
      slice_k h0 state = Spec.k))
    (ensures  (fun h0 r h1 ->
      let seq_data = Hacl.Spec.Endianness.reveal_sbytes (as_seq h0 data) in
      let prevlen = U32.(counter h0 state * (v block_length)) in
      live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1 /\
      slice_k h1 state == Spec.k /\
      slice_hash h1 state = Spec.update_last (slice_hash h0 state) prevlen seq_data))

val finish:
  state :uint32_p{length state = v size_state} ->
  hash  :uint8_p{length hash = v hash_length /\ disjoint state hash} ->
  Stack unit
    (requires (fun h0 ->
      live h0 state /\ live h0 hash))
    (ensures  (fun h0 _ h1 ->
      let seq_hash = Hacl.Spec.Endianness.reveal_sbytes (as_seq h1 hash) in
      live h0 state /\ live h1 hash /\ modifies_1 hash h0 h1 /\
      seq_hash == Spec.finish (slice_hash h0 state)))

val hash:
  hash :uint8_p {length hash = v hash_length} ->
  input:uint8_p {length input < Spec.max_input_len_8 /\ disjoint hash input} ->
  len  :uint32_t{v len = length input} ->
  Stack unit
    (requires (fun h0 ->
      live h0 hash /\ live h0 input))
    (ensures  (fun h0 _ h1 ->
      let seq_input = Hacl.Spec.Endianness.reveal_sbytes (as_seq h0 input) in
      let seq_hash = Hacl.Spec.Endianness.reveal_sbytes (as_seq h1 hash) in
      live h0 input /\ live h0 hash /\ live h1 hash /\ modifies_1 hash h0 h1 /\
      seq_hash == Spec.hash seq_input))
