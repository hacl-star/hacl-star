module Hacl.SHA2_384

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

module Spec = Spec.SHA2_384


#reset-options "--max_fuel 0  --z3rlimit 100"


(* Definition of base types *)
private let uint8_t   = FStar.UInt8.t
private let uint32_t  = FStar.UInt32.t
private let uint64_t  = FStar.UInt64.t

private let uint8_ht  = Hacl.UInt8.t
private let uint64_ht = Hacl.UInt64.t

private let uint64_p = Buffer.buffer uint64_ht
private let uint8_p  = Buffer.buffer uint8_ht


//
// SHA-384
//

(* Define word size *)
inline_for_extraction let word_length = 8ul // Size of the word in bytes

(* Define algorithm parameters *)
inline_for_extraction let state_word_length   = 8ul // 8 words (Intermediate hash output size)
inline_for_extraction let block_word_length  = 16ul  // 16 words (Working data block size)
inline_for_extraction let hash_length     = word_length *^ state_word_length
inline_for_extraction let block_length    = word_length *^ block_word_length
inline_for_extraction let hash_word_length = 6ul // 6 words (Final hash output size)
inline_for_extraction let size_hash_final   = word_length *^ hash_word_length


(* Sizes of objects in the state *)
inline_for_extraction let size_k_w     = 80ul  // 80 words of 64 bits (block_length)
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

type state = state:uint64_p {length state = v size_state}

let slice_k (h:HS.mem)
            (s:state{live h s})
   : GTot (Seq.lseq UInt64.t (U32.v size_k_w))
   = Hacl.Spec.Endianness.reveal_h64s
          (Seq.slice (as_seq h s)
                     (U32.v pos_k_w)
                     (U32.(v pos_k_w + v size_k_w)))

let slice_hash (h:HS.mem)
               (s:state{live h s})
    : GTot (Seq.lseq UInt64.t (U32.v state_word_length))
    = Hacl.Spec.Endianness.reveal_h64s
           (Seq.slice (as_seq h s)
                      (U32.v pos_whash_w)
                      (U32.(v pos_whash_w + v size_whash_w)))

let counter (h:HS.mem)
            (s:state{live h s})
    : GTot nat
    = H64.v (Seq.index (as_seq h s) (U32.v pos_count_w))

[@"c_inline"]
val alloc:
  unit ->
  StackInline state
    (requires (fun h0 -> True))
    (ensures (fun h0 st h1 ->
                ~(contains h0 st) /\
                live h1 st /\
                modifies_0 h0 h1 /\
                frameOf st == (HS.get_tip h1) /\
                Map.domain (HS.get_hmap h1) == Map.domain (HS.get_hmap h0)))

val init:
  state:state ->
  Stack unit
        (requires (fun h0 -> live h0 state))
        (ensures  (fun h0 r h1 ->
                     live h1 state /\
                     modifies_1 state h0 h1 /\
                     slice_k h1 state == Spec.k /\
                     slice_hash h1 state == Spec.h_0 /\
                     counter h1 state == 0))

val update:
  state :state ->
  data  :uint8_p  {length data = v block_length /\ disjoint state data} ->
  Stack unit
        (requires (fun h0 ->
                     live h0 state /\
                     live h0 data  /\
                     slice_k h0 state == Spec.k /\
                     counter h0 state < pow2 64 - 1))
        (ensures  (fun h0 r h1 ->
                     let seq_block = Hacl.Spec.Endianness.reveal_sbytes (as_seq h0 data) in
                     live h1 state /\
                     modifies_1 state h0 h1 /\
                     slice_k h0 state == slice_k h1 state /\
                     counter h1 state == counter h0 state + 1 /\
                     slice_hash h1 state == Spec.update (slice_hash h0 state) seq_block))

val update_multi:
  state :state ->
  data  :uint8_p {length data % v block_length = 0 /\ disjoint state data} ->
  n     :uint32_t{v n * v block_length = length data} ->
  Stack unit
        (requires (fun h0 ->
                     live h0 state /\
                     live h0 data /\
                     slice_k h0 state == Spec.k /\
                     counter h0 state < pow2 64 - v n))
        (ensures  (fun h0 _ h1 ->
                     let seq_block = Hacl.Spec.Endianness.reveal_sbytes (as_seq h0 data) in
                     live h1 state /\
                     modifies_1 state h0 h1 /\
                     slice_k h0 state == slice_k h1 state /\
                     counter h1 state == counter h0 state + v n /\
                     slice_hash h1 state == Spec.update_multi (slice_hash h0 state) seq_block))

val update_last:
  state :state ->
  data  :uint8_p  {disjoint state data} ->
  len   :uint32_t {v len = length data /\ (length data + v len_length + 1) < 2 * v block_length} ->
  Stack unit
        (requires (fun h0 ->
                     live h0 state /\
                     live h0 data /\
                     slice_k h0 state == Spec.k /\
                     counter h0 state < pow2 64 - 2))
        (ensures  (fun h0 r h1 ->
                     let seq_block = Hacl.Spec.Endianness.reveal_sbytes (as_seq h0 data) in
                     let prevlen = FStar.Mul.(counter h0 state * U32.v block_length) in
                     live h1 state /\
                     modifies_1 state h0 h1 /\
                     slice_k h1 state == Spec.k /\
                     slice_hash h1 state == Spec.update_last (slice_hash h0 state) prevlen seq_block))

val finish:
  state :state ->
  hash  :uint8_p{length hash = v size_hash_final /\ disjoint state hash} ->
  Stack unit
        (requires (fun h0 ->
                     live h0 state /\
                     live h0 hash))
        (ensures  (fun h0 _ h1 ->
                     let seq_hash = Hacl.Spec.Endianness.reveal_sbytes (as_seq h1 hash) in
                     live h1 state /\
                     live h1 hash /\
                     modifies_1 hash h0 h1 /\
                     seq_hash == Spec.finish (slice_hash h0 state)))

val hash:
  hash :uint8_p {length hash = v size_hash_final} ->
  input:uint8_p {length input < Spec.max_input_len_8 /\ disjoint hash input} ->
  len  :uint32_t{v len = length input} ->
  Stack unit
        (requires (fun h0 ->
                     live h0 hash /\
                     live h0 input))
        (ensures  (fun h0 _ h1 ->
                     let seq_input = Hacl.Spec.Endianness.reveal_sbytes (as_seq h0 input) in
                     let seq_hash = Hacl.Spec.Endianness.reveal_sbytes (as_seq h1 hash) in
                     live h1 hash /\
                     modifies_1 hash h0 h1 /\
                     seq_hash == Spec.hash seq_input))
