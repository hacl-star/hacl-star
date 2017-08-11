module SHA2_384

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer

open Hacl.Cast
open Hacl.UInt8
open Hacl.UInt32
open FStar.UInt32

open Hacl.Hash.SHA2_384


(* Definition of aliases for modules *)
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module H8 = Hacl.UInt8
module H32 = Hacl.UInt32
module H64 = Hacl.UInt64

module Buffer = FStar.Buffer
module Cast = Hacl.Cast

module Spec = Spec.SHA2_384
module Hash = Hacl.Hash.SHA2_384


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

(* Define algorithm parameters *)
inline_for_extraction let size_hash = Hash.size_hash_final
inline_for_extraction let size_block = Hash.size_block
inline_for_extraction let size_state = Hash.size_state


#reset-options "--max_fuel 0  --z3rlimit 10"

[@"c_inline"]
val alloc:
  unit ->
  StackInline (state:uint64_p{length state = v size_state})
    (requires (fun h0 -> True))
    (ensures (fun h0 st h1 -> ~(contains h0 st) /\ live h1 st /\ modifies_0 h0 h1 /\ frameOf st == h1.tip
             /\ Map.domain h1.h == Map.domain h0.h))

let alloc () = Hash.alloc ()


#reset-options "--max_fuel 0  --z3rlimit 30"

val init:
  state:uint64_p{length state = v size_state} ->
  Stack unit
    (requires (fun h0 -> live h0 state
              /\ (let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
              let counter = Seq.index seq_counter 0 in
              H64.v counter = 0)))
    (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1
              /\ (let slice_k = Seq.slice (as_seq h1 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
              let slice_h_0 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
              let seq_counter = Seq.slice (as_seq h1 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
              let counter = Seq.index seq_counter 0 in
              let seq_k = Hacl.Spec.Endianness.reveal_h64s slice_k in
              let seq_h_0 = Hacl.Spec.Endianness.reveal_h64s slice_h_0 in
              seq_k == Spec.k /\ seq_h_0 == Spec.h_0 /\ H64.v counter = 0)))

let init state = Hash.init state


#reset-options "--max_fuel 0  --z3rlimit 50"

val update:
  state :uint64_p {length state = v size_state} ->
  data  :uint8_p  {length data = v size_block /\ disjoint state data} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data
                  /\ (let seq_k = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  seq_k == Spec.k /\ H64.v counter < (pow2 32 - 1))))
        (ensures  (fun h0 r h1 -> live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1
                  /\ (let seq_hash_0 = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash_1 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_k_0 = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_k_1 = Seq.slice (as_seq h1 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_block = as_seq h0 data in
                  let seq_counter_0 = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let seq_counter_1 = Seq.slice (as_seq h1 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter_0 = Seq.index seq_counter_0 0 in
                  let counter_1 = Seq.index seq_counter_1 0 in
                  seq_k_0 == seq_k_1
                  /\ H64.v counter_1 = H64.v counter_0 + 1 /\ H64.v counter_1 < pow2 32
                  /\ seq_hash_1 == Spec.update seq_hash_0 seq_block)))

let update state data_8 = Hash.update state data_8


#reset-options "--max_fuel 0  --z3rlimit 100"

val update_multi:
  state :uint64_p{length state = v size_state} ->
  data  :uint8_p {length data % v size_block = 0 /\ disjoint state data} ->
  n     :uint32_t{v n * v size_block = length data} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data
                  /\ (let seq_k = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  seq_k == Spec.k /\ H64.v counter < (pow2 32 - (v n)))))
        (ensures  (fun h0 _ h1 -> live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1
                  /\ (let seq_hash_0 = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash_1 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_k_0 = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_k_1 = Seq.slice (as_seq h1 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_blocks = as_seq h0 data in
                  let seq_counter_0 = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let seq_counter_1 = Seq.slice (as_seq h1 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter_0 = Seq.index seq_counter_0 0 in
                  let counter_1 = Seq.index seq_counter_1 0 in
                  seq_k_0 == seq_k_1
                  /\ H64.v counter_1 = H64.v counter_0 + (v n) /\ H64.v counter_1 < pow2 32
                  /\ seq_hash_1 == Spec.update_multi seq_hash_0 seq_blocks)))

let update_multi state data n = Hash.update_multi state data n


#reset-options "--max_fuel 0  --z3rlimit 50"

val update_last:
  state :uint64_p {length state = v size_state} ->
  data  :uint8_p  {disjoint state data} ->
  len   :uint64_t {U64.v len = length data /\ (length data + v size_len_8 + 1) < 2 * v size_block} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data
                  /\ (let seq_k = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  let nb = U64.div len (u32_to_u64 size_block) in
                  seq_k == Spec.k /\ H64.v counter < (pow2 32 - 2))))
        (ensures  (fun h0 r h1 -> live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1
                  /\ (let seq_hash_0 = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash_1 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_data = as_seq h0 data in
                  let count = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.v pos_count_w + 1) in
                  let prevlen = U32.(H64.v (Seq.index count 0) * (v size_block)) in
                  seq_hash_1 == Spec.update_last seq_hash_0 prevlen seq_data)))

let update_last state data len = Hash.update_last state data len


#reset-options "--max_fuel 0  --z3rlimit 10"

val finish:
  state :uint64_p{length state = v size_state} ->
  hash  :uint8_p{length hash = v size_hash} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 hash))
        (ensures  (fun h0 _ h1 -> live h0 state /\ live h1 hash /\ modifies_1 hash h0 h1
                  /\ (let seq_hash_w = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash = as_seq h1 hash in
                  seq_hash = Spec.finish seq_hash_w)))

let finish state hash = Hash.finish state hash


#reset-options "--max_fuel 0  --z3rlimit 10"

val hash:
  hash :uint8_p {length hash = v size_hash} ->
  input:uint8_p {length input < Spec.max_input_len_8} ->
  len  :uint32_t{v len = length input} ->
  Stack unit
        (requires (fun h0 -> live h0 hash /\ live h0 input))
        (ensures  (fun h0 _ h1 -> live h0 input /\ live h0 hash /\ live h1 hash /\ modifies_1 hash h0 h1
                  /\ (let seq_input = as_seq h0 input in
                  let seq_hash = as_seq h1 hash in
                  seq_hash == Spec.hash seq_input)))

let hash hash input len = Hash.hash hash input len
