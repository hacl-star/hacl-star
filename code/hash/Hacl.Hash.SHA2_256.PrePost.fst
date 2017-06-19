module Hacl.Hash.SHA2_256.PrePost

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.ST
open FStar.Buffer

open Hacl.Cast
open Hacl.UInt8
open Hacl.UInt32
open FStar.UInt32

open Hacl.Hash.SHA2_256


(* Definition of aliases for modules *)
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module H8 = Hacl.UInt8
module H32 = Hacl.UInt32
module H64 = Hacl.UInt64

module Buffer = FStar.Buffer
module Cast = Hacl.Cast

module Spec = Spec.SHA2_256
module Hash = Hacl.Hash.SHA2_256


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

(* Define algorithm parameters *)
let size_hash = Hash.size_hash
let size_block = Hash.size_block
let size_state = Hash.size_state


let alloc_pre = True
let alloc_post h0 st h1 = ~(contains h0 st) /\ live h1 st /\ modifies_0 h0 h1 /\ frameOf st == h1.tip /\ Map.domain h1.h == Map.domain h0.h


let init_pre h0 state = live h0 state
              /\ (let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
              let counter = Seq.index seq_counter 0 in
              H32.v counter = 0)

let init_post h0 r h1 state = live h1 state /\ modifies_1 state h0 h1
              /\ (let slice_k = Seq.slice (as_seq h1 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
              let slice_h_0 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
              let seq_counter = Seq.slice (as_seq h1 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
              let counter = Seq.index seq_counter 0 in
              let seq_k = Hacl.Spec.Endianness.reveal_h32s slice_k in
              let seq_h_0 = Hacl.Spec.Endianness.reveal_h32s slice_h_0 in
              seq_k == Spec.k /\ seq_h_0 == Spec.h_0 /\ H32.v counter = 0)


let update_pre h0 state data = live h0 state /\ live h0 data
                  /\ (let seq_k = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  seq_k == Spec.k /\ H32.v counter < (pow2 32 - 1))

let update_post h0 r h1 state data = live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1
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
                  /\ H32.v counter_1 = H32.v counter_0 + 1 /\ H32.v counter_1 < pow2 32
                  /\ seq_hash_1 == Spec.update seq_hash_0 seq_block)

let update_last_pre h0 state data len = live h0 state /\ live h0 data
                  /\ (let seq_k = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  let nb = U32.div len size_block in
                  seq_k == Spec.k /\ H32.v counter < (pow2 32 - 2))

let update_last_post h0 r h1 state data len = live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1
                  /\ (let seq_hash_0 = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash_1 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_data = as_seq h0 data in
                  let count = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.v pos_count_w + 1) in
                  let prevlen = U32.(v (Seq.index count 0) * (v size_block)) in
                  seq_hash_1 == Spec.update_last seq_hash_0 prevlen seq_data)

let finish_pre h0 state hash =  live h0 state /\ live h0 hash


let finish_post h0 r h1 state hash = live h0 state /\ live h1 hash /\ modifies_1 hash h0 h1
                  /\ (let seq_hash_w = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash = as_seq h1 hash in
                  seq_hash = Spec.finish seq_hash_w)


val alloc:
  unit ->
  StackInline (state:uint32_p{length state = v size_state})
    (requires (fun h0 -> True))
    (ensures (fun h0 st h1 -> alloc_post h0 st h1))


val init:
  state:uint32_p{length state = v size_state} ->
  Stack unit
    (requires (fun h0 -> init_pre h0 state))
    (ensures  (fun h0 r h1 -> init_post h0 r h1 state))

val update:
  state :uint32_p {length state = v size_state} ->
  data  :uint8_p  {length data = v size_block /\ disjoint state data} ->
  Stack unit
        (requires (fun h0 -> update_pre h0 state data))
        (ensures  (fun h0 r h1 -> update_post h0 r h1 state data))

val update_last:
  state :uint32_p {length state = v size_state} ->
  data  :uint8_p  {disjoint state data} ->
  len   :uint32_t {v len = length data /\ (length data + v size_len_8 + 1) < 2 * v size_block} ->
  Stack unit
        (requires (fun h0 -> update_last_pre h0 state data len))
        (ensures  (fun h0 r h1 -> update_last_post h0 r h1 state data len))

val finish:
  state :uint32_p{length state = v size_state} ->
  hash  :uint8_p{length hash = v size_hash} ->
  Stack unit
        (requires (fun h0 -> finish_pre h0 state hash))
        (ensures  (fun h0 r h1 -> finish_post h0 r h1 state hash))

