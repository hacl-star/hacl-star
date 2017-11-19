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

open Hacl.Impl.SHA2_256


(* Definition of aliases for modules *)
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module H8 = Hacl.UInt8
module H32 = Hacl.UInt32
module H64 = Hacl.UInt64

module ST = FStar.HyperStack.ST
module Buffer = FStar.Buffer
module Cast = Hacl.Cast

module Spec = Spec.SHA2_256
module Hash = Hacl.Impl.SHA2_256


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


#reset-options "--max_fuel 0  --z3rlimit 10"

[@"c_inline"]
val alloc:
  unit ->
  StackInline (state:uint32_p{length state = v size_state})
    (requires (fun h0 -> True))
    (ensures (fun h0 st h1 -> (st `unused_in` h0) /\ live h1 st /\ modifies_0 h0 h1 /\ frameOf st == h1.tip
             /\ Map.domain h1.h == Map.domain h0.h))

let alloc () = Hash.alloc ()


#reset-options "--max_fuel 0  --z3rlimit 30"

val init:
  state:uint32_p{length state = v size_state} ->
  Stack unit
    (requires (fun h0 -> live h0 state
              /\ (let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
              let counter = Seq.index seq_counter 0 in
              H32.v counter = 0)))
    (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1
              /\ (let slice_k = Seq.slice (as_seq h1 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
              let slice_h_0 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
              let seq_counter = Seq.slice (as_seq h1 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
              let counter = Seq.index seq_counter 0 in
              let seq_k = Hacl.Spec.Endianness.reveal_h32s slice_k in
              let seq_h_0 = Hacl.Spec.Endianness.reveal_h32s slice_h_0 in
              seq_k == Spec.k /\ seq_h_0 == Spec.h_0 /\ H32.v counter = 0)))

let init state =
  Hash.init state

#reset-options "--max_fuel 0  --z3rlimit 50"

val update:
  state :uint32_p {length state = v size_state} ->
  data  :uint8_p  {length data = v size_block /\ disjoint state data} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data
                  /\ (let seq_k = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  Hacl.Spec.Endianness.reveal_h32s seq_k == Spec.k /\ H32.v counter < (pow2 32 - 1))))
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
                  /\ H32.v counter_1 = H32.v counter_0 + 1 /\ H32.v counter_1 < pow2 32
                  /\ (Hacl.Spec.Endianness.reveal_h32s seq_hash_1 == Spec.update (Hacl.Spec.Endianness.reveal_h32s seq_hash_0) (Hacl.Spec.Endianness.reveal_sbytes seq_block)))))

let update state data_8 = Hash.update state data_8


#reset-options "--max_fuel 0  --z3rlimit 100"

val update_multi:
  state :uint32_p{length state = v size_state} ->
  data  :uint8_p {length data % v size_block = 0 /\ disjoint state data} ->
  n     :uint32_t{v n * v size_block = length data} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data /\
                 (let seq_k = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  Hacl.Spec.Endianness.reveal_h32s seq_k == Spec.k /\ H32.v counter < pow2 32 - (v n))))
        (ensures  (fun h0 _ h1 -> live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1 /\
                 (let seq_hash0 = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash1 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_k0 = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_k1 = Seq.slice (as_seq h1 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_blocks = as_seq h0 data in
                  let seq_counter0 = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let seq_counter1 = Seq.slice (as_seq h1 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter0 = Seq.index seq_counter0 0 in
                  let counter1 = Seq.index seq_counter1 0 in
                  seq_k0 == seq_k1 /\
                  H32.v counter1 = H32.v counter0 + (v n) /\
                  H32.v counter1 < pow2 32 /\
                  Hacl.Spec.Endianness.reveal_h32s seq_hash1 ==
                  Spec.update_multi (Hacl.Spec.Endianness.reveal_h32s seq_hash0) (Hacl.Spec.Endianness.reveal_sbytes seq_blocks) )))

let update_multi state data n = Hash.update_multi state data n


#reset-options "--max_fuel 0  --z3rlimit 50"

val update_last:
  state :uint32_p {length state = v size_state} ->
  data  :uint8_p  {disjoint state data} ->
  len   :uint32_t {v len = length data /\ (length data + v size_len_8 + 1) < 2 * v size_block} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data
                  /\ (let seq_k = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  let nb = U32.div len size_block in
                  Hacl.Spec.Endianness.reveal_h32s seq_k == Spec.k /\ H32.v counter < (pow2 32 - 2))))
        (ensures  (fun h0 r h1 -> live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1
                  /\ (let seq_hash_0 = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash_1 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_data = Hacl.Spec.Endianness.reveal_sbytes (as_seq h0 data) in
                  let count = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.v pos_count_w + 1) in
                  let prevlen = U32.(H32.v (Seq.index count 0) * (v size_block)) in
                  (Hacl.Spec.Endianness.reveal_h32s seq_hash_1) == Spec.update_last (Hacl.Spec.Endianness.reveal_h32s seq_hash_0) prevlen seq_data)))

let update_last state data len = Hash.update_last state data len


#reset-options "--max_fuel 0  --z3rlimit 10"

val finish:
  state :uint32_p{length state = v size_state} ->
  hash  :uint8_p{length hash = v size_hash /\ disjoint state hash} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 hash))
        (ensures  (fun h0 _ h1 -> live h0 state /\ live h1 hash /\ modifies_1 hash h0 h1
                  /\ (let seq_hash_w = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash = Hacl.Spec.Endianness.reveal_sbytes (as_seq h1 hash) in
                  seq_hash = Spec.finish (Hacl.Spec.Endianness.reveal_h32s seq_hash_w))))

let finish state hash = Hash.finish state hash


#reset-options "--max_fuel 0  --z3rlimit 10"

val hash:
  hash :uint8_p {length hash = v size_hash} ->
  input:uint8_p {length input < Spec.max_input_len_8 /\ disjoint hash input} ->
  len  :uint32_t{v len = length input} ->
  Stack unit
        (requires (fun h0 -> live h0 hash /\ live h0 input))
        (ensures  (fun h0 _ h1 -> live h0 input /\ live h0 hash /\ live h1 hash /\ modifies_1 hash h0 h1
                  /\ (let seq_input = Hacl.Spec.Endianness.reveal_sbytes (as_seq h0 input) in
                  let seq_hash = Hacl.Spec.Endianness.reveal_sbytes (as_seq h1 hash) in
                  seq_hash == Spec.hash seq_input)))

let hash hash input len = Hash.hash hash input len
