module SHA2_512

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.ST
open FStar.Buffer

open Hacl.Cast
open Hacl.UInt8
open Hacl.UInt32
open FStar.UInt32


(* Definition of aliases for modules *)
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

module S8 = Hacl.UInt8
module S32 = Hacl.UInt32
module S64 = Hacl.UInt64

module Buffer = FStar.Buffer
module Cast = Hacl.Cast


(* Definition of base types *)
private let uint8_t   = FStar.UInt8.t
private let uint32_t  = FStar.UInt32.t
private let uint64_t  = FStar.UInt64.t

private let suint8_t  = Hacl.UInt8.t
private let suint32_t = Hacl.UInt32.t
private let suint64_t = Hacl.UInt64.t

private let uint64_p = Buffer.buffer uint64_t
private let suint8_p  = Buffer.buffer suint8_t



//
// SHA-512
//

(* Define algorithm parameters *)
let hash_hashsize_512 = Hacl.Hash.SHA2.L512.size_hash
let hash_blocksize_512 = Hacl.Hash.SHA2.L512.size_block
let hash_size_state_512 = Hacl.Hash.SHA2.L512.size_state



val sha2_alloc_512:
  unit ->
  StackInline (state:uint64_p{length state = v hash_size_state_512})
        (requires (fun h0 -> True))
        (ensures  (fun h0 state h1 -> modifies_0 h0 h1 /\ live h1 state))

let sha2_alloc_512 () = Hacl.Hash.SHA2.L512.alloc ()


val sha2_init_512:
  (state:uint64_p{length state = v hash_size_state_512}) ->
  Stack unit
        (requires (fun h0 -> live h0 state))
        (ensures  (fun h0 r h1 -> modifies_1 state h0 h1))
let sha2_init_512 state = Hacl.Hash.SHA2.L512.init state



val sha2_update_512:
  state:uint64_p{length state = v hash_size_state_512} ->
  data :suint8_p {length data = v hash_blocksize_512} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data))
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))
let sha2_update_512 state data_8 = Hacl.Hash.SHA2.L512.update state data_8



val sha2_update_multi_512:
  state :uint64_p{length state = v hash_size_state_512} ->
  data  :suint8_p ->
  n     :uint32_t{v n * v hash_blocksize_512 <= length data} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data))
        (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))

let sha2_update_multi_512 state data n = Hacl.Hash.SHA2.L512.update_multi state data n



val sha2_update_last_512:
  state :uint64_p{length state = v hash_size_state_512} ->
  data  :suint8_p {length data <= v hash_blocksize_512} ->
  len   :uint32_t {U32.v len = length data} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data))
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

let sha2_update_last_512 state data len = Hacl.Hash.SHA2.L512.update_last state data len



val sha2_finish_512:
  state :uint64_p{length state = v hash_size_state_512} ->
  hash  :suint8_p{length hash = v hash_hashsize_512} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 hash))
        (ensures  (fun h0 _ h1 -> live h1 hash /\ modifies_1 hash h0 h1))

let sha2_finish_512 state hash = Hacl.Hash.SHA2.L512.finish state hash



val sha2_512:
  hash :suint8_p{length hash = v hash_hashsize_512} ->
  input:suint8_p ->
  len  :uint32_t{v len = length input} ->
  Stack unit
        (requires (fun h0 -> live h0 hash /\ live h0 input))
        (ensures  (fun h0 _ h1 -> live h1 hash /\ modifies_1 hash h0 h1))

let sha2_512 hash input len = Hacl.Hash.SHA2.L512.hash hash input len
