module SHA2_256

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

private let suint32_p = Buffer.buffer suint32_t
private let suint8_p  = Buffer.buffer suint8_t



//
// SHA-256
//

(* Define algorithm parameters *)
let hashsize_256 = Hacl.Hash.SHA2.L256.hashsize
let blocksize_256 = Hacl.Hash.SHA2.L256.blocksize
let size_state_256 = Hacl.Hash.SHA2.L256.size_state



val sha2_alloc_256:
  unit ->
  StackInline (state:suint32_p{length state = v size_state_256})
        (requires (fun h0 -> True))
        (ensures  (fun h0 state h1 -> modifies_0 h0 h1 /\ live h1 state))

let sha2_alloc_256 () = Hacl.Hash.SHA2.L256.alloc ()


val sha2_init_256:
  (state:suint32_p{length state = v size_state_256}) ->
  Stack unit
        (requires (fun h0 -> live h0 state))
        (ensures  (fun h0 r h1 -> modifies_1 state h0 h1))
let sha2_init_256 state = Hacl.Hash.SHA2.L256.init state



val sha2_update_256:
  state:suint32_p{length state = v size_state_256} ->
  data :suint8_p {length data = v blocksize_256} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data))
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))
let sha2_update_256 state data_8 = Hacl.Hash.SHA2.L256.update state data_8



val sha2_update_multi_256:
  state :suint32_p{length state = v size_state_256} ->
  data  :suint8_p ->
  n     :uint32_t{v n * v blocksize_256 <= length data} ->
  idx   :uint32_t{v idx <= v n} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data))
        (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))

let sha2_update_multi_256 state data n idx = Hacl.Hash.SHA2.L256.update_multi state data n idx



val sha2_update_last_256:
  state :suint32_p{length state = v size_state_256} ->
  data  :suint8_p {length data <= v blocksize_256} ->
  len   :uint32_t {U32.v len = length data} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data))
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

let sha2_update_last_256 state data len = Hacl.Hash.SHA2.L256.update_last state data len



val sha2_finish_256:
  state :suint32_p{length state = v size_state_256} ->
  hash  :suint8_p{length hash = v hashsize_256} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 hash))
        (ensures  (fun h0 _ h1 -> live h1 hash /\ modifies_1 hash h0 h1))

let sha2_finish_256 state hash = Hacl.Hash.SHA2.L256.finish state hash



val sha2_256:
  hash :suint8_p{length hash = v hashsize_256} ->
  input:suint8_p ->
  len  :uint32_t{v len = length input} ->
  Stack unit
        (requires (fun h0 -> live h0 hash /\ live h0 input))
        (ensures  (fun h0 _ h1 -> live h1 hash /\ modifies_1 hash h0 h1))

let sha2_256 hash input len = Hacl.Hash.SHA2.L256.hash hash input len
