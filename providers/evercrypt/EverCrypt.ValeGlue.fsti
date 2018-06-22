(** Wrappers around Vale functions; implemented in Low* and extracted using Kremlin *)
module EverCrypt.ValeGlue

open EverCrypt.Helpers
open FStar.HyperStack.ST

module U32 = FStar.UInt32
module B = LowStar.Buffer
module M = LowStar.Modifies
module HS = FStar.HyperStack

type uint8_p = B.buffer UInt8.t

///  SHA256

// JP: no clue that this is correct ...
let sha256_size_state = 137ul

type sha256_state = b:B.buffer UInt32.t { B.length b = U32.v sha256_size_state }

val sha256_slice_k: HS.mem -> sha256_state -> Seq.lseq UInt32.t 64
val sha256_slice_hash: HS.mem -> sha256_state -> Seq.lseq UInt32.t 8
val sha256_counter: HS.mem -> sha256_state -> nat

/// Incremental API
val sha256_init: state:B.buffer UInt32.t ->
  Stack unit
    (requires (fun h0 -> B.live h0 state))
    (ensures (fun h0 _ h1 -> B.live h1 state /\ M.(modifies (loc_buffer state) h0 h1)))
val sha256_update: state:sha256_state -> data:uint8_p -> Stack_ unit
val sha256_update_multi: state:sha256_state -> data:uint8_p -> n:uint32_t -> Stack_ unit
val sha256_update_last: state:sha256_state -> data:uint8_p -> n:uint32_t -> Stack_ unit
val sha256_finish: state:sha256_state -> data:uint8_p -> Stack_ unit

/// All-in one
val sha256_hash: dst:uint8_p -> data:uint8_p -> n:uint32_t -> Stack_ unit
