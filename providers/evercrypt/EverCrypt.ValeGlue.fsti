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

// FIXME
let sha256_slice_k (h:HS.mem) (s: sha256_state): GTot (Seq.lseq UInt32.t 64) =
  Seq.create 64 0ul
let sha256_slice_hash (h:HS.mem) (s: sha256_state): GTot (Seq.lseq UInt32.t 8) =
  Seq.create 8 0ul
let sha256_counter (h: HS.mem) (s: sha256_state) =
  0

/// Incremental API
val sha256_init: state:B.buffer UInt32.t ->
  Stack unit
    (requires (fun h0 -> B.live h0 state))
    (ensures (fun h0 _ h1 -> B.live h1 state /\ M.(modifies (loc_buffer state) h0 h1)))

val sha256_update: state:sha256_state -> data:uint8_p ->
  Stack unit
    (requires (fun h0 -> B.live h0 state /\ B.live h0 data))
    (ensures (fun h0 _ h1 -> B.live h1 state /\ M.(modifies (loc_buffer state) h0 h1)))

val sha256_update_multi: state:sha256_state -> data:uint8_p -> n:uint32_t ->
  Stack unit
    (requires (fun h0 -> B.live h0 state /\ B.live h0 data))
    (ensures (fun h0 _ h1 -> B.live h1 state /\ M.(modifies (loc_buffer state) h0 h1)))

val sha256_update_last: state:sha256_state -> data:uint8_p -> n:uint32_t ->
  Stack unit
    (requires (fun h0 -> B.live h0 state /\ B.live h0 data))
    (ensures (fun h0 _ h1 -> B.live h1 state /\ M.(modifies (loc_buffer state) h0 h1)))

val sha256_finish: state:sha256_state -> hash:uint8_p ->
  Stack unit
    (requires (fun h0 -> B.live h0 state /\ B.live h0 hash))
    (ensures (fun h0 _ h1 -> B.live h1 state /\ M.(modifies (loc_buffer hash) h0 h1)))

/// All-in one
val sha256_hash: dst:uint8_p -> data:uint8_p -> n:uint32_t ->
  Stack unit
    (requires (fun h0 -> B.live h0 dst /\ B.live h0 data))
    (ensures (fun h0 _ h1 -> B.live h1 dst /\ M.(modifies (loc_buffer dst) h0 h1)))
