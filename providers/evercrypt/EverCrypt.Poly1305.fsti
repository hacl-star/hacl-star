module EverCrypt.Poly1305

/// A multiplexed frontend for Poly1305.

module B = LowStar.Buffer
module U32 = FStar.UInt32
module ST = FStar.HyperStack.ST

module BF = Arch.BufferFriend

open FStar.HyperStack.ST

(** @type: true
*)
val poly1305: dst:B.buffer UInt8.t { B.length dst = 16 } ->
  src:B.buffer UInt8.t ->
  len:U32.t { U32.v len = B.length src /\ U32.v len + 16 <= UInt.max_int 32 } ->
  key:B.buffer UInt8.t { B.length key = 32 } ->
  Stack unit
    (requires fun h ->
      B.live h src /\ B.live h dst /\ B.live h key /\
      B.disjoint dst src /\ B.disjoint dst key)
    (ensures fun h0 _ h1 ->
      B.(modifies (loc_buffer dst) h0 h1 /\ (
      B.as_seq h1 dst ==
        BF.of_bytes (Spec.Poly1305.poly1305
          (BF.to_bytes (B.as_seq h0 src))
          (BF.to_bytes (B.as_seq h0 key))))))
