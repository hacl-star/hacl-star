module EverCrypt.Poly1305

/// A multiplexed frontend for Poly1305.

module B = LowStar.Buffer
module U32 = FStar.UInt32

module BF = Vale.Arch.BufferFriend

open FStar.HyperStack.ST

[@@ Comment "Compute the Poly1305 MAC of a message.

@param output Pointer to 16 bytes of memory where the MAC is written to.
@param input Pointer to `input_len` bytes of memory where the message is read from.
@param input_len Length of the message.
@param key Pointer to 32 bytes of memory where the key is read from."]
(** @type: true
*)
val mac: output:B.buffer UInt8.t { B.length output = 16 } ->
  input:B.buffer UInt8.t ->
  input_len:U32.t { U32.v input_len = B.length input /\ U32.v input_len + 16 <= UInt.max_int 32 } ->
  key:B.buffer UInt8.t { B.length key = 32 } ->
  Stack unit
    (requires fun h ->
      B.live h input /\ B.live h output /\ B.live h key /\
      B.disjoint output input /\ B.disjoint output key)
    (ensures fun h0 _ h1 ->
      B.(modifies (loc_buffer output) h0 h1 /\ (
      B.as_seq h1 output ==
        BF.of_bytes (Spec.Poly1305.poly1305_mac
          (BF.to_bytes (B.as_seq h0 input))
          (BF.to_bytes (B.as_seq h0 key))))))
