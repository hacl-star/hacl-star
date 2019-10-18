module Vale.Wrapper.X64.Sha

open Vale.X64.CPU_Features_s
open FStar.HyperStack.ST
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module BV = LowStar.BufferView
module HS = FStar.HyperStack
module BF = Vale.Arch.BufferFriend
open FStar.Mul
open Vale.SHA.SHA_helpers
open Lib.IntTypes

unfold
let uint32_p = B.buffer uint32
unfold
let uint32_i = IB.ibuffer uint32
unfold
let uint8_p = B.buffer uint8
unfold
let uint64 = uint_t U64 PUB

inline_for_extraction
val sha256_update
  (ctx_b:uint32_p)
  (in_b:uint8_p)
  (num_val:uint64)
  (k_b:uint32_i)
  : Stack unit
  (requires fun h ->
    sha_enabled /\
    B.live h ctx_b /\ B.live h in_b /\ B.live h k_b /\
    B.length k_b == 64 /\ B.length ctx_b == 8 /\
    B.length in_b = 64 * (UInt64.v num_val) /\
    B.disjoint ctx_b in_b /\
    B.disjoint ctx_b k_b /\
    B.disjoint in_b k_b /\
    Seq.equal (B.as_seq h k_b) (Spec.SHA2.Constants.k224_256)
  )
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer ctx_b) h0 h1 /\
    Seq.length (B.as_seq h0 in_b) % block_length == 0 /\
   (reveal_word();
    Seq.equal
      (B.as_seq h1 ctx_b)
      (update_multi_transparent (B.as_seq h0 ctx_b) (BF.of_bytes (B.as_seq h0 in_b))))
  )
