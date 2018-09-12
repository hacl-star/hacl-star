module Hacl.Hash

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST

include Hacl.Hash.Common
open Spec.Hash.Common
open Spec.Hash.Helpers
open FStar.Mul

include Hacl.SHA2

inline_for_extraction
let blocks_t (a: hash_alg) =
  b:B.buffer U8.t { B.length b % size_block a = 0 }

// Generic stateful type for update, for any hash_alg.
inline_for_extraction
let update_st (a:hash_alg) =
  s:state a ->
  block:B.buffer U8.t { B.length block = size_block a } ->
  ST.Stack unit
    (requires (fun h ->
      B.live h s /\ B.live h block /\ B.disjoint s block))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer s) h0 h1) /\
      B.as_seq h1 s == Spec.Hash.update a (B.as_seq h0 s) (B.as_seq h0 block)))

// Note: we cannot take more than 4GB of data because we are currently
// constrained by the size of buffers...
inline_for_extraction
let update_multi_st (a: hash_alg) =
  s:state a ->
  blocks:blocks_t a ->
  n:U32.t { B.length blocks = size_block a * U32.v n } ->
  ST.Stack unit
    (requires (fun h ->
      B.live h s /\ B.live h blocks /\ B.disjoint s blocks))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer s) h0 h1) /\
      Seq.equal (B.as_seq h1 s)
        (Spec.Hash.update_multi a (B.as_seq h0 s) (B.as_seq h0 blocks))))

noextract
val mk_update_multi: a:hash_alg -> update:update_st a -> update_multi_st a

val update_multi_sha2_224: update_multi_st SHA2_224
val update_multi_sha2_256: update_multi_st SHA2_256
val update_multi_sha2_384: update_multi_st SHA2_384
val update_multi_sha2_512: update_multi_st SHA2_512
