module Hacl.Hash.Incremental

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128
module B = LowStar.Buffer
module S = FStar.Seq
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module Tactics = FStar.Tactics
module Lemmas = FStar.Math.Lemmas

module Common = Spec.Hash.Common

open Hacl.Hash.Common
open Hacl.Hash.Lemmas
open Spec.Hash.Helpers
open Spec.Hash.Incremental
open FStar.Mul

inline_for_extraction
let update_last_st (a: hash_alg) =
  s:state a ->
  prev_len:len_t a { len_v a prev_len % size_block a = 0 } ->
  input:B.buffer U8.t { B.length input + len_v a prev_len < max_input8 a } ->
  input_len:U32.t { B.length input = U32.v input_len } ->
  ST.Stack unit
    (requires (fun h ->
      B.live h s /\ B.live h input /\ B.disjoint s input))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer s) h0 h1) /\
      Seq.equal (B.as_seq h1 s)
        (update_last a (B.as_seq h0 s) (len_v a prev_len) (B.as_seq h0 input))))

val update_last_sha2_224: update_last_st SHA2_224
val update_last_sha2_256: update_last_st SHA2_256
val update_last_sha2_384: update_last_st SHA2_384
val update_last_sha2_512: update_last_st SHA2_512
// val update_last_sha1: update_last_st SHA1
// val update_last_md5: update_last_st MD5
