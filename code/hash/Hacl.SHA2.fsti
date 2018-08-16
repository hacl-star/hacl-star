module Hacl.SHA2

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module S = FStar.Seq
module B = LowStar.Buffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module M = LowStar.Modifies

module Spec = Spec.SHA2

open Spec.Hash.Helpers

val static_fp: M.loc

let word (a: sha2_alg) =
  match a with
  | SHA2_224 | SHA2_256 -> U32.t
  | SHA2_384 | SHA2_512 -> U64.t

type state (a: sha2_alg) =
  b:B.buffer (word a) { B.length b = size_hash_w a }

let alloca_t (a: sha2_alg) = unit -> ST.StackInline (state a)
  (requires (fun h ->
    HS.is_stack_region (HS.get_tip h)))
  (ensures (fun h0 s h1 ->
    M.(modifies M.loc_none h0 h1) /\
    B.live h1 s /\
    B.as_seq h1 s = Spec.init a))

val alloca: a:sha2_alg -> alloca_t a

let init_t (a:sha2_alg) = (s: state a) -> ST.Stack unit
  (requires (fun h ->
    M.loc_disjoint (B.loc_addr_of_buffer s) static_fp /\
    B.live h s))
  (ensures (fun h0 _ h1 ->
    M.(modifies (loc_buffer s) h0 h1) /\
    B.as_seq h1 s = Spec.init a))

val init: a:sha2_alg -> init_t a
