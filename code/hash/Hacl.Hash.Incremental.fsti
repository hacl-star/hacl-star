module Hacl.Hash.Incremental

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module S = FStar.Seq
module B = LowStar.Buffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module M = LowStar.Modifies

module Spec = Spec.Hash

(** Lifting words, state and abstract predicates in the stateful style. *)

let word a =
  let open Spec in
  match a with
  | SHA2_224 | SHA2_256 -> U32.t
  | SHA2_384 | SHA2_512 -> U64.t

type state a =
  b:B.buffer (word a) { B.length b = Spec.size_hash_w }

val hashes: a:Spec.hash_alg ->
  (s: S.seq (word a) { S.length s = Spec.size_hash_w }) ->
  (l:Spec.bytes_blocks a) ->
  Type0

let alloca_t (a: Spec.hash_alg) = unit -> ST.StackInline (state a)
  (requires (fun h ->
    HS.is_stack_region (HS.get_tip h)))
  (ensures (fun h0 s h1 ->
    M.(modifies M.loc_none h0 h1) /\
    B.live h1 s /\
    hashes a (B.as_seq h1 s) S.empty))

val alloca: a:Spec.hash_alg -> alloca_t a

let init_t (a:Spec.hash_alg) = (s: state a) -> ST.Stack unit
  (requires (fun h ->
    B.live h s))
  (ensures (fun h0 _ h1 ->
    M.(modifies (loc_buffer s) h0 h1) /\
    hashes a (B.as_seq h1 s) S.empty))

val init: a:Spec.hash_alg -> init_t a
