module Hacl.SHA2

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module S = FStar.Seq
module B = LowStar.Buffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module M = LowStar.Modifies

module Spec = Spec.SHA2

open Spec.Hash.Helpers

(** This module uses top-level arrays behind an abstract footprint *)

val static_fp: unit -> GTot M.loc

(* A useful lemma for clients, to be called at any time before performing an
   allocation, hence giving them "for free" that their allocation is disjoint from
   our top-level arrays. *)
val recall_static_fp: unit -> ST.Stack unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 ->
    M.(modifies loc_none h0 h1) /\
    static_fp () `loc_in` h1))


(** We need to reveal the definition of the internal state for clients to use it *)

let word (a: sha2_alg) =
  match a with
  | SHA2_224 | SHA2_256 -> U32.t
  | SHA2_384 | SHA2_512 -> U64.t

type state (a: sha2_alg) =
  b:B.buffer (word a) { B.length b = size_hash_w a }


(** A series of functions; we only expose the monomorphic variants, and leave it
  * up to EverCrypt.Hash to perform multiplexing. *)

inline_for_extraction
let alloca_t (a: sha2_alg) = unit -> ST.StackInline (state a)
  (requires (fun h ->
    HS.is_stack_region (HS.get_tip h)))
  (ensures (fun h0 s h1 ->
    M.(modifies M.loc_none h0 h1) /\
    B.live h1 s /\
    B.as_seq h1 s = Spec.init a))

val alloca_224: alloca_t SHA2_224
val alloca_256: alloca_t SHA2_256
val alloca_384: alloca_t SHA2_384
val alloca_512: alloca_t SHA2_512

inline_for_extraction
let init_t (a:sha2_alg) = s:state a -> ST.Stack unit
  (requires (fun h ->
    M.loc_disjoint (B.loc_addr_of_buffer s) (static_fp ()) /\
    B.live h s))
  (ensures (fun h0 _ h1 ->
    M.(modifies (loc_buffer s) h0 h1) /\
    Seq.equal (B.as_seq h1 s) (Spec.init a)))

val init_224: init_t SHA2_224
val init_256: init_t SHA2_256
val init_384: init_t SHA2_384
val init_512: init_t SHA2_512

inline_for_extraction
let update_t (a:sha2_alg) =
  s:state a ->
  block:B.buffer U8.t { B.length block = size_block a } ->
  ST.Stack unit
    (requires (fun h ->
      B.live h s /\ B.live h block /\ B.disjoint s block))
    (ensures (fun h0 _ h1 ->
      M.(modifies (loc_buffer s) h0 h1) /\
      B.as_seq h1 s == Spec.update a (B.as_seq h0 s) (B.as_seq h0 block)))

val update_224: update_t SHA2_224
val update_256: update_t SHA2_256
val update_384: update_t SHA2_384
val update_512: update_t SHA2_512

inline_for_extraction
let pad_t (a: sha2_alg) = len:len_t a -> dst:B.buffer U8.t ->
  ST.Stack unit
    (requires (fun h ->
      len_v a len < max_input8 a /\
      B.live h dst /\
      B.length dst = pad_length a (len_v a len)))
    (ensures (fun h0 _ h1 ->
      M.(modifies (loc_buffer dst) h0 h1) /\
      B.as_seq h1 dst == Spec.pad a (len_v a len)))

val pad_224: pad_t SHA2_224
val pad_256: pad_t SHA2_256
val pad_384: pad_t SHA2_384
val pad_512: pad_t SHA2_512
