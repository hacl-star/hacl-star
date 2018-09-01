module Hacl.MD5

include Hacl.Hash.Common
open Spec.Hash.Helpers

module U8 = FStar.UInt8
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Spec = Spec.MD5

val alloca: unit -> HST.StackInline (state MD5)
  (requires (fun h ->
    HS.is_stack_region (HS.get_tip h)))
  (ensures (fun h0 s h1 ->
    B.(modifies B.loc_none h0 h1) /\
    B.live h1 s /\
    B.as_seq h1 s = Spec.init))

val static_fp: unit -> GTot B.loc

let loc_in (l: B.loc) (h: HS.mem) =
  B.(loc_not_unused_in h `loc_includes` l)

(* A useful lemma for clients, to be called at any time before performing an
   allocation, hence giving them "for free" that their allocation is disjoint from
   our top-level arrays. *)
val recall_static_fp: unit -> HST.Stack unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 ->
    B.(modifies loc_none h0 h1) /\
    static_fp () `loc_in` h1))

val init (s: state MD5) : HST.Stack unit
  (requires (fun h ->
    B.loc_disjoint (B.loc_addr_of_buffer s) (static_fp ()) /\
    B.live h s))
  (ensures (fun h0 _ h1 ->
    B.(modifies (loc_buffer s) h0 h1) /\
    Seq.equal (B.as_seq h1 s) Spec.init))

val update
  (s:state MD5)
  (block:B.buffer U8.t { B.length block = size_block MD5 })
: HST.Stack unit
    (requires (fun h ->
      B.loc_disjoint (B.loc_union (B.loc_buffer s) (B.loc_buffer block)) (static_fp ()) /\
      B.live h s /\ B.live h block /\ B.disjoint s block))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer s) h0 h1) /\
      B.live h1 s /\
      B.as_seq h1 s == Spec.update (B.as_seq h0 s) (B.as_seq h0 block)))
