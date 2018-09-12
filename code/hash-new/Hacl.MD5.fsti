module Hacl.MD5

open Spec.Hash.Helpers
include Hacl.Hash.Common // must come last, for update_t

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

val init (s: state MD5) : HST.Stack unit
  (requires (fun h ->
    B.live h s))
  (ensures (fun h0 _ h1 ->
    B.(modifies (loc_buffer s) h0 h1) /\
    Seq.equal (B.as_seq h1 s) Spec.init))

val update: update_st MD5

val pad: pad_st MD5
