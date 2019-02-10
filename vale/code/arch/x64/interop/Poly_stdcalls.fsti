module Poly_stdcalls

open FStar.HyperStack.ST
module B = LowStar.Buffer
module BV = LowStar.BufferView
module HS = FStar.HyperStack
open FStar.Mul
open X64.Poly1305.Util
open X64.Poly1305.Math
open Poly1305.Spec_s
open Types_s
open Interop.Base
module MH = Vale.AsLowStar.MemoryHelpers

unfold
let uint8_p = B.buffer UInt8.t
unfold
let uint64 = UInt64.t

let uint64_to_nat_seq
      (b:Seq.seq UInt64.t)
    : (s:Seq.lseq nat64 (Seq.length b))
    = Seq.init (Seq.length b) (fun (i:nat{i < Seq.length b}) -> (UInt64.v (Seq.index b i) <: nat64))

[@ (CCConv "stdcall") ]
val poly1305
  (ctx_b:uint8_p)
  (inp_b:uint8_p)
  (len:uint64)
  : Stack unit
  (requires fun h ->
    B.live h ctx_b /\ B.live h inp_b /\
    B.disjoint ctx_b inp_b /\
    B.length ctx_b = 192 /\
    B.length inp_b = 8 * readable_words (UInt64.v len)
  )
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer ctx_b) h0 h1 /\
    (let key_r0 = UInt64.v (MH.low_buffer_read TUInt64 h0 ctx_b 3) in
    let key_r1 = UInt64.v (MH.low_buffer_read TUInt64 h0 ctx_b 4) in
    let key_s0 = UInt64.v (MH.low_buffer_read TUInt64 h0 ctx_b 5) in
    let key_s1 = UInt64.v (MH.low_buffer_read TUInt64 h0 ctx_b 6) in    
    let key_r = lowerUpper128_opaque key_r0 key_r1 in
    let key_s = lowerUpper128_opaque key_s0 key_s1 in

    let h0_out = UInt64.v (MH.low_buffer_read TUInt64 h1 ctx_b 0) in    
    let h1_out = UInt64.v (MH.low_buffer_read TUInt64 h1 ctx_b 1) in    
    let h = lowerUpper128_opaque h0_out h1_out in

    let inp_mem = seqTo128 (uint64_to_nat_seq (BV.as_seq h1 (BV.mk_buffer_view inp_b Views.view64))) in
    h == poly1305_hash key_r key_s inp_mem (UInt64.v len)
    )
  )
