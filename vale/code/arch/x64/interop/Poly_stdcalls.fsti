module Poly_stdcalls

open FStar.HyperStack.ST
module B = LowStar.Buffer
module DV = LowStar.BufferView.Down
module UV = LowStar.BufferView.Up
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

noextract
let uint64_to_nat_seq
      (b:Seq.seq UInt64.t)
    : (s:Seq.lseq nat64 (Seq.length b))
    = Seq.init (Seq.length b) (fun (i:nat{i < Seq.length b}) -> (UInt64.v (Seq.index b i) <: nat64))

let math_aux (b:uint8_p) (n:nat) : Lemma
  (requires B.length b = 8 * n)
  (ensures DV.length (get_downview b) % 8 = 0) =
  DV.length_eq (get_downview b)


inline_for_extraction
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
    (DV.length_eq (get_downview ctx_b);
    let key_r0 = UInt64.v (MH.low_buffer_read TUInt8 TUInt64 h0 ctx_b 3) in
    let key_r1 = UInt64.v (MH.low_buffer_read TUInt8 TUInt64 h0 ctx_b 4) in
    let key_s0 = UInt64.v (MH.low_buffer_read TUInt8 TUInt64 h0 ctx_b 5) in
    let key_s1 = UInt64.v (MH.low_buffer_read TUInt8 TUInt64 h0 ctx_b 6) in    
    let key_r = lowerUpper128_opaque key_r0 key_r1 in
    let key_s = lowerUpper128_opaque key_s0 key_s1 in

    let h0_out = UInt64.v (MH.low_buffer_read TUInt8 TUInt64 h1 ctx_b 0) in    
    let h1_out = UInt64.v (MH.low_buffer_read TUInt8 TUInt64 h1 ctx_b 1) in    
    let h = lowerUpper128_opaque h0_out h1_out in
    let db = get_downview inp_b in
    math_aux inp_b (readable_words (UInt64.v len));
    let inp_mem = seqTo128 (uint64_to_nat_seq (UV.as_seq h1 (UV.mk_buffer db Views.up_view64))) in
    h == poly1305_hash key_r key_s inp_mem (UInt64.v len)
    )
  )
