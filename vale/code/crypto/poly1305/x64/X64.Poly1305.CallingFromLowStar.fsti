module X64.Poly1305.CallingFromLowStar

module HS = FStar.HyperStack
module B = LowStar.Buffer
module PU = X64.Poly1305.Util
module PM = X64.Poly1305.Math
module IT = Interop.Types
module PS = Poly_stdcalls
module MH = Vale.AsLowStar.MemoryHelpers
module DV = LowStar.BufferView.Down
module UV = LowStar.BufferView.Up
module BF = Arch.BufferFriend

open Words_s
open Types_s
open FStar.Mul
open FStar.Seq.Base
open Poly1305.Spec_s
open Poly1305.Equiv

val lemma_call_poly1305 (h0 h1:HS.mem) (ctx_b:PS.uint8_p) (inp_b:PS.uint8_p) (src key:bytes) : Lemma
  (requires (
    let open PU in
    let len = length src in
    B.live h1 ctx_b /\
    // copied from Poly_stdcalls.poly1305:
    B.live h0 ctx_b /\ B.live h0 inp_b /\
    B.length ctx_b = 192 /\
    B.length inp_b = 8 * readable_words len /\
    // interface to Poly1305.Equiv:
    equal (BF.of_bytes key) (slice (B.as_seq h0 ctx_b) 24 72) /\
    equal (BF.of_bytes src) (slice (B.as_seq h1 inp_b) 0 len)
  ))
  (ensures (
    let open PU in
    let open PM in
    let open PS in
    let open IT in
    assert (view_n TUInt8 == 1);
    assert (view_n TUInt64 == 8);
    let len = length src in

    // copied from Poly_stdcalls.poly1305:
    DV.length_eq (get_downview ctx_b);
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
    math_aux inp_b (readable_words len);
    let inp_mem = seqTo128 (uint64_to_nat_seq (UV.as_seq h1 (UV.mk_buffer db Views.up_view64))) in
    let h_call = poly1305_hash key_r key_s inp_mem len in

    // interface to Poly1305.Equiv:
    let key_r_spec:nat128 = nat_from_bytes_le (slice key 0 16) in
    let key_s_spec:nat128 = nat_from_bytes_le (slice key 16 32) in
    let h_spec = poly1305_hash key_r key_s (block_fun src) len in
    key_r == key_r_spec /\ key_s == key_s_spec /\ h_call == h_spec
  ))
