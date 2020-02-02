module Vale.Poly1305.CallingFromLowStar

module HS = FStar.HyperStack
module B = LowStar.Buffer
module PU = Vale.Poly1305.Util
module PM = Vale.Poly1305.Math
module IT = Vale.Interop.Types
module PS = Vale.Wrapper.X64.Poly
module MH = Vale.AsLowStar.MemoryHelpers
module DV = LowStar.BufferView.Down
module UV = LowStar.BufferView.Up
module BF = Vale.Arch.BufferFriend

open Vale.Def.Words_s
open Vale.Def.Types_s
open FStar.Mul
open FStar.Seq.Base
open Vale.Poly1305.Spec_s
open Vale.Poly1305.Equiv

val lemma_hash_init (h0 h1:HS.mem) (ctx_b:PS.uint8_p) (is_zero:bool) : Lemma
  (requires
    B.live h0 ctx_b /\
    B.live h1 ctx_b /\
    B.length ctx_b == 192 /\
    (forall (i:int).{:pattern (B.get h0 ctx_b i)} 0 <= i /\ i < 24 ==>
      B.get h0 ctx_b i == B.get h1 ctx_b i) /\
    (is_zero ==> (forall (i:int).{:pattern (B.get h0 ctx_b i)} 0 <= i /\ i < 24 ==>
      B.get h0 ctx_b i == 0uy))
  )
  (ensures (
    let open IT in
    assert (view_n TUInt8 == 1);
    assert (view_n TUInt64 == 8);
    DV.length_eq (get_downview ctx_b);
    let h0_in = UInt64.v (MH.low_buffer_read TUInt8 TUInt64 h0 ctx_b 0) in
    let h1_in = UInt64.v (MH.low_buffer_read TUInt8 TUInt64 h0 ctx_b 1) in
    let h2_in = UInt64.v (MH.low_buffer_read TUInt8 TUInt64 h0 ctx_b 2) in
    let h0_out = UInt64.v (MH.low_buffer_read TUInt8 TUInt64 h1 ctx_b 0) in
    let h1_out = UInt64.v (MH.low_buffer_read TUInt8 TUInt64 h1 ctx_b 1) in
    let h2_out = UInt64.v (MH.low_buffer_read TUInt8 TUInt64 h1 ctx_b 2) in
    h0_in == h0_out /\ h1_in == h1_out /\ h2_in == h2_out /\
    (is_zero ==>
      h0_in == 0 /\ h1_in == 0 /\ h2_in == 0 /\ modp 0 == 0 /\
      PM.lowerUpper192 (PM.lowerUpper128 h0_in h1_in) h2_in == 0)
  ))

val lemma_call_poly1305 (h0 h1:HS.mem) (ctx_b:PS.uint8_p) (inp_b:PS.uint8_p) (src key:bytes) : Lemma
  (requires (
    let open PU in
    let len = length src in
    B.live h1 ctx_b /\
    // copied from Vale.Wrapper.X64.Poly.poly1305:
    B.live h0 ctx_b /\ B.live h0 inp_b /\
    B.length ctx_b == 192 /\
    B.length inp_b == 8 * readable_words len /\
    // interface to Poly1305.Equiv:
    equal (BF.of_bytes key) (slice (B.as_seq h0 ctx_b) 24 56) /\
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

    // copied from Vale.Wrapper.X64.Poly.poly1305:
    DV.length_eq (get_downview ctx_b);
    let h0_in = UInt64.v (MH.low_buffer_read TUInt8 TUInt64 h0 ctx_b 0) in
    let h1_in = UInt64.v (MH.low_buffer_read TUInt8 TUInt64 h0 ctx_b 1) in
    let h2_in = UInt64.v (MH.low_buffer_read TUInt8 TUInt64 h0 ctx_b 2) in
    let key_r0 = UInt64.v (MH.low_buffer_read TUInt8 TUInt64 h0 ctx_b 3) in
    let key_r1 = UInt64.v (MH.low_buffer_read TUInt8 TUInt64 h0 ctx_b 4) in
    let key_s0 = UInt64.v (MH.low_buffer_read TUInt8 TUInt64 h0 ctx_b 5) in
    let key_s1 = UInt64.v (MH.low_buffer_read TUInt8 TUInt64 h0 ctx_b 6) in
    let h_in = lowerUpper192 (lowerUpper128 h0_in h1_in) h2_in in
    let key_r = lowerUpper128 key_r0 key_r1 in
    let key_s = lowerUpper128 key_s0 key_s1 in

    let h0_out = UInt64.v (MH.low_buffer_read TUInt8 TUInt64 h1 ctx_b 0) in
    let h1_out = UInt64.v (MH.low_buffer_read TUInt8 TUInt64 h1 ctx_b 1) in
    let h2_out = UInt64.v (MH.low_buffer_read TUInt8 TUInt64 h1 ctx_b 2) in
    let h10 = lowerUpper128 h0_out h1_out in
    let db = get_downview inp_b in
    math_aux inp_b (readable_words len);
    let inp_mem = seqTo128 (uint64_to_nat_seq (UV.as_seq h1 (UV.mk_buffer db Vale.Interop.Views.up_view64))) in
    let n = 0x10000000000000000 in
    let h_call = poly1305_hash_blocks (modp h_in) (n * n) (make_r key_r) inp_mem (len / 16) in
    let h_call' = poly1305_hash_all (modp h_in) key_r key_s inp_mem len in

    // interface to Poly1305.Equiv:
    let key_r_spec:nat128 = nat_from_bytes_le (slice key 0 16) in
    let key_s_spec:nat128 = nat_from_bytes_le (slice key 16 32) in
    let h_spec = poly1305_hash_blocks (modp h_in) (n * n) (make_r key_r) (block_fun src) (len / 16) in
    let h_spec' = poly1305_hash_all (modp h_in) key_r key_s (block_fun src) len in
    let tag = BF.to_bytes (slice (B.as_seq h1 ctx_b) 0 16) in
    key_r == key_r_spec /\ key_s == key_s_spec /\ h_call == h_spec /\ h_call' == h_spec' /\
    h10 == nat_from_bytes_le tag
  ))
