module Vale.Wrapper.X64.Poly

open FStar.HyperStack.ST
module B = LowStar.Buffer
module DV = LowStar.BufferView.Down
module UV = LowStar.BufferView.Up
module HS = FStar.HyperStack
open FStar.Mul
open Vale.Poly1305.Util
open Vale.Poly1305.Math
open Vale.Poly1305.Spec_s
open Vale.Def.Types_s
open Vale.Interop.Base
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

#set-options "--smtencoding.nl_arith_repr boxwrap"
inline_for_extraction
val x64_poly1305
  (ctx_b:uint8_p)
  (inp_b:uint8_p)
  (len:uint64)
  (finish:uint64)
  : Stack unit
  (requires fun h ->
    B.live h ctx_b /\ B.live h inp_b /\
    B.disjoint ctx_b inp_b /\
    B.length ctx_b = 192 /\
    B.length inp_b = 8 * readable_words (UInt64.v len) /\
    UInt64.v (DV.length_eq (get_downview ctx_b); MH.low_buffer_read TUInt8 TUInt64 h ctx_b 2) < 5 /\
    UInt64.v finish < 2
  )
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer ctx_b) h0 h1 /\
    (DV.length_eq (get_downview ctx_b);
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
    let h210 = lowerUpper192 h10 h2_out in
    let db = get_downview inp_b in
    math_aux inp_b (readable_words (UInt64.v len));
    let inp_mem = seqTo128 (uint64_to_nat_seq (UV.as_seq h1 (UV.mk_buffer db Vale.Interop.Views.up_view64))) in
    let n = 0x10000000000000000 in
    (UInt64.v finish == 0 ==>
      modp h210 == poly1305_hash_blocks (modp h_in) (n * n) (make_r key_r) inp_mem (UInt64.v len / 16)) /\
    (UInt64.v finish == 0 ==> h2_out < 5) /\
    (UInt64.v finish == 1 ==> h10 == poly1305_hash_all (modp h_in) key_r key_s inp_mem (UInt64.v len))
    )
  )
