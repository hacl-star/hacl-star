module Hacl.Impl.Load51

open FStar.Mul
open FStar.Buffer
open FStar.Endianness

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Endianness
open Hacl.UInt64

let u32 = UInt32.t
let h8 = Hacl.UInt8.t
let h64 = Hacl.UInt64.t
let hint8_p = buffer h8


val load_51: output:felem -> input:hint8_p{length input = 32} -> Stack unit
  (requires (fun h -> Buffer.live h output /\ Buffer.live h input))
  (ensures (fun h0 _ h1 -> Buffer.live h0 output /\ Buffer.live h0 input
    /\ Buffer.live h1 output /\ modifies_1 output h0 h1
    /\ Hacl.Bignum25519.red_513 (as_seq h1 output)
    (* /\ as_seq h1 output == Hacl.Spec.EC.Format.fexpand_spec (as_seq h0 input) *)))
let load_51 output input =
  let h = ST.get() in
  Seq.lemma_eq_intro (Seq.slice (as_seq h input) 0 8) (as_seq h (Buffer.sub input 0ul 8ul));
  Seq.lemma_eq_intro (Seq.slice (as_seq h input) 6 14) (as_seq h (Buffer.sub input 6ul 8ul));
  Seq.lemma_eq_intro (Seq.slice (as_seq h input) 12 20) (as_seq h (Buffer.sub input 12ul 8ul));
  Seq.lemma_eq_intro (Seq.slice (as_seq h input) 19 27) (as_seq h (Buffer.sub input 19ul 8ul));
  Seq.lemma_eq_intro (Seq.slice (as_seq h input) 24 32) (as_seq h (Buffer.sub input 24ul 8ul));
  let mask_51 = uint64_to_limb 0x7ffffffffffffuL in
  let i0 = hload64_le (Buffer.sub input 0ul 8ul) in
  let i1 = hload64_le (Buffer.sub input 6ul 8ul) in
  let i2 = hload64_le (Buffer.sub input 12ul 8ul) in
  let i3 = hload64_le (Buffer.sub input 19ul 8ul) in
  let i4 = hload64_le (Buffer.sub input 24ul 8ul) in
  let output0 = (i0         ) &^ mask_51 in
  let output1 = (i1 >>^ 3ul ) &^ mask_51 in
  let output2 = (i2 >>^ 6ul ) &^ mask_51 in
  let output3 = (i3 >>^ 1ul ) &^ mask_51 in
  let output4 = (i4 >>^ 12ul) &^ mask_51 in
  UInt.logand_mask (v i0) (51);
  UInt.logand_mask (v (i1 >>^ 3ul)) (51);
  UInt.logand_mask (v (i2 >>^ 6ul )) (51);
  UInt.logand_mask (v (i3 >>^ 1ul )) (51);
  UInt.logand_mask (v (i4 >>^ 12ul)) (51);
  Hacl.Lib.Create64.make_h64_5 output output0 output1 output2 output3 output4
