module Gcm_simplify

module B = LowStar.Buffer
module DV = LowStar.BufferView.Down
module UV = LowStar.BufferView.Up
module HS = FStar.HyperStack
open Interop.Base
open Workarounds
open Types_s
open Arch.Types
open Words_s
open Words.Seq_s
open Vale.AsLowStar.MemoryHelpers
open GCM_helpers
open FStar.Mul

val gcm_simplify1 (b:buf_t TUInt8 TUInt128) (h:HS.mem) (n:nat) : Lemma 
  (requires B.live h b /\ B.length b = n)
  (ensures (
  DV.length_eq (get_downview b);
  Seq.equal
    (seq_uint8_to_seq_nat8 (B.as_seq h b))
    (slice_work_around (le_seq_quad32_to_bytes (UV.as_seq h (UV.mk_buffer (get_downview b) Views.up_view128))) n)
  ))

val gcm_simplify2 (b:buf_t TUInt8 TUInt128) (h:HS.mem) : Lemma
  (requires B.live h b /\ B.length b == 16)
  (ensures (
    DV.length_eq (get_downview b);
    assert (DV.length (get_downview b) / 16 == 1);
    Seq.equal
      (seq_uint8_to_seq_nat8 (B.as_seq h b))
      (le_quad32_to_bytes (low_buffer_read TUInt8 TUInt128 h b 0))
  ))
  
val gcm_simplify3 (b:buf_t TUInt8 TUInt128) (h:HS.mem) : Lemma
  (requires B.live h b /\ B.length b == 16)
  (ensures (
    DV.length_eq (get_downview b);
    assert (DV.length (get_downview b) / 16 == 1);
    Seq.equal
      (seq_uint8_to_seq_nat8 (B.as_seq h b))
      (be_quad32_to_bytes (reverse_bytes_quad32 (low_buffer_read TUInt8 TUInt128 h b 0)))
  ))
