module Simplify_Sha

open Words.Seq_s
open Types_s
open SHA_helpers
open X64.MemoryAdapters
open Interop.Base
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module UV = LowStar.BufferView.Up
module DV = LowStar.BufferView.Down
module HS = FStar.HyperStack
open FStar.Mul
open Vale.AsLowStar.MemoryHelpers

val lemma_k_reqs_equiv 
  (k_b:ibuf_t TUInt32 TUInt128)
  (h:HS.mem) : Lemma
  (requires IB.live h k_b /\
    IB.length k_b == 64 /\
    Seq.equal (B.as_seq h k_b) (Spec.SHA2.Constants.k224_256))
  (ensures  (
    DV.length_eq (get_downview k_b);
    k_reqs (UV.as_seq h (UV.mk_buffer (get_downview k_b) Views.up_view128))))

val lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 
  (b:buf_t TUInt8 TUInt128) 
  (h:HS.mem) : Lemma
  (requires True )
  (ensures (
  DV.length_eq (get_downview b);
  Seq.equal
    (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes (UV.as_seq h (UV.mk_buffer (get_downview b) Views.up_view128))))
    (B.as_seq h b)))

val simplify_le_bytes_to_hash_uint32
  (b:buf_t TUInt32 TUInt128)
  (h:HS.mem) : Lemma
  (requires B.live h b /\ B.length b == 8)
  (ensures 
  (reveal_word(); 
  DV.length_eq (get_downview b);
  Seq.equal
    (le_bytes_to_hash (le_seq_quad32_to_bytes (UV.as_seq h (UV.mk_buffer (get_downview b) Views.up_view128))))
    (B.as_seq h b)))
