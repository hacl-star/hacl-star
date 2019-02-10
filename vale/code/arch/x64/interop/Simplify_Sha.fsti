module Simplify_Sha

open Words.Seq_s
open Types_s
open SHA_helpers
open X64.MemoryAdapters
open Interop.Base
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module BV = LowStar.BufferView
module HS = FStar.HyperStack
open FStar.Mul
open Vale.AsLowStar.MemoryHelpers

val lemma_k_reqs_equiv 
  (k_b:IB.ibuffer UInt32.t)
  (k_b8:ibuf_t TUInt128)
  (h:HS.mem) : Lemma
  (requires IB.live h k_b /\ IB.live h k_b8 /\
    IB.length k_b == 64 /\
    IB.length k_b8 == 256 /\
    IB.length k_b8 % 4 == 0 /\
    Seq.equal (B.as_seq h k_b) (Spec.SHA2.Constants.k224_256) /\
    (forall (i:nat{i < IB.length k_b8 / 4}). Seq.index (IB.as_seq h k_b) i == imm_low_buffer_read TUInt32 h k_b8 i))    
  (ensures k_reqs (BV.as_seq h (BV.mk_buffer_view k_b8 Views.view128)))

val lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 
  (b:buf_t TUInt128) 
  (h:HS.mem) : Lemma
  (requires B.live h b )
  (ensures Seq.equal
    (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes (BV.as_seq h (BV.mk_buffer_view b Views.view128))))
    (B.as_seq h b))

val simplify_le_bytes_to_hash_uint32
  (b8:buf_t TUInt128)
  (b:B.buffer UInt32.t)
  (h:HS.mem) : Lemma
  (requires B.live h b /\ B.live h b8 /\ B.length b8 == B.length b * 4 /\ B.length b == 8 /\
    B.length b8 % 4 == 0 /\
    (forall (i:nat{i < B.length b}). Seq.index (B.as_seq h b) i == low_buffer_read TUInt32 h b8 i))
  (ensures (reveal_word(); Seq.equal
    (le_bytes_to_hash (le_seq_quad32_to_bytes (BV.as_seq h (BV.mk_buffer_view b8 Views.view128))))
    (B.as_seq h b)))
