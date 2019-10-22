module Vale.AES.Gcm_simplify

module B = LowStar.Buffer
module DV = LowStar.BufferView.Down
module UV = LowStar.BufferView.Up
module HS = FStar.HyperStack
open Vale.Interop.Base
open Vale.Def.Types_s
open Vale.Arch.Types
open Vale.Def.Words_s
open Vale.Def.Words.Seq_s
open Vale.AsLowStar.MemoryHelpers
open Vale.AES.GCM_helpers
open Vale.AES.AES256_helpers
open FStar.Mul

val le_bytes_to_seq_quad32_uint8_to_nat8_length (s:Seq.seq UInt8.t) : Lemma
  (requires Seq.length s % 16 = 0)
  (ensures Seq.length (le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 s)) == Seq.length s / 16)

val gcm_simplify1 (b:buf_t TUInt8 TUInt128) (h:HS.mem) (n:nat) : Lemma
  (requires B.length b = n)
  (ensures (
    DV.length_eq (get_downview b);
    let s = (le_seq_quad32_to_bytes (UV.as_seq h (UV.mk_buffer (get_downview b) Vale.Interop.Views.up_view128))) in
    n <= Seq.length s ==>
      Seq.equal
        (seq_uint8_to_seq_nat8 (B.as_seq h b))
        (Seq.slice s 0 n)
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

#push-options "--z3cliopt smt.arith.nl=true"
val aes_simplify1 (b:buf_t TUInt8 TUInt128) (h:HS.mem) : Lemma
  (requires B.live h b /\ B.length b = 16)
  (ensures (
  DV.length_eq (get_downview b);
  Seq.equal
    (seq_nat8_to_seq_nat32_LE (seq_uint8_to_seq_nat8 (B.as_seq h b)))
    (quad32_to_seq (low_buffer_read TUInt8 TUInt128 h b 0))
  ))
#pop-options

val aes_simplify2 (b:buf_t TUInt8 TUInt128) (h:HS.mem) : Lemma
  (requires B.live h b /\ B.length b = 32)
  (ensures (
  DV.length_eq (get_downview b);
  Seq.equal
    (seq_nat8_to_seq_nat32_LE (seq_uint8_to_seq_nat8 (B.as_seq h b)))
    (make_AES256_key (low_buffer_read TUInt8 TUInt128 h b 0) (low_buffer_read TUInt8 TUInt128 h b 1))
  ))

val aes_simplify3 (b:buf_t TUInt8 TUInt128) (h:HS.mem) (s:Seq.seq quad32) : Lemma
  (requires B.live h b /\
    (let db = get_downview b in
     DV.length_eq db;
     let ub = UV.mk_buffer db Vale.Interop.Views.up_view128 in
     Seq.equal (UV.as_seq h ub) s)
  )
  (ensures
     Seq.equal (B.as_seq h b)
       (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes s)))

