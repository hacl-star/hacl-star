module Gcm_simplify

open Simplify_Sha

let gcm_simplify1 b h n =
  let db = get_downview b in
  DV.length_eq db;
  let ub = UV.mk_buffer db Views.up_view128 in
  UV.length_eq ub;
  lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 b h

let gcm_simplify2 b h =
  let view = Views.up_view128 in
  let s_init = B.as_seq h b in
  let db = get_downview b in
  let s_down = DV.as_seq h db in
  DV.length_eq db;
  assert (DV.length (get_downview b) / 16 = 1);
  let b_v = UV.mk_buffer db view in
  UV.length_eq b_v;  
  UV.get_sel h b_v 0;
  let aux (i:nat{i < B.length b}) : Lemma (Seq.index s_init i == Seq.index s_down i) =
    DV.as_seq_sel h db i;
    DV.get_sel h db i;
    Opaque_s.reveal_opaque Views.get8_def
  in Classical.forall_intro aux;
  assert (Seq.equal (DV.as_seq h db) (B.as_seq h b));
  Opaque_s.reveal_opaque Views.get128_def;
  le_quad32_to_bytes_to_quad32 (seq_uint8_to_seq_nat8 s_init)

open Collections.Seqs_s
open Words.Four_s

let simplify_be_quad32 (q:quad32) : Lemma
  (be_quad32_to_bytes (reverse_bytes_quad32 q) == le_quad32_to_bytes q)
  = reveal_reverse_bytes_quad32 q;
  let q' = four_map reverse_bytes_nat32 q in
  let q_rev = reverse_bytes_quad32 q in
  let q_f = be_quad32_to_bytes q_rev in
  assert (q_f = seq_four_to_seq_BE (seq_map (nat_to_four 8) (four_to_seq_BE q_rev)));
  assert (q_rev.lo0 = q'.hi3);
  admit()

let gcm_simplify3 b h =
  let db = get_downview b in
  DV.length_eq db;
  assert (DV.length (get_downview b) / 16 = 1);
  simplify_be_quad32 (low_buffer_read TUInt8 TUInt128 h b 0);
  gcm_simplify2 b h
