module Vale.Poly1305.CallingFromLowStar
open FStar.Mul

module BS = Lib.ByteSequence
module LI = Lib.IntTypes
module FE = FStar.Endianness
module PU = Vale.Poly1305.Util
module PM = Vale.Poly1305.Math
module IT = Vale.Interop.Types
module PS = Vale.Wrapper.X64.Poly

#reset-options "--z3rlimit 100"

let lemma_hash_init h0 h1 ctx_b is_zero =
  let open IT in
  let tag0 = BF.to_bytes (slice (B.as_seq h0 ctx_b) 0 24) in
  let tag1 = BF.to_bytes (slice (B.as_seq h1 ctx_b) 0 24) in
  assert (forall (i:int).{:pattern (index (BF.of_bytes tag0) i)} 0 <= i /\ i < 24 ==> index (BF.of_bytes tag0) i == B.get h0 ctx_b i);
  assert (forall (i:int).{:pattern (index (BF.of_bytes tag1) i)} 0 <= i /\ i < 24 ==> index (BF.of_bytes tag1) i == B.get h1 ctx_b i);
  // REVIEW: triggers F* "Unexpected error": assert (equal (BF.of_bytes tag0) (BF.of_bytes tag1));
  let workaround : squash (equal (BF.of_bytes tag0) (BF.of_bytes tag1)) = () in
  assert (view_n TUInt8 == 1);
  assert (view_n TUInt64 == 8);
  DV.length_eq (get_downview ctx_b);
  let h0_in = UInt64.v (MH.low_buffer_read TUInt8 TUInt64 h0 ctx_b 0) in
  let h1_in = UInt64.v (MH.low_buffer_read TUInt8 TUInt64 h0 ctx_b 1) in
  let h2_in = UInt64.v (MH.low_buffer_read TUInt8 TUInt64 h0 ctx_b 2) in
  let h0_out = UInt64.v (MH.low_buffer_read TUInt8 TUInt64 h1 ctx_b 0) in
  let h1_out = UInt64.v (MH.low_buffer_read TUInt8 TUInt64 h1 ctx_b 1) in
  let h2_out = UInt64.v (MH.low_buffer_read TUInt8 TUInt64 h1 ctx_b 2) in
  let view = Vale.AsLowStar.LowStarSig.view_of_base_typ TUInt64 in
  let ctx_db = get_downview ctx_b in
  let ctx_vb = UV.mk_buffer ctx_db view in
  UV.length_eq ctx_vb;
  let open Vale.Def.Words.Seq_s in
  BF.nat_from_bytes_le_is_le_bytes_to_nat64 (slice tag0 0 8);
  calc (==) {
    h0_in;
    == {}
    UInt64.v (UV.sel h0 ctx_vb 0);
    == {UV.get_sel h0 ctx_vb 0; Vale.Interop.Views.get64_reveal ()}
    le_bytes_to_nat64 (seq_uint8_to_seq_nat8 (slice (DV.as_seq h0 (UV.as_down_buffer ctx_vb)) 0 8));
    == {BF.same_seq_downview8 ctx_b h0}
    nat_from_bytes_le (slice tag0 0 8);
  };
  BF.nat_from_bytes_le_is_le_bytes_to_nat64 (slice tag1 0 8);
  calc (==) {
    h0_out;
    == {}
    UInt64.v (UV.sel h1 ctx_vb 0);
    == {UV.get_sel h1 ctx_vb 0; Vale.Interop.Views.get64_reveal ()}
    le_bytes_to_nat64 (seq_uint8_to_seq_nat8 (slice (DV.as_seq h1 (UV.as_down_buffer ctx_vb)) 0 8));
    == {BF.same_seq_downview8 ctx_b h1}
    nat_from_bytes_le (slice tag1 0 8);
  };
  BF.lemma_le_to_n_is_nat_from_bytes (BF.of_bytes (slice tag0 0 8));
  if is_zero then
    calc (==) {
      nat_from_bytes_le (slice tag0 0 8) <: nat;
      == {}
      FE.le_to_n (BF.of_bytes (slice tag0 0 8));
      == {BF.lemma_le_to_n_indexed (BF.of_bytes (slice tag0 0 8))}
      BF.le_to_n_indexed (BF.of_bytes (slice tag0 0 8));
      == {
        norm_spec [iota; zeta; primops; delta_only [`%BF.le_to_n_indexed_rec; `%pow2]]
          (BF.le_to_n_indexed_rec (BF.of_bytes (slice tag0 0 8)) 8)
      }
      0;
    };
  BF.nat_from_bytes_le_is_le_bytes_to_nat64 (slice tag0 8 16);
  calc (==) {
    h1_in;
    == {}
    UInt64.v (UV.sel h0 ctx_vb 1);
    == {UV.get_sel h0 ctx_vb 1; Vale.Interop.Views.get64_reveal ()}
    le_bytes_to_nat64 (seq_uint8_to_seq_nat8 (slice (DV.as_seq h0 (UV.as_down_buffer ctx_vb)) 8 16));
    == {BF.same_seq_downview8 ctx_b h0}
    nat_from_bytes_le (slice tag0 8 16);
  };
  BF.nat_from_bytes_le_is_le_bytes_to_nat64 (slice tag1 8 16);
  calc (==) {
    h1_out;
    == {}
    UInt64.v (UV.sel h1 ctx_vb 1);
    == {UV.get_sel h1 ctx_vb 1; Vale.Interop.Views.get64_reveal ()}
    le_bytes_to_nat64 (seq_uint8_to_seq_nat8 (slice (DV.as_seq h1 (UV.as_down_buffer ctx_vb)) 8 16));
    == {BF.same_seq_downview8 ctx_b h1}
    nat_from_bytes_le (slice tag1 8 16);
  };
  BF.lemma_le_to_n_is_nat_from_bytes (BF.of_bytes (slice tag0 8 16));
  if is_zero then
    calc (==) {
      nat_from_bytes_le (slice tag0 8 16) <: nat;
      == {}
      FE.le_to_n (BF.of_bytes (slice tag0 8 16));
      == {BF.lemma_le_to_n_indexed (BF.of_bytes (slice tag0 8 16))}
      BF.le_to_n_indexed (BF.of_bytes (slice tag0 8 16));
      == {
        norm_spec [iota; zeta; primops; delta_only [`%BF.le_to_n_indexed_rec; `%pow2]]
          (BF.le_to_n_indexed_rec (BF.of_bytes (slice tag0 8 16)) 8)
      }
      0;
    };
  BF.nat_from_bytes_le_is_le_bytes_to_nat64 (slice tag0 16 24);
  calc (==) {
    h2_in;
    == {}
    UInt64.v (UV.sel h0 ctx_vb 2);
    == {UV.get_sel h0 ctx_vb 2; Vale.Interop.Views.get64_reveal ()}
    le_bytes_to_nat64 (seq_uint8_to_seq_nat8 (slice (DV.as_seq h0 (UV.as_down_buffer ctx_vb)) 16 24));
    == {BF.same_seq_downview8 ctx_b h0}
    nat_from_bytes_le (slice tag0 16 24);
  };
  BF.nat_from_bytes_le_is_le_bytes_to_nat64 (slice tag1 16 24);
  calc (==) {
    h2_out;
    == {}
    UInt64.v (UV.sel h1 ctx_vb 2);
    == {UV.get_sel h1 ctx_vb 2; Vale.Interop.Views.get64_reveal ()}
    le_bytes_to_nat64 (seq_uint8_to_seq_nat8 (slice (DV.as_seq h1 (UV.as_down_buffer ctx_vb)) 16 24));
    == {BF.same_seq_downview8 ctx_b h1}
    nat_from_bytes_le (slice tag1 16 24);
  };
  BF.lemma_le_to_n_is_nat_from_bytes (BF.of_bytes (slice tag0 16 24));
  if is_zero then
    calc (==) {
      nat_from_bytes_le (slice tag0 16 24) <: nat;
      == {}
      FE.le_to_n (BF.of_bytes (slice tag0 16 24));
      == {BF.lemma_le_to_n_indexed (BF.of_bytes (slice tag0 16 24))}
      BF.le_to_n_indexed (BF.of_bytes (slice tag0 16 24));
      == {
        norm_spec [iota; zeta; primops; delta_only [`%BF.le_to_n_indexed_rec; `%pow2]]
          (BF.le_to_n_indexed_rec (BF.of_bytes (slice tag0 16 24)) 8)
      }
      0;
    };
  assert_norm (modp 0 == 0);
  if is_zero then
    calc (==) {
      PM.lowerUpper192 (PM.lowerUpper128 h0_in h1_in) h2_in;
      == {PM.lowerUpper128_reveal (); PM.lowerUpper192_reveal ()}
      0;
    }

let lemma_block (h1:HS.mem) (inp_b:B.buffer UInt8.t) (len:nat) (i:nat) : Lemma
  (requires B.length inp_b = 8 * PU.readable_words len /\ i < B.length inp_b / 16)
  (ensures (
    PS.math_aux inp_b (PU.readable_words len);
    let inp_db = IT.get_downview inp_b in
    let inp_sb = B.as_seq h1 inp_b in
    let inp_mem = PU.seqTo128 (PS.uint64_to_nat_seq (UV.as_seq h1 (UV.mk_buffer inp_db Vale.Interop.Views.up_view64))) in
    inp_mem i == block_fun (BF.to_bytes inp_sb) i
  ))
  =
  PS.math_aux inp_b (PU.readable_words len);
  let inp_sb = B.as_seq h1 inp_b in
  let text = BF.to_bytes inp_sb in
  let inp_db = IT.get_downview inp_b in
  let inp_vb = UV.mk_buffer inp_db Vale.Interop.Views.up_view64 in
  let inp_su = UV.as_seq h1 inp_vb in
  let inp_mem = PU.seqTo128 (PS.uint64_to_nat_seq inp_su) in
  let inp_sd = DV.as_seq h1 (UV.as_down_buffer inp_vb) in
  let j1 = i * size_block in
  let j2 = i * size_block + size_block in
  Math.Lemmas.pow2_le_compat 128 (8 * (j2 - j1));
  UV.length_eq inp_vb;
  BF.same_seq_downview8 inp_b h1;
  BF.lemma_up_as_seq_index h1 inp_vb (2 * i);
  BF.lemma_up_as_seq_index h1 inp_vb (2 * i + 1);
  let open Vale.Def.Words.Seq_s in
  BF.nat_from_bytes_le_is_le_bytes_to_nat64 (slice text j1 (j1 + 8));
  calc (==) {
    UInt64.v (index inp_su (2 * i));
    == {Vale.Interop.Views.get64_reveal ()}
    UInt64.v (Vale.Interop.Views.get64_def (slice inp_sd j1 (j1 + 8)));
    == {}
    le_bytes_to_nat64 (seq_uint8_to_seq_nat8 (BF.of_bytes (slice text j1 (j1 + 8))));
    == {}
    nat_from_bytes_le (slice text j1 (j1 + 8));
  };
  BF.nat_from_bytes_le_is_le_bytes_to_nat64 (slice text (j1 + 8) (j1 + 16));
  calc (==) {
    UInt64.v (index inp_su (2 * i + 1));
    == {Vale.Interop.Views.get64_reveal ()}
    UInt64.v (Vale.Interop.Views.get64_def (slice inp_sd (j1 + 8) (j1 + 16)));
    == {}
    le_bytes_to_nat64 (seq_uint8_to_seq_nat8 (BF.of_bytes (slice text (j1 + 8) (j1 + 16))));
    == {}
    nat_from_bytes_le (slice text (j1 + 8) (j1 + 16));
  };
  calc (==) {
    inp_mem i;
    == {}
    UInt64.v (index inp_su (2 * i)) + pow2 64 * UInt64.v (index inp_su (2 * i + 1));
    == {}
    nat_from_bytes_le (slice text j1 (j1 + 8)) + pow2 64 * nat_from_bytes_le (slice text (j1 + 8) (j1 + 16));
    == {}
    nat_from_bytes_le (slice (slice text j1 j2) 0 8) + pow2 64 * nat_from_bytes_le (slice (slice text j1 j2) 8 16);
    == {BS.nat_from_intseq_le_slice_lemma #LI.U8 #LI.SEC #16 (slice text j1 j2) 8}
    nat_from_bytes_le (slice text j1 j2);
    == {}
    block_fun text i;
  }

let lemma_block_extra (h1:HS.mem) (inp_b:B.buffer UInt8.t) (len:nat) : Lemma
  (requires B.length inp_b = 8 * PU.readable_words len /\ len % 16 > 0)
  (ensures (
    PS.math_aux inp_b (PU.readable_words len);
    let i = len / 16 in
    let nExtra = len % 16 in
    let padLast = pow2 (nExtra * 8) in
    let inp_db = IT.get_downview inp_b in
    let inp_sb = B.as_seq h1 inp_b in
    let inp_ssb = slice inp_sb 0 len in
    let inp_mem = PU.seqTo128 (PS.uint64_to_nat_seq (UV.as_seq h1 (UV.mk_buffer inp_db Vale.Interop.Views.up_view64))) in
    inp_mem i % padLast == block_fun (BF.to_bytes inp_ssb) i % padLast
  ))
  =
  PS.math_aux inp_b (PU.readable_words len);
  let i = len / 16 in
  let nExtra = len % 16 in
  let padLast = pow2 (nExtra * 8) in
  let inp_db = IT.get_downview inp_b in
  let inp_sb = B.as_seq h1 inp_b in
  let inp_ssb = slice inp_sb 0 len in
  let inp_mem = PU.seqTo128 (PS.uint64_to_nat_seq (UV.as_seq h1 (UV.mk_buffer inp_db Vale.Interop.Views.up_view64))) in
  let j1 = i * size_block in
  let j2 = i * size_block + size_block in
  let text = BF.to_bytes inp_sb in
  let block = slice text j1 j2 in
  let nLo = nat_from_bytes_le (slice block 0 nExtra) in
  let nHi = nat_from_bytes_le (slice block nExtra 16) in
  calc (==) {
    inp_mem i % padLast;
    == {lemma_block h1 inp_b len i}
    block_fun text i % padLast;
    == {}
    nat_from_bytes_le block % padLast;
    == {BS.nat_from_intseq_le_slice_lemma #LI.U8 #LI.SEC #16 block nExtra}
    (nLo + padLast * nHi) % padLast;
    == {FStar.Math.Lemmas.swap_mul nHi padLast}
    (nLo + nHi * padLast) % padLast;
    == {FStar.Math.Lemmas.lemma_mod_plus nLo nHi padLast}
    nLo % padLast;
    == {}
    block_fun (BF.to_bytes inp_ssb) i % padLast;
  }

let post_call_poly1305_blocks (h1:HS.mem) (inp_b:PS.uint8_p) (src:bytes) (h_in pad r:int) (k:nat
  {B.length inp_b = 8 * PU.readable_words (length src) /\ k <= B.length inp_b / 16}) =
    let len = length src in
    PS.math_aux inp_b (PU.readable_words len);
    let inp_db = IT.get_downview inp_b in
    let inp_sb = B.as_seq h1 inp_b in
    let inp_mem = PU.seqTo128 (PS.uint64_to_nat_seq (UV.as_seq h1 (UV.mk_buffer inp_db Vale.Interop.Views.up_view64))) in
    let h_call = poly1305_hash_blocks (modp h_in) pad r inp_mem k in
    let h_spec = poly1305_hash_blocks (modp h_in) pad r (block_fun src) k in
    h_call == h_spec

let rec lemma_call_poly1305_blocks (h1:HS.mem) (inp_b:PS.uint8_p) (src:bytes) (h_in pad r:int) (k:nat) : Lemma
  (requires (
    let len = length src in
    B.length inp_b = 8 * PU.readable_words len /\
    equal (BF.of_bytes src) (slice (B.as_seq h1 inp_b) 0 len) /\
    k <= len / 16
  ))
  (ensures (
(* REVIEW: this didn't type check because of the "let rec" (non-recursive "let" worked):
    let len = length src in
    PS.math_aux inp_b (PU.readable_words len);
    let inp_db = IT.get_downview inp_b in
    let inp_sb = B.as_seq h1 inp_b in
    let inp_mem = PU.seqTo128 (PS.uint64_to_nat_seq (UV.as_seq h1 (UV.mk_buffer inp_db Vale.Interop.Views.up_view64))) in
    let h_call = poly1305_hash_blocks (modp h_in) pad r inp_mem k in
    let h_spec = poly1305_hash_blocks (modp h_in) pad r (block_fun src) k in
    h_call == h_spec
*)
    post_call_poly1305_blocks h1 inp_b src h_in pad r k
  ))
  =
  let len = length src in
  if k > 0 then
  (
    lemma_call_poly1305_blocks h1 inp_b src h_in pad r (k - 1);
    lemma_block h1 inp_b len (k - 1);
    let inp_sb = B.as_seq h1 inp_b in
    let j1 = (k - 1) * size_block in
    let j2 = (k - 1) * size_block + size_block in
    assert (BF.to_bytes (BF.of_bytes src) == src);
    assert (equal (slice (BF.to_bytes inp_sb) j1 j2) (slice src j1 j2));
    ()
  )

let lemma_call_poly1305_all (h1:HS.mem) (inp_b:PS.uint8_p) (src:bytes) (h_in:int) (key_r key_s:nat128) : Lemma
  (requires (
    let len = length src in
    B.length inp_b = 8 * PU.readable_words len /\
    equal (BF.of_bytes src) (slice (B.as_seq h1 inp_b) 0 len)
  ))
  (ensures (
    let len = length src in
    PS.math_aux inp_b (PU.readable_words len);
    let inp_db = IT.get_downview inp_b in
    let inp_sb = B.as_seq h1 inp_b in
    let inp_mem = PU.seqTo128 (PS.uint64_to_nat_seq (UV.as_seq h1 (UV.mk_buffer inp_db Vale.Interop.Views.up_view64))) in
    let h_call = poly1305_hash_all (modp h_in) key_r key_s inp_mem len in
    let h_spec = poly1305_hash_all (modp h_in) key_r key_s (block_fun src) len in
    h_call == h_spec
  ))
  =
  let len = length src in
  let r = iand key_r 0x0ffffffc0ffffffc0ffffffc0fffffff in
  let nBlocks = len / 16 in
  let nExtra = len % 16 in
  lemma_call_poly1305_blocks h1 inp_b src h_in pow2_128 r nBlocks;
  if nExtra > 0 then lemma_block_extra h1 inp_b len;
  ()

let lemma_call_poly1305 h0 h1 ctx_b inp_b src key =
  let open Vale.Def.Words.Seq_s in
  let open PU in
  let open PM in
  let open PS in
  let open IT in
  let len = length src in
  assert (view_n TUInt8 == 1);
  assert (view_n TUInt64 == 8);

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
  let h = lowerUpper128 h0_out h1_out in
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

  let view = Vale.AsLowStar.LowStarSig.view_of_base_typ TUInt64 in
  let ctx_db = get_downview ctx_b in
  let ctx_vb = UV.mk_buffer ctx_db view in
  UV.length_eq ctx_vb;

  BF.nat_from_bytes_le_is_le_bytes_to_nat64 (slice key 0 8);
  calc (==) {
    key_r0;
    == {}
    UInt64.v (UV.sel h0 ctx_vb 3);
    == {UV.get_sel h0 ctx_vb 3; Vale.Interop.Views.get64_reveal ()}
    le_bytes_to_nat64 (seq_uint8_to_seq_nat8 (slice (DV.as_seq h0 (UV.as_down_buffer ctx_vb)) 24 32));
    == {BF.same_seq_downview8 ctx_b h0}
    nat_from_bytes_le (slice (slice key 0 16) 0 8);
  };

  BF.nat_from_bytes_le_is_le_bytes_to_nat64 (slice key 8 16);
  calc (==) {
    key_r1;
    == {}
    UInt64.v (UV.sel h0 ctx_vb 4);
    == {UV.get_sel h0 ctx_vb 4; Vale.Interop.Views.get64_reveal ()}
    le_bytes_to_nat64 (seq_uint8_to_seq_nat8 (slice (DV.as_seq h0 (UV.as_down_buffer ctx_vb)) 32 40));
    == {BF.same_seq_downview8 ctx_b h0}
    nat_from_bytes_le (slice (slice key 0 16) 8 16);
  };

  calc (==) {
    key_r;
    == {}
    lowerUpper128 key_r0 key_r1;
    == {lowerUpper128_reveal ()}
    nat_from_bytes_le (slice (slice key 0 16) 0 8) + pow2 64 * nat_from_bytes_le (slice (slice key 0 16) 8 16);
    == {BS.nat_from_intseq_le_slice_lemma #LI.U8 #LI.SEC #16 (slice key 0 16) 8}
    nat_from_bytes_le (slice key 0 16);
    == {}
    key_r_spec;
  };

  BF.nat_from_bytes_le_is_le_bytes_to_nat64 (slice key 16 24);
  calc (==) {
    key_s0;
    == {}
    UInt64.v (UV.sel h0 ctx_vb 5);
    == {UV.get_sel h0 ctx_vb 5; Vale.Interop.Views.get64_reveal ()}
    le_bytes_to_nat64 (seq_uint8_to_seq_nat8 (slice (DV.as_seq h0 (UV.as_down_buffer ctx_vb)) 40 48));
    == {BF.same_seq_downview8 ctx_b h0}
    nat_from_bytes_le (slice (slice key 16 32) 0 8);
  };

  BF.nat_from_bytes_le_is_le_bytes_to_nat64 (slice key 24 32);
  calc (==) {
    key_s1;
    == {}
    UInt64.v (UV.sel h0 ctx_vb 6);
    == {UV.get_sel h0 ctx_vb 6; Vale.Interop.Views.get64_reveal ()}
    le_bytes_to_nat64 (seq_uint8_to_seq_nat8 (slice (DV.as_seq h0 (UV.as_down_buffer ctx_vb)) 48 56));
    == {BF.same_seq_downview8 ctx_b h0}
    nat_from_bytes_le (slice (slice key 16 32) 8 16);
  };

  calc (==) {
    key_s;
    == {}
    lowerUpper128 key_s0 key_s1;
    == {lowerUpper128_reveal ()}
    nat_from_bytes_le (slice (slice key 16 32) 0 8) + pow2 64 * nat_from_bytes_le (slice (slice key 16 32) 8 16);
    == {BS.nat_from_intseq_le_slice_lemma #LI.U8 #LI.SEC #16 (slice key 16 32) 8}
    nat_from_bytes_le (slice key 16 32);
    == {}
    key_s_spec;
  };

  let r = iand key_r 0x0ffffffc0ffffffc0ffffffc0fffffff in
  let nBlocks = len / 16 in
  lemma_call_poly1305_blocks h1 inp_b src h_in pow2_128 r nBlocks;
  lemma_call_poly1305_all h1 inp_b src h_in key_r key_s;

  let tag = BF.to_bytes (slice (B.as_seq h1 ctx_b) 0 16) in

  BF.nat_from_bytes_le_is_le_bytes_to_nat64 (slice tag 0 8);
  calc (==) {
    h0_out;
    == {}
    UInt64.v (UV.sel h1 ctx_vb 0);
    == {UV.get_sel h1 ctx_vb 0; Vale.Interop.Views.get64_reveal ()}
    le_bytes_to_nat64 (seq_uint8_to_seq_nat8 (slice (DV.as_seq h1 (UV.as_down_buffer ctx_vb)) 0 8));
    == {BF.same_seq_downview8 ctx_b h1}
    nat_from_bytes_le (slice tag 0 8);
  };

  BF.nat_from_bytes_le_is_le_bytes_to_nat64 (slice tag 8 16);
  calc (==) {
    h1_out;
    == {}
    UInt64.v (UV.sel h1 ctx_vb 1);
    == {UV.get_sel h1 ctx_vb 1; Vale.Interop.Views.get64_reveal ()}
    le_bytes_to_nat64 (seq_uint8_to_seq_nat8 (slice (DV.as_seq h1 (UV.as_down_buffer ctx_vb)) 8 16));
    == {BF.same_seq_downview8 ctx_b h1}
    nat_from_bytes_le (slice tag 8 16);
  };

  calc (==) {
    h;
    == {}
    lowerUpper128 h0_out h1_out;
    == {lowerUpper128_reveal ()}
    nat_from_bytes_le (slice tag 0 8) + pow2 64 * nat_from_bytes_le (slice tag 8 16);
    == {BS.nat_from_intseq_le_slice_lemma #LI.U8 #LI.SEC #16 tag 8}
    nat_from_bytes_le tag;
  };

  ()
