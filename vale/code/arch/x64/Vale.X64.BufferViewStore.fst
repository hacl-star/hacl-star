module Vale.X64.BufferViewStore

open Vale.Interop.Views
open Vale.Interop
module MB = LowStar.Monotonic.Buffer
module HS = FStar.HyperStack
open Vale.Lib.BufferViewHelpers
open Vale.Def.Types_s
open Vale.Def.Words_s
open Vale.Def.Words.Two_s
open Vale.Def.Words.Two
open Vale.Def.Words.Four_s
open Vale.Def.Words.Seq_s
open Vale.Def.Words.Seq
open Vale.Arch.Types

open FStar.Calc

friend LowStar.BufferView.Up

#reset-options "--z3rlimit 10 --max_fuel 0 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 1"

let math_aux (a b c:int) : Lemma (a + b + (c - b) == a + c) = ()

let map_aux (ptr1 ptr2:int) (v:int) (m:machine_heap) : Lemma
  (requires ptr1 == ptr2 /\ m.[ptr1] == v)
  (ensures m.[ptr2] == v) = ()

let get64_aux (ptr:int) (heap:machine_heap) (v:nat64) (k:nat{k < 8}) : Lemma
  (requires get_heap_val64 ptr heap == v)
  (ensures heap.[ptr + k] == UInt8.v (Seq.index (put64 (UInt64.uint_to_t v)) k)) =
  Vale.Def.Opaque_s.reveal_opaque get_heap_val64_def;
  Vale.Def.Opaque_s.reveal_opaque put64_def;
  Vale.Def.Opaque_s.reveal_opaque le_nat64_to_bytes_def;
  FStar.Pervasives.reveal_opaque (`%seq_four_to_seq_LE) (seq_four_to_seq_LE #nat8);
  four_to_nat_8_injective ();
  two_to_nat_32_injective ()

let get128_aux (ptr:int) (heap:machine_heap) (v:quad32) (k:nat{k < 16}) : Lemma
  (requires get_heap_val128 ptr heap == v)
  (ensures heap.[ptr + k] == UInt8.v (Seq.index (put128 v) k)) =
  Vale.Def.Opaque_s.reveal_opaque get_heap_val128_def;
  Vale.Def.Opaque_s.reveal_opaque get_heap_val32_def;
  Vale.Def.Opaque_s.reveal_opaque put128_def;
  FStar.Pervasives.reveal_opaque (`%seq_four_to_seq_LE) (seq_four_to_seq_LE #nat8);
  FStar.Pervasives.reveal_opaque (`%le_quad32_to_bytes) le_quad32_to_bytes;
  four_to_nat_8_injective ()

#reset-options "--max_fuel 1 --initial_fuel 1 --z3rlimit 200"

let bv_upd_update_heap64 b heap i v mem =
  let dv = IB.get_downview b.IB.bsrc in
  DV.length_eq dv;
  let uv = UV.mk_buffer dv up_view64 in
  let addrs = IB.addrs_of_mem mem in
  let h = IB.hs_of_mem mem in
  UV.length_eq uv;
  let ptr = addrs b + 8 * i in
  let heap' = update_heap64 ptr v heap in
  let prefix, _, suffix = UV.split_at_i uv i h in
  let s_down = prefix `Seq.append` (put64 (UInt64.uint_to_t v) `Seq.append` suffix) in
  let s_f = get_seq_heap heap' addrs b in
  let h' = UV.upd h uv i (UInt64.uint_to_t v) in
  // This is by definition of UV.upd, fetched from the friended definition
  assert (h' == DV.upd_seq h dv s_down);
  DV.upd_seq_spec h dv s_down;
  // assert (DV.as_seq h' dv == s_down);

  // We know that all elements but UV.sel h' uv i will be the same, (using UV.sel_upd lemmas)
  // hence aux1 and aux3 can be proven with initial correct_down_p on h
  // and the Bytes_Semantics.frame lemma
  // For aux2, we know that get64 (Seq.slice s_down (i*8) (i*8+8)) = v (through UV.sel lemmas)
  // We also know that get_heap_val64 ptr = v, which with get64_aux and some index matching
  // should give us the property
  let aux1 (j:nat{j < i * 8}) : Lemma (Seq.index s_down j == Seq.index s_f j)
    = let base = j / 8 in
      let s_init = DV.as_seq h dv in

      calc (==) {
        Seq.index s_down j;
        ( == ) { FStar.Math.Lemmas.euclidean_division_definition j 8 }
        Seq.index s_down (base * 8 + j%8);
        ( == ) {  assert (base * 8 + 8 <= Seq.length s_down);
                  Seq.lemma_index_slice s_down (base*8) (base*8 + 8) (j % 8)
                } // True by slice properties
        Seq.index (Seq.slice s_down (base*8) (base*8 + 8)) (j%8);
        ( == ) {
          UV.sel_upd uv i base (UInt64.uint_to_t v) h;
          // assert (UV.sel h uv base == UV.sel h' uv base);
          UV.get_sel h uv base;
          UV.get_sel h' uv base;
          // With the injectivity of get64, which we get from get64 and put64 being inverses,
          // we get the following
          assert (Seq.equal (Seq.slice s_init (base*8) (base*8+8)) (Seq.slice s_down (base*8) (base*8+8))) }
        Seq.index (Seq.slice s_init (base*8) (base*8 + 8)) (j%8);
        ( == ) { assert (base * 8 + 8 <= Seq.length s_init);
                  Seq.lemma_index_slice s_init (base*8) (base*8 + 8) (j % 8)
                } // True by slice properties
        Seq.index s_init (base * 8 + j%8);
        ( == ) { FStar.Math.Lemmas.euclidean_division_definition j 8 }
        Seq.index s_init j;
        ( == ) { assert (Seq.index s_init j == UInt8.uint_to_t (heap.[addrs b + j])) }
        UInt8.uint_to_t (heap.[addrs b + j]); // True by correct_down_p
        ( == ) { Vale.X64.Bytes_Semantics.frame_update_heap ptr v heap } // True by frame_update
        UInt8.uint_to_t (heap'.[addrs b + j]);
        ( == ) { } // True by definition of get_seq_heap
        Seq.index s_f j;
      }
  in let aux2(j:nat{j >= i * 8 /\ j < i * 8 + 8}) : Lemma (Seq.index s_down j == Seq.index s_f j)
    = UV.sel_upd uv i i (UInt64.uint_to_t v) h;
      // assert (UV.sel h' uv i == UInt64.uint_to_t v);
      UV.get_sel h' uv i;
      // assert (Vale.Interop.Views.get64 (Seq.slice s_down (i*8) (i*8+8)) = UInt64.uint_to_t v);
      Vale.X64.Bytes_Semantics.correct_update_get ptr v heap;
      // assert (get_heap_val64 ptr heap' = v);
      let k = j - i * 8 in
      get64_aux ptr heap' v k;
      // assert (heap'.[ptr + k] = UInt8.v (Seq.index (put64 (UInt64.uint_to_t v)) k));
      map_aux (ptr + k) (addrs b + j) (UInt8.v (Seq.index s_down j))  heap'
      // assert (heap'.[ptr + k] = heap'.[addrs b + j])
  in let aux3 (j:nat{j >= i * 8 + 8 /\ j < Seq.length s_down}) : Lemma (Seq.index s_down j == Seq.index s_f j)
    = let base = j / 8 in
      let s_init = DV.as_seq h dv in

      calc (==) {
        Seq.index s_down j;
        ( == ) { FStar.Math.Lemmas.euclidean_division_definition j 8 }
        Seq.index s_down (base * 8 + j%8);
        ( == ) {  assert (base * 8 + 8 <= Seq.length s_down);
                  Seq.lemma_index_slice s_down (base*8) (base*8 + 8) (j % 8)
                } // True by slice properties
        Seq.index (Seq.slice s_down (base*8) (base*8 + 8)) (j%8);
        ( == ) {
          UV.sel_upd uv i base (UInt64.uint_to_t v) h;
          // assert (UV.sel h uv base == UV.sel h' uv base);
          UV.get_sel h uv base;
          UV.get_sel h' uv base;
          // With the injectivity of get64, which we get from get64 and put64 being inverses,
          // we get the following
          assert (Seq.equal (Seq.slice s_init (base*8) (base*8+8)) (Seq.slice s_down (base*8) (base*8+8))) }
        Seq.index (Seq.slice s_init (base*8) (base*8 + 8)) (j%8);
        ( == ) { assert (base * 8 + 8 <= Seq.length s_init);
                  Seq.lemma_index_slice s_init (base*8) (base*8 + 8) (j % 8)
                } // True by slice properties
        Seq.index s_init (base * 8 + j%8);
        ( == ) { FStar.Math.Lemmas.euclidean_division_definition j 8 }
        Seq.index s_init j;
        ( == ) { assert (Seq.index s_init j == UInt8.uint_to_t (heap.[addrs b + j])) }
        UInt8.uint_to_t (heap.[addrs b + j]); // True by correct_down_p
        ( == ) { Vale.X64.Bytes_Semantics.frame_update_heap ptr v heap } // True by frame_update
        UInt8.uint_to_t (heap'.[addrs b + j]);
        ( == ) { } // True by definition of get_seq_heap
        Seq.index s_f j;
      }
  in
  Classical.forall_intro aux1;
  Classical.forall_intro aux2;
  Classical.forall_intro aux3;
  assert (Seq.equal s_down s_f)

let bv_upd_update_heap128 b heap i v mem =
  let dv = IB.get_downview b.IB.bsrc in
  DV.length_eq dv;
  let uv = UV.mk_buffer dv up_view128 in
  let addrs = IB.addrs_of_mem mem in
  let h = IB.hs_of_mem mem in
  UV.length_eq uv;
  let ptr = addrs b + 16 * i in
  let heap' = update_heap128 ptr v heap in
  let prefix, _, suffix = UV.split_at_i uv i h in
  let s_down = prefix `Seq.append` (put128 v `Seq.append` suffix) in
  let s_f = get_seq_heap heap' addrs b in
  let h' = UV.upd h uv i v in
  // This is by definition of UV.upd, fetched from the friended definition
  assert (h' == DV.upd_seq h dv s_down);
  DV.upd_seq_spec h dv s_down;
  // assert (DV.as_seq h' dv == s_down);

  let aux1 (j:nat{j < i * 16}) : Lemma (Seq.index s_down j == Seq.index s_f j)
    = let base = j / 16 in
      let s_init = DV.as_seq h dv in

      calc (==) {
        Seq.index s_down j;
        ( == ) { FStar.Math.Lemmas.euclidean_division_definition j 16 }
        Seq.index s_down (base * 16 + j%16);
        ( == ) {  assert (base * 16 + 16 <= Seq.length s_down);
                  Seq.lemma_index_slice s_down (base*16) (base*16 + 16) (j % 16)
                } // True by slice properties
        Seq.index (Seq.slice s_down (base*16) (base*16 + 16)) (j%16);
        ( == ) {
          UV.sel_upd uv i base v h;
          // assert (UV.sel h uv base == UV.sel h' uv base);
          UV.get_sel h uv base;
          UV.get_sel h' uv base;
          // With the injectivity of get128, which we get from get128 and put128 being inverses,
          // we get the following
          assert (Seq.equal (Seq.slice s_init (base*16) (base*16+16)) (Seq.slice s_down (base*16) (base*16+16))) }
        Seq.index (Seq.slice s_init (base*16) (base*16+16)) (j%16);
        ( == ) { assert (base * 16 + 16 <= Seq.length s_init);
                  Seq.lemma_index_slice s_init (base*16) (base*16 + 16) (j % 16)
                } // True by slice properties
        Seq.index s_init (base * 16 + j%16);
        ( == ) { FStar.Math.Lemmas.euclidean_division_definition j 16 }
        Seq.index s_init j;
        ( == ) { assert (Seq.index s_init j == UInt8.uint_to_t (heap.[addrs b + j])) }
        UInt8.uint_to_t (heap.[addrs b + j]); // True by correct_down_p
        ( == ) { Vale.X64.Bytes_Semantics.frame_update_heap128 ptr v heap } // True by frame_update
        UInt8.uint_to_t (heap'.[addrs b + j]);
        ( == ) { } // True by definition of get_seq_heap
        Seq.index s_f j;
      }
  in let aux2(j:nat{j >= i * 16 /\ j < i * 16 + 16}) : Lemma (Seq.index s_down j == Seq.index s_f j)
    = UV.sel_upd uv i i v h;
      // assert (UV.sel h' uv i == v);
      UV.get_sel h' uv i;
      // assert (Vale.Interop.Views.get128 (Seq.slice s_down (i*16) (i*16+16)) = v);
      Vale.X64.Bytes_Semantics.correct_update_get128 ptr v heap;
      // assert (get_heap_val128 ptr heap' = v);
      let k = j - i * 16 in
      get128_aux ptr heap' v k;
      // assert (heap'.[ptr + k] = UInt8.v (Seq.index (put128 v) k));
      map_aux (ptr + k) (addrs b + j) (UInt8.v (Seq.index s_down j))  heap'
      // assert (heap'.[ptr + k] = heap'.[addrs b + j])
  in let aux3 (j:nat{j >= i * 16 + 16 /\ j < Seq.length s_down}) : Lemma (Seq.index s_down j == Seq.index s_f j)
    = let base = j / 16 in
      let s_init = DV.as_seq h dv in

      calc (==) {
        Seq.index s_down j;
        ( == ) { FStar.Math.Lemmas.euclidean_division_definition j 16 }
        Seq.index s_down (base * 16 + j%16);
        ( == ) {  assert (base * 16 + 16 <= Seq.length s_down);
                  Seq.lemma_index_slice s_down (base*16) (base*16 + 16) (j % 16)
                } // True by slice properties
        Seq.index (Seq.slice s_down (base*16) (base*16 + 16)) (j%16);
        ( == ) {
          UV.sel_upd uv i base v h;
          // assert (UV.sel h uv base == UV.sel h' uv base);
          UV.get_sel h uv base;
          UV.get_sel h' uv base;
          // With the injectivity of get128, which we get from get128 and put128 being inverses,
          // we get the following
          assert (Seq.equal (Seq.slice s_init (base*16) (base*16+16)) (Seq.slice s_down (base*16) (base*16+16))) }
        Seq.index (Seq.slice s_init (base*16) (base*16+16)) (j%16);
        ( == ) { assert (base * 16 + 16 <= Seq.length s_init);
                  Seq.lemma_index_slice s_init (base*16) (base * 16 + 16) (j % 16)
                } // True by slice properties
        Seq.index s_init (base * 16 + j%16);
        ( == ) { FStar.Math.Lemmas.euclidean_division_definition j 16 }
        Seq.index s_init j;
        ( == ) { assert (Seq.index s_init j == UInt8.uint_to_t (heap.[addrs b + j])) }
        UInt8.uint_to_t (heap.[addrs b + j]); // True by correct_down_p
        ( == ) { Vale.X64.Bytes_Semantics.frame_update_heap128 ptr v heap } // True by frame_update
        UInt8.uint_to_t (heap'.[addrs b + j]);
        ( == ) { } // True by definition of get_seq_heap
        Seq.index s_f j;
      }
  in
  Classical.forall_intro aux1;
  Classical.forall_intro aux2;
  Classical.forall_intro aux3;
  assert (Seq.equal s_down s_f)
