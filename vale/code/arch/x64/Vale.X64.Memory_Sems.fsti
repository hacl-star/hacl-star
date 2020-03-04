module Vale.X64.Memory_Sems

open FStar.Mul
open Vale.Def.Prop_s
open Vale.Def.Types_s
open Vale.Arch.Types
open Vale.Arch.HeapImpl
open Vale.Arch.Heap
open Vale.Arch.MachineHeap_s
open Vale.X64.Machine_s
open Vale.X64.Memory
open Vale.Lib.Seqs
module S = Vale.X64.Machine_Semantics_s
module Map16 = Vale.Lib.Map16

val same_domain (h:vale_heap) (m:S.machine_heap) : prop0

val lemma_same_domains (h:vale_heap) (m1:S.machine_heap) (m2:S.machine_heap) : Lemma
  (requires same_domain h m1 /\ Set.equal (Map.domain m1) (Map.domain m2))
  (ensures same_domain h m2)

val get_heap (h:vale_heap) : GTot (m:S.machine_heap{same_domain h m})

val upd_heap (h:vale_heap) (m:S.machine_heap{is_machine_heap_update (get_heap h) m}) : GTot (h':vale_heap)

//val lemma_upd_get_heap (h:vale_heap) : Lemma (upd_heap h (get_heap h) == h)
//  [SMTPat (upd_heap h (get_heap h))]

val lemma_get_upd_heap (h:vale_heap) (m:S.machine_heap) : Lemma
  (requires is_machine_heap_update (get_heap h) m)
  (ensures get_heap (upd_heap h m) == m)

unfold let coerce (#b #a:Type) (x:a{a == b}) : b = x

val lemma_heap_impl : squash (heap_impl == vale_full_heap)

val lemma_heap_get_heap (h:vale_full_heap) : Lemma
  (heap_get (coerce h) == get_heap (get_vale_heap h))
  [SMTPat (heap_get (coerce h))]

val lemma_heap_taint (h:vale_full_heap) : Lemma
  (heap_taint (coerce h) == full_heap_taint h)
  [SMTPat (heap_taint (coerce h))]

let is_full_read (#t:base_typ) (h1 h2:vale_heap) (b:buffer t) (i:int) =
  buffer_addr b h1 == buffer_addr b h2 /\
  buffer_read b i h1 == buffer_read b i h2 /\
  valid_buffer_read h1 b i  // needed to trigger "index = i" in valid_mem_operand64/valid_mem_operand128

let is_full_update (vfh:vale_full_heap) (h':vale_heap) (hid:heaplet_id) (mh':machine_heap) (mt':memtaint) =
  is_machine_heap_update (heap_get (coerce vfh)) mh' /\ (
    let vfh' = coerce (heap_upd (coerce vfh) mh' mt') in
    mem_inv vfh' /\
    vfh'.vf_layout == vfh.vf_layout /\
    vfh'.vf_heaplets == Map16.upd vfh.vf_heaplets hid h'
  )

val create_heaplets (buffers:list buffer_info) (h1:vale_full_heap) : GTot vale_full_heap

val lemma_create_heaplets (buffers:list buffer_info) (h1:vale_full_heap) : Lemma
  (requires
    mem_inv h1 /\
    is_initial_heap h1.vf_layout h1.vf_heap /\
    init_heaplets_req h1.vf_heap (list_to_seq buffers)
  )
  (ensures (
    let h2 = create_heaplets buffers h1 in
    let bs = list_to_seq buffers in
    h1.vf_heap == h2.vf_heap /\
    h1.vf_heaplets == h2.vf_heaplets /\
    h1.vf_layout.vl_taint == h2.vf_layout.vl_taint /\
    get_heaplet_id h1.vf_heap == None /\
    layout_heaplets_initialized h2.vf_layout.vl_inner /\
    layout_modifies_loc h2.vf_layout.vl_inner == loc_mutable_buffers buffers /\
    layout_old_heap h2.vf_layout.vl_inner == h1.vf_heap /\
    layout_buffers h2.vf_layout.vl_inner == bs /\
    (forall (i:nat).{:pattern Seq.index bs i} i < Seq.length bs ==> (
      let Mkbuffer_info t b hid _ mut = Seq.index bs i in
      valid_layout_buffer_id t b h2.vf_layout (Some hid) false /\
      valid_layout_buffer_id t b h2.vf_layout (Some hid) (mut = Mutable))) /\
    (forall (i:heaplet_id).{:pattern Map16.sel h2.vf_heaplets i}
      get_heaplet_id (Map16.sel h2.vf_heaplets i) == Some i /\
      heaps_match bs h1.vf_layout.vl_taint h1.vf_heap (Map16.sel h2.vf_heaplets i) i) /\
    mem_inv h2
  ))

val destroy_heaplets (h1:vale_full_heap) : GTot vale_full_heap

val lemma_destroy_heaplets (h1:vale_full_heap) : Lemma
  (requires
    mem_inv h1 /\
    layout_heaplets_initialized h1.vf_layout.vl_inner
  )
  (ensures (
    let h2 = destroy_heaplets h1 in
    heap_get (coerce h1) == heap_get (coerce h2) /\
    heap_taint (coerce h1) == heap_taint (coerce h2) /\
    h1.vf_heap == h2.vf_heap /\
    h1.vf_heaplets == h2.vf_heaplets /\
    h1.vf_layout.vl_taint == h2.vf_layout.vl_taint /\
    get_heaplet_id h1.vf_heap == None /\
    modifies (layout_modifies_loc h1.vf_layout.vl_inner) (layout_old_heap h1.vf_layout.vl_inner) h2.vf_heap /\
    (forall (i:heaplet_id).{:pattern Map16.sel h1.vf_heaplets i}
      heaps_match (layout_buffers h1.vf_layout.vl_inner) h1.vf_layout.vl_taint h2.vf_heap
        (Map16.sel h1.vf_heaplets i) i) /\
    (mem_inv h1 ==> mem_inv h2)
  ))

//let heap_upd_def (hi:vale_full_heap) (h':vale_heap) (mt':memTaint_t) : vale_full_heap =
//  { hi with
//    vf_layout = {hi.vf_layout with vl_taint = mt'};
//    vf_heap = h';
//    vf_heaplets = Map16.upd hi.vf_heaplets 0 h';
//  }

//val lemma_heap_upd_heap (h:vale_full_heap) (mh:machine_heap) (mt:memTaint_t) : Lemma
//  (requires is_machine_heap_update (get_heap (get_vale_heap h)) mh)
//  (ensures heap_upd (coerce h) mh mt == coerce (heap_upd_def h (upd_heap h.vf_heap mh) mt))
//  [SMTPat (heap_upd (coerce h) mh mt)]

val bytes_valid64 (i:int) (m:vale_heap) : Lemma
  (requires valid_mem64 i m)
  (ensures S.valid_addr64 i (get_heap m))
  [SMTPat (S.valid_addr64 i (get_heap m))]

val bytes_valid128 (i:int) (m:vale_heap) : Lemma
  (requires valid_mem128 i m)
  (ensures S.valid_addr128 i (get_heap m))
  [SMTPat (S.valid_addr128 i (get_heap m))]

val equiv_load_mem64 (ptr:int) (m:vale_heap) : Lemma
  (requires valid_mem64 ptr m)
  (ensures load_mem64 ptr m == S.get_heap_val64 ptr (get_heap m))

//val low_lemma_valid_mem64: b:buffer64 -> i:nat -> h:vale_heap -> Lemma
//  (requires
//    i < Seq.length (buffer_as_seq h b) /\
//    buffer_readable h b
//  )
//  (ensures
//    S.valid_addr64 (buffer_addr b h + scale8 i) (get_heap h)
//  )

//val low_lemma_load_mem64 : b:buffer64 -> i:nat -> h:vale_heap -> Lemma
//  (requires
//    i < Seq.length (buffer_as_seq h b) /\
//    buffer_readable h b
//  )
//  (ensures
//    S.get_heap_val64 (buffer_addr b h + scale8 i) (get_heap h) == buffer_read b i h
//  )

//val same_domain_update64: b:buffer64 -> i:nat -> v:nat64 -> h:vale_heap -> Lemma
//  (requires
//    i < Seq.length (buffer_as_seq h b) /\
//    buffer_readable h b
//  )
//  (ensures same_domain h (S.update_heap64 (buffer_addr b h + scale8 i) v (get_heap h)))

val low_lemma_load_mem64_full (b:buffer64) (i:nat) (vfh:vale_full_heap) (t:taint) (hid:heaplet_id) : Lemma
  (requires (
    let (h, mt) = (Map16.get vfh.vf_heaplets hid, vfh.vf_layout.vl_taint) in
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b /\
    valid_layout_buffer b vfh.vf_layout h false /\
    valid_taint_buf64 b h mt t /\
    mem_inv vfh
  ))
  (ensures (
    let (h, mt) = (Map16.get vfh.vf_heaplets hid, vfh.vf_layout.vl_taint) in
    let ptr = buffer_addr b h + scale8 i in
    is_full_read vfh.vf_heap h b i /\
//    valid_addr64 ptr (heap_get (coerce vfh)) /\
    valid_mem64 ptr vfh.vf_heap /\
    valid_taint_buf64 b vfh.vf_heap mt t
  ))

val low_lemma_store_mem64 (b:buffer64) (i:nat) (v:nat64) (h:vale_heap) : Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b /\
    buffer_writeable b
  )
  (ensures (
    let m = S.update_heap64 (buffer_addr b h + scale8 i) v (get_heap h) in
    is_machine_heap_update (get_heap h) m /\ upd_heap h m == buffer_write b i v h
  ))

val low_lemma_store_mem64_full (b:buffer64) (i:nat) (v:nat64) (vfh:vale_full_heap) (t:taint) (hid:heaplet_id) : Lemma
  (requires (
    let (h, mt) = (Map16.get vfh.vf_heaplets hid, vfh.vf_layout.vl_taint) in
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b /\
    buffer_writeable b /\
    valid_layout_buffer b vfh.vf_layout h true /\
    valid_taint_buf64 b h mt t /\
    mem_inv vfh
  ))
  (ensures (
    let h = Map16.get vfh.vf_heaplets hid in
    let h' = buffer_write b i v h in
    let ptr = buffer_addr b h + scale8 i in
    buffer_addr b vfh.vf_heap == buffer_addr b h /\
    valid_addr64 ptr (heap_get (coerce vfh)) /\
    is_full_update vfh h' hid
      (S.update_heap64 ptr v (heap_get (coerce vfh)))
      (S.update_n ptr 8 (heap_taint (coerce vfh)) t)
  ))

val equiv_load_mem128 (ptr:int) (m:vale_heap) : Lemma
  (requires valid_mem128 ptr m)
  (ensures load_mem128 ptr m == S.get_heap_val128 ptr (get_heap m))

//val same_domain_update128: b:buffer128 -> i:nat -> v:quad32 -> h:vale_heap -> Lemma
//  (requires
//    i < Seq.length (buffer_as_seq h b) /\
//    buffer_readable h b
//  )
//  (ensures same_domain h (S.update_heap128 (buffer_addr b h + scale16 i) v (get_heap h)))

val low_lemma_load_mem128_full (b:buffer128) (i:nat) (vfh:vale_full_heap) (t:taint) (hid:heaplet_id) : Lemma
  (requires (
    let (h, mt) = (Map16.get vfh.vf_heaplets hid, vfh.vf_layout.vl_taint) in
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b /\
    valid_layout_buffer b vfh.vf_layout h false /\
    valid_taint_buf128 b h mt t /\
    mem_inv vfh
  ))
  (ensures (
    let (h, mt) = (Map16.get vfh.vf_heaplets hid, vfh.vf_layout.vl_taint) in
    let ptr = buffer_addr b h + scale16 i in
    is_full_read vfh.vf_heap h b i /\
    valid_mem128 ptr vfh.vf_heap /\
    valid_taint_buf128 b vfh.vf_heap mt t
  ))

val low_lemma_store_mem128 (b:buffer128) (i:nat) (v:quad32) (h:vale_heap) : Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b /\
    buffer_writeable b
  )
  (ensures (
    let m = S.update_heap128 (buffer_addr b h + scale16 i) v (get_heap h) in
    is_machine_heap_update (get_heap h) m /\ upd_heap h m == buffer_write b i v h
  ))

val low_lemma_store_mem128_full (b:buffer128) (i:nat) (v:quad32) (vfh:vale_full_heap) (t:taint) (hid:heaplet_id) : Lemma
  (requires (
    let (h, mt) = (Map16.get vfh.vf_heaplets hid, vfh.vf_layout.vl_taint) in
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b /\
    buffer_writeable b /\
    valid_layout_buffer b vfh.vf_layout h true /\
    valid_taint_buf128 b h mt t /\
    mem_inv vfh
  ))
  (ensures (
    let h = Map16.get vfh.vf_heaplets hid in
    let ptr = buffer_addr b h + scale16 i in
    buffer_addr b vfh.vf_heap == buffer_addr b h /\
    valid_addr128 ptr (heap_get (coerce vfh)) /\
    is_full_update vfh (buffer_write b i v h) hid
      (S.update_heap128 ptr v (heap_get (coerce vfh)))
      (S.update_n ptr 16 (heap_taint (coerce vfh)) t)
  ))

val low_lemma_valid_mem128_64 (b:buffer128) (i:nat) (h:vale_heap) : Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b
  )
  (ensures
    S.valid_addr64 (buffer_addr b h + scale16 i) (get_heap h) /\
    S.valid_addr64 (buffer_addr b h + scale16 i + 8) (get_heap h)
  )

val low_lemma_load_mem128_lo64 (b:buffer128) (i:nat) (h:vale_heap) : Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b
  )
  (ensures
    S.get_heap_val64 (buffer_addr b h + scale16 i) (get_heap h) ==
      lo64 (buffer_read b i h)
  )

val low_lemma_load_mem128_hi64 (b:buffer128) (i:nat) (h:vale_heap) : Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b
  )
  (ensures
    S.get_heap_val64 (buffer_addr b h + scale16 i + 8) (get_heap h) ==
      hi64 (buffer_read b i h)
  )

//val same_domain_update128_64 (b:buffer128) (i:nat) (v:nat64) (h:vale_heap) : Lemma
//  (requires
//    i < Seq.length (buffer_as_seq h b) /\
//    buffer_readable h b
//  )
//  (ensures
//    same_domain h (S.update_heap64 (buffer_addr b h + scale16 i) v (get_heap h)) /\
//    same_domain h (S.update_heap64 (buffer_addr b h + scale16 i + 8) v (get_heap h))
//  )

val low_lemma_load_mem128_lo_hi_full (b:buffer128) (i:nat) (vfh:vale_full_heap) (t:taint) (hid:heaplet_id) : Lemma
  (requires (
    let (h, mt) = (Map16.get vfh.vf_heaplets hid, vfh.vf_layout.vl_taint) in
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b /\
    valid_layout_buffer b vfh.vf_layout h false /\
    valid_taint_buf128 b h mt t /\
    mem_inv vfh
  ))
  (ensures (
    let (h, mt) = (Map16.get vfh.vf_heaplets hid, vfh.vf_layout.vl_taint) in
    let ptr = buffer_addr b h + scale16 i in
    is_full_read vfh.vf_heap h b i /\
    valid_addr64 ptr (heap_get (coerce vfh)) /\
    valid_addr64 (ptr + 8) (heap_get (coerce vfh)) /\
    valid_mem128 ptr vfh.vf_heap /\
    valid_taint_buf128 b vfh.vf_heap mt t
  ))

val low_lemma_store_mem128_lo64 (b:buffer128) (i:nat) (v:nat64) (h:vale_heap) : Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b /\
    buffer_writeable b
  )
  (ensures (
    let v' = insert_nat64 (buffer_read b i h) v 0 in
    let m = S.update_heap64 (buffer_addr b h + scale16 i) v (get_heap h) in
    is_machine_heap_update (get_heap h) m /\ upd_heap h m == buffer_write b i v' h
  ))

val low_lemma_store_mem128_lo64_full (b:buffer128) (i:nat) (v:nat64) (vfh:vale_full_heap) (t:taint) (hid:heaplet_id) : Lemma
  (requires (
    let (h, mt) = (Map16.get vfh.vf_heaplets hid, vfh.vf_layout.vl_taint) in
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b /\
    buffer_writeable b /\
    valid_layout_buffer b vfh.vf_layout h true /\
    valid_taint_buf128 b h mt t /\
    mem_inv vfh
  ))
  (ensures (
    let h = Map16.get vfh.vf_heaplets hid in
    let ptr = buffer_addr b h + scale16 i in
    let v' = insert_nat64 (buffer_read b i h) v 0 in
    buffer_addr b vfh.vf_heap == buffer_addr b h /\
    valid_addr64 ptr (heap_get (coerce vfh)) /\
    is_full_update vfh (buffer_write b i v' h) hid
      (S.update_heap64 ptr v (heap_get (coerce vfh)))
      (S.update_n ptr 8 (heap_taint (coerce vfh)) t)
  ))

val low_lemma_store_mem128_hi64 (b:buffer128) (i:nat) (v:nat64) (h:vale_heap) : Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b /\
    buffer_writeable b
  )
  (ensures (
    let v' = insert_nat64 (buffer_read b i h) v 1 in
    let m = S.update_heap64 (buffer_addr b h + scale16 i + 8) v (get_heap h) in
    is_machine_heap_update (get_heap h) m /\ upd_heap h m == buffer_write b i v' h)
  )

val low_lemma_store_mem128_hi64_full (b:buffer128) (i:nat) (v:nat64) (vfh:vale_full_heap) (t:taint) (hid:heaplet_id) : Lemma
  (requires (
    let (h, mt) = (Map16.get vfh.vf_heaplets hid, vfh.vf_layout.vl_taint) in
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b /\
    buffer_writeable b /\
    valid_layout_buffer b vfh.vf_layout h true /\
    valid_taint_buf128 b h mt t /\
    mem_inv vfh
  ))
  (ensures (
    let h = Map16.get vfh.vf_heaplets hid in
    let ptr = buffer_addr b h + scale16 i + 8 in
    let v' = insert_nat64 (buffer_read b i h) v 1 in
    buffer_addr b vfh.vf_heap == buffer_addr b h /\
    valid_addr64 ptr (heap_get (coerce vfh)) /\
    is_full_update vfh (buffer_write b i v' h) hid
      (S.update_heap64 ptr v (heap_get (coerce vfh)))
      (S.update_n ptr 8 (heap_taint (coerce vfh)) t)
  ))
