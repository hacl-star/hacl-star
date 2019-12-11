module Vale.X64.Memory_Sems

open FStar.Mul
open Vale.Def.Prop_s
open Vale.Arch.HeapImpl
open Vale.Arch.Heap
open Vale.Arch.MachineHeap_s
open Vale.X64.Machine_s
open Vale.X64.Memory
module S = Vale.X64.Machine_Semantics_s
module Map16 = Vale.Lib.Map16

val same_domain (h:vale_heap) (m:S.machine_heap) : prop0

val lemma_same_domains (h:vale_heap) (m1:S.machine_heap) (m2:S.machine_heap) : Lemma
  (requires same_domain h m1 /\ Set.equal (Map.domain m1) (Map.domain m2))
  (ensures same_domain h m2)

val reveal_mem_inv (_:unit) : Lemma
  (ensures (forall (h:vale_full_heap).{:pattern (mem_inv h)}
    mem_inv h <==> h.vf_heap == Map16.sel h.vf_heaplets 0))

val get_heap (h:vale_heap) : GTot (m:S.machine_heap{same_domain h m})

val upd_heap (h:vale_heap) (m:S.machine_heap{is_machine_heap_update (get_heap h) m}) : GTot (h':vale_heap)

val lemma_upd_get_heap (h:vale_heap) : Lemma (upd_heap h (get_heap h) == h)
  [SMTPat (upd_heap h (get_heap h))]

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

let heap_upd_def (hi:vale_full_heap) (h':vale_heap) (mt':memTaint_t) : vale_full_heap =
  { hi with
    vf_layout = {hi.vf_layout with vl_taint = mt'};
    vf_heap = h';
    vf_heaplets = Map16.upd hi.vf_heaplets 0 h';
  }

val lemma_heap_upd_heap (h:vale_full_heap) (mh:machine_heap) (mt:memTaint_t) : Lemma
  (requires is_machine_heap_update (get_heap (get_vale_heap h)) mh)
  (ensures heap_upd (coerce h) mh mt == coerce (heap_upd_def h (upd_heap h.vf_heap mh) mt))
  [SMTPat (heap_upd (coerce h) mh mt)]

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
//    S.valid_addr64 (buffer_addr b h + 8 * i) (get_heap h)
//  )

//val low_lemma_load_mem64 : b:buffer64 -> i:nat -> h:vale_heap -> Lemma
//  (requires
//    i < Seq.length (buffer_as_seq h b) /\
//    buffer_readable h b
//  )
//  (ensures
//    S.get_heap_val64 (buffer_addr b h + 8 * i) (get_heap h) == buffer_read b i h
//  )

//val same_domain_update64: b:buffer64 -> i:nat -> v:nat64 -> h:vale_heap -> Lemma
//  (requires
//    i < Seq.length (buffer_as_seq h b) /\
//    buffer_readable h b
//  )
//  (ensures same_domain h (S.update_heap64 (buffer_addr b h + 8 * i) v (get_heap h)))

val low_lemma_store_mem64 (b:buffer64) (i:nat) (v:nat64) (h:vale_heap) : Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b /\
    buffer_writeable b
  )
  (ensures (
    let m = S.update_heap64 (buffer_addr b h + 8 * i) v (get_heap h) in
    is_machine_heap_update (get_heap h) m /\ upd_heap h m == buffer_write b i v h
  ))

val low_lemma_store_mem64_taint (b:buffer64) (i:nat) (v:nat64) (h:vale_heap) (mt:memtaint) (t:taint) : Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b /\
    buffer_writeable b /\
    valid_taint_buf64 b h mt t
  )
  (ensures (
    let ptr = buffer_addr b h + 8 * i in
    let m = S.update_heap64 ptr v (get_heap h) in
    is_machine_heap_update (get_heap h) m /\
    upd_heap h m == buffer_write b i v h /\
    S.update_n ptr 8 mt t == mt
  ))

val equiv_load_mem128 (ptr:int) (m:vale_heap) : Lemma
  (requires valid_mem128 ptr m)
  (ensures load_mem128 ptr m == S.get_heap_val128 ptr (get_heap m))

//val same_domain_update128: b:buffer128 -> i:nat -> v:quad32 -> h:vale_heap -> Lemma
//  (requires
//    i < Seq.length (buffer_as_seq h b) /\
//    buffer_readable h b
//  )
//  (ensures same_domain h (S.update_heap128 (buffer_addr b h + 16 * i) v (get_heap h)))

val low_lemma_store_mem128 (b:buffer128) (i:nat) (v:quad32) (h:vale_heap) : Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b /\
    buffer_writeable b
  )
  (ensures (
    let m = S.update_heap128 (buffer_addr b h + 16 * i) v (get_heap h) in
    is_machine_heap_update (get_heap h) m /\ upd_heap h m == buffer_write b i v h
  ))

val low_lemma_store_mem128_taint (b:buffer128) (i:nat) (v:quad32) (h:vale_heap) (mt:memtaint) (t:taint) : Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b /\
    buffer_writeable b /\
    valid_taint_buf128 b h mt t
  )
  (ensures (
    let ptr = buffer_addr b h + 16 * i in
    let m = S.update_heap128 ptr v (get_heap h) in
    is_machine_heap_update (get_heap h) m /\
    upd_heap h m == buffer_write b i v h /\
    S.update_n ptr 16 mt t == mt
  ))

val low_lemma_valid_mem128_64: b:buffer128 -> i:nat -> h:vale_heap -> Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b
  )
  (ensures
    S.valid_addr64 (buffer_addr b h + 16 * i) (get_heap h) /\
    S.valid_addr64 (buffer_addr b h + 16 * i + 8) (get_heap h)
  )

open Vale.Arch.Types

val low_lemma_load_mem128_lo64 : b:buffer128 -> i:nat -> h:vale_heap -> Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b
  )
  (ensures
    S.get_heap_val64 (buffer_addr b h + 16 * i) (get_heap h) ==
      lo64 (buffer_read b i h)
  )

val low_lemma_load_mem128_hi64 : b:buffer128 -> i:nat -> h:vale_heap -> Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b
  )
  (ensures
    S.get_heap_val64 (buffer_addr b h + 16 * i + 8) (get_heap h) ==
      hi64 (buffer_read b i h)
  )

//val same_domain_update128_64: b:buffer128 -> i:nat -> v:nat64 -> h:vale_heap -> Lemma
//  (requires
//    i < Seq.length (buffer_as_seq h b) /\
//    buffer_readable h b
//  )
//  (ensures
//    same_domain h (S.update_heap64 (buffer_addr b h + 16 * i) v (get_heap h)) /\
//    same_domain h (S.update_heap64 (buffer_addr b h + 16 * i + 8) v (get_heap h))
//  )

val low_lemma_store_mem128_lo64 : b:buffer128 -> i:nat-> v:nat64 -> h:vale_heap -> Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b /\
    buffer_writeable b
  )
  (ensures (
    let v' = insert_nat64_opaque (buffer_read b i h) v 0 in
    let m = S.update_heap64 (buffer_addr b h + 16 * i) v (get_heap h) in
    is_machine_heap_update (get_heap h) m /\ upd_heap h m == buffer_write b i v' h)
  )

val low_lemma_store_mem128_lo64_taint (b:buffer128) (i:nat) (v:nat64) (h:vale_heap) (mt:memtaint) (t:taint) : Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b /\
    buffer_writeable b /\
    valid_taint_buf128 b h mt t
  )
  (ensures (
    let ptr = buffer_addr b h + 16 * i in
    let v' = insert_nat64_opaque (buffer_read b i h) v 0 in
    let m = S.update_heap64 ptr v (get_heap h) in
    is_machine_heap_update (get_heap h) m /\
    upd_heap h m == buffer_write b i v' h /\
    S.update_n ptr 8 mt t == mt
  ))

val low_lemma_store_mem128_hi64 : b:buffer128 -> i:nat-> v:nat64 -> h:vale_heap -> Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b /\
    buffer_writeable b
  )
  (ensures (
    let v' = insert_nat64_opaque (buffer_read b i h) v 1 in
    let m = S.update_heap64 (buffer_addr b h + 16 * i + 8) v (get_heap h) in
    is_machine_heap_update (get_heap h) m /\ upd_heap h m == buffer_write b i v' h)
  )

val low_lemma_store_mem128_hi64_taint (b:buffer128) (i:nat) (v:nat64) (h:vale_heap) (mt:memtaint) (t:taint) : Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b /\
    buffer_writeable b /\
    valid_taint_buf128 b h mt t
  )
  (ensures (
    let ptr = buffer_addr b h + 16 * i + 8 in
    let v' = insert_nat64_opaque (buffer_read b i h) v 1 in
    let m = S.update_heap64 ptr v (get_heap h) in
    is_machine_heap_update (get_heap h) m /\
    upd_heap h m == buffer_write b i v' h /\
    S.update_n ptr 8 mt t == mt
  ))
