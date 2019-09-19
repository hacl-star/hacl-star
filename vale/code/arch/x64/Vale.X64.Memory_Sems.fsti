module Vale.X64.Memory_Sems

open FStar.Mul
open Vale.Def.Prop_s
open Vale.Arch.HeapImpl
open Vale.Arch.Heap
open Vale.Arch.MachineHeap_s
open Vale.X64.Machine_s
open Vale.X64.Memory
module S = Vale.X64.Machine_Semantics_s

val same_domain (h:vale_heap) (m:S.machine_heap) : prop0

val lemma_same_domains (h:vale_heap) (m1:S.machine_heap) (m2:S.machine_heap) : Lemma
  (requires same_domain h m1 /\ Set.equal (Map.domain m1) (Map.domain m2))
  (ensures same_domain h m2)

val get_heap (h:vale_heap) : GTot (m:S.machine_heap{same_domain h m})

val upd_heap (h:vale_heap) (m:S.machine_heap{is_machine_heap_update (get_heap h) m}) : GTot (h':vale_heap)

val lemma_upd_get_heap (h:vale_heap) : Lemma (upd_heap h (get_heap h) == h)
  [SMTPat (upd_heap h (get_heap h))]

val lemma_get_upd_heap (h:vale_heap) (m:S.machine_heap) : Lemma
  (requires is_machine_heap_update (get_heap h) m)
  (ensures get_heap (upd_heap h m) == m)

unfold let coerce (#b #a:Type) (x:a{a == b}) : b = x

val lemma_heap_get_heap (h:vale_heap_impl) : Lemma
  (vale_heap_impl == heap_impl /\ heap_get (coerce h) == get_heap (get_vale_heap h))
  [SMTPat (heap_get (coerce h))]

val lemma_heap_upd_heap (h:vale_heap_impl) (m:machine_heap) : Lemma
  (requires is_machine_heap_update (get_heap h) m)
  (ensures vale_heap_impl == heap_impl /\ heap_upd (coerce h) m == coerce (upd_heap (get_vale_heap h) m))
  [SMTPat (heap_upd (coerce h) m)]

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
