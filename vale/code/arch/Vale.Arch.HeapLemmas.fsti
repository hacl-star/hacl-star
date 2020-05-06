module Vale.Arch.HeapLemmas
open FStar.Mul
open Vale.Arch.HeapTypes_s
open Vale.Arch.MachineHeap_s
open Vale.Arch.Heap
open Vale.Arch.HeapImpl

val lemma_heap_impl : squash (heap_impl == vale_full_heap)

val empty_vale_heap_layout_inner (h:vale_heap) : vale_heap_layout_inner
val empty_vale_heaplets (h:vale_heap) : vale_heaplets

let heap_ignore_ghost (vfh:vale_full_heap) : vale_full_heap =
  {vfh with
    vf_layout = {vfh.vf_layout with vl_inner = empty_vale_heap_layout_inner vfh.vf_heap};
    vf_heaplets = empty_vale_heaplets vfh.vf_heap;
  }

unfold let coerce (#b #a:Type) (x:a{a == b}) : b = x

let heap_ignore_ghost_machine (h:heap_impl) : heap_impl =
  coerce (heap_ignore_ghost (coerce h))

val lemma_heap_ignore_ghost_machine (h1 h2:heap_impl) : Lemma
  (requires heap_ignore_ghost_machine h1 == heap_ignore_ghost_machine h2)
  (ensures
    heap_get h1 == heap_get h2 /\
    heap_taint h1 == heap_taint h2 /\
    (forall (mh':machine_heap) (mt':memTaint_t).{:pattern heap_upd h1 mh' mt'; heap_upd h2 mh' mt'}
      is_machine_heap_update (heap_get h1) mh' /\ is_machine_heap_update (heap_get h2) mh' ==>
      heap_ignore_ghost_machine (heap_upd h1 mh' mt') == heap_ignore_ghost_machine (heap_upd h2 mh' mt')))

