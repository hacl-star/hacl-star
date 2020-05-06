module Vale.Arch.Heap
open FStar.Mul
open Vale.Def.Words_s
open Vale.Arch.HeapTypes_s
open Vale.Arch.MachineHeap_s
open Vale.Interop.Heap_s

// This module defines the heap interface, called heap_impl, seen by Vale.X64.Machine_Semantics_s.
// The interface is a trusted specification, but its implementation is defined in untrusted code.

val heap_impl : Type u#1

val heap_get (hi:heap_impl) : machine_heap

val heap_taint (hi:heap_impl) : memTaint_t

val heap_upd (hi:heap_impl) (mh':machine_heap) (mt':memTaint_t) : Pure heap_impl
  (requires is_machine_heap_update (heap_get hi) mh')
  (ensures fun hi -> heap_get hi == mh' /\ heap_taint hi == mt')

val heap_create_machine (ih:interop_heap) : Ghost machine_heap
  (requires True)
  (ensures fun mh -> correct_down ih mh)

val heap_create_impl (ih:interop_heap) (mt:memTaint_t) : Ghost heap_impl
  (requires True)
  (ensures fun hi -> heap_get hi == heap_create_machine ih /\ heap_taint hi == mt)
