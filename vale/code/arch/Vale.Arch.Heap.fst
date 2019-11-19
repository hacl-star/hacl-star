module Vale.Arch.Heap
open FStar.Mul
open Vale.Interop
open Vale.Arch.HeapImpl
friend Vale.Arch.HeapImpl

let heap_impl = vale_full_heap

let heap_get hi = hi.v_h.mh

let heap_upd hi mh' =
  {v_h = mi_heap_upd hi.v_h mh'}

let heap_create_from_interop ih = {v_h = ValeHeap (down_mem ih) (Ghost.hide ih)}
