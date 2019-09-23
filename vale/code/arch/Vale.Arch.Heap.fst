module Vale.Arch.Heap
open FStar.Mul
open Vale.Interop
open Vale.Arch.HeapImpl
friend Vale.Arch.HeapImpl

let heap_impl = vale_heap_impl

let heap_get hi = hi.mh

let heap_upd hi mh' =
  mi_heap_upd hi mh'

let heap_of_interop ih = ValeHeap (down_mem ih) (Ghost.hide ih)
