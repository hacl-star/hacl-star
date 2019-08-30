module Vale.Arch.Heap
open Vale.Interop
open Vale.Arch.HeapImpl
friend Vale.Arch.HeapImpl

let heap_down = down_mem

let heap_impl = vale_heap_impl

let heap_get hi = hi.mh

let heap_new ih mh = ValeHeap mh (Ghost.hide ih)

let heap_upd hi mh' =
  mi_heap_upd hi mh'
