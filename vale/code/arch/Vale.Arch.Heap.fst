module Vale.Arch.Heap
open FStar.Mul
open Vale.Interop
open Vale.Arch.HeapImpl
module Map16 = Vale.Lib.Map16
friend Vale.Arch.HeapImpl

let heap_impl = vale_full_heap

let heap_get hi = hi.vf_heap.mh

let heap_taint hi = hi.vf_layout.vl_taint

let heap_upd hi mh' mt' =
  let h' = mi_heap_upd hi.vf_heap mh' in
  let hh' = ValeHeap h'.mh h'.ih (Map16.sel hi.vf_heaplets 0).heapletId in
  {
    vf_layout = {hi.vf_layout with vl_taint = mt'};
    vf_heap = h';
    vf_heaplets = Map16.upd hi.vf_heaplets 0 hh';
  }

let heap_create_machine ih =
  down_mem ih

let heap_create_impl ih mt =
  let vh = ValeHeap (down_mem ih) (Ghost.hide ih) None in
  let vh4 = ((vh, vh), (vh, vh)) in
  let vh16 = ((vh4, vh4), (vh4, vh4)) in
  let layout_inner = {
    vl_old_heap = vh;
  } in
  let layout = {vl_inner = layout_inner; vl_taint = mt;} in
  {
    vf_layout = layout;
    vf_heap = vh;
    vf_heaplets = Map16.upd vh16 0 vh;
  }
