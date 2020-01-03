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

let one_heaplet (ih:interop_heap) (id:option heaplet_id) : GTot vale_heap =
  let m = down_mem ih in
  let g = Ghost.hide ih in
  ValeHeap m g id

let rec make_heaplets (ih:interop_heap) (n:nat) : Ghost (Map16.map16 vale_heap)
  (requires n <= 16)
  (ensures fun h -> forall (i:nat).{:pattern Map16.sel h i} i < n ==> Map16.sel h i == one_heaplet ih (Some i))
  =
  let vh = one_heaplet ih None in
  let vh4 = ((vh, vh), (vh, vh)) in
  let vh16 = ((vh4, vh4), (vh4, vh4)) in
  if n = 0 then vh16 else
  Map16.upd (make_heaplets ih (n - 1)) (n - 1) (one_heaplet ih (Some (n - 1)))

let heap_create_impl ih mt =
  let vh = one_heaplet ih None in
  let layout_inner = {
    vl_n_buffers = 0;
    vl_old_heap = vh;
  } in
  let layout = {vl_inner = layout_inner; vl_taint = mt;} in
  {
    vf_layout = layout;
    vf_heap = vh;
    vf_heaplets = make_heaplets ih 16;
  }
