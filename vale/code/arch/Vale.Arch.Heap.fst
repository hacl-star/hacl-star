module Vale.Arch.Heap
open FStar.Mul
open Vale.Interop
open Vale.Arch.HeapImpl
module Map16 = Vale.Lib.Map16
friend Vale.Arch.HeapImpl

let heap_impl = vale_full_heap

let heap_get hi = hi.vf_heap.mh

let heap_taint hi = hi.vf_layout.vl_taint

// Update heaplet k with mh', but only for the addresses that k owns (addresses not owned by k remain unmodified)
let heaplet_upd_f (vfh:vale_full_heap) (mh':machine_heap) (k:heaplet_id) : vale_heap =
  let hk = Map16.sel vfh.vf_heaplets k in
  let mhk = hk.mh in
  let dom_upd = Set.intersect (vfh.vf_layout.vl_inner.vl_heaplet_sets k) (Map.domain mhk) in
  let mhk' = Map.concat mhk (Map.restrict dom_upd mh') in
  mi_heap_upd hk mhk'

let heap_upd hi mh' mt' =
  let h' = mi_heap_upd hi.vf_heap mh' in
  let hs' = Map16.init vale_heap (heaplet_upd_f hi mh') in
  {
    vf_layout = {hi.vf_layout with vl_taint = mt'};
    vf_heap = h';
    vf_heaplets = hs';
  }

let heap_create_machine ih =
  down_mem ih

let one_heaplet (ih:interop_heap) (id:option heaplet_id) : GTot vale_heap =
  let m = down_mem ih in
  let g = Ghost.hide ih in
  ValeHeap m g id

let heap_create_impl ih mt =
  let vh = one_heaplet ih None in
  let layout = {vl_inner = empty_vale_heap_layout_inner vh; vl_taint = mt;} in
  {
    vf_layout = layout;
    vf_heap = vh;
    vf_heaplets = empty_vale_heaplets vh;
  }
