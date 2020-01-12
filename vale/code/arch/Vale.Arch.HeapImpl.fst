module Vale.Arch.HeapImpl
open FStar.Mul
open Vale.Interop
open Vale.Def.Words_s
open Vale.Arch.MachineHeap_s
open Vale.Interop.Heap_s

noeq type vale_heap =
  | ValeHeap:
    mh:machine_heap ->
    ih:Ghost.erased interop_heap{mh == down_mem (Ghost.reveal ih)} ->
    heapletId:option heaplet_id ->
    vale_heap

noeq type vale_heap_layout_inner : Type u#1 = {
  vl_n_buffers:nat;
  vl_old_heap:vale_heap;
}

let empty_vale_heap_layout_inner (h:vale_heap) : vale_heap_layout_inner =
  {
    vl_n_buffers = 0;
    vl_old_heap = h;
  }

let empty_heaplet (h:vale_heap) (n:nat{n < 16}) : vale_heap =
  let ValeHeap mh ih _ = h in ValeHeap mh ih (Some n)

let empty_vale_heaplets (h:vale_heap) : vale_heaplets =
  Map16.init vale_heap (empty_heaplet h)

let _ih (vh:vale_heap) : GTot interop_heap = Ghost.reveal vh.ih

let mi_heap_upd (vh:vale_heap) (mh':machine_heap) : Pure vale_heap
  (requires is_machine_heap_update vh.mh mh')
  (ensures fun vh' -> vh'.mh == mh')
  =
  up_down_identity (_ih vh) mh';
  ValeHeap mh' (Ghost.hide (up_mem mh' (_ih vh))) vh.heapletId

