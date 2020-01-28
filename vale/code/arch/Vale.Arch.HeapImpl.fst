module Vale.Arch.HeapImpl
open FStar.Mul
open Vale.Interop
open Vale.Def.Words_s
open Vale.Arch.MachineHeap_s
open Vale.Interop.Heap_s
module DV = LowStar.BufferView.Down

let buffer t = (b:b8{DV.length (get_downview b.bsrc) % view_n t == 0})

noeq type vale_heap =
  | ValeHeap:
    mh:machine_heap ->
    ih:Ghost.erased interop_heap{mh == down_mem (Ghost.reveal ih)} ->
    heapletId:option heaplet_id ->
    vale_heap

noeq type vale_heap_layout_inner : Type u#1 = {
  vl_heaplets_initialized:bool;
  vl_heaplet_map:int -> option heaplet_id; // each address is owned by at most one heaplet
  vl_heaplet_sets:heaplet_id -> Set.set int; // addresses owned by each heaplet (redundant with vl_heaplet_map, but convenient)
  vl_old_heap:vale_heap;
  vl_buffers:Seq.seq buffer_info;
  vl_mod_loc:LowStar.Modifies.loc;
}

let empty_vale_heap_layout_inner (h:vale_heap) : vale_heap_layout_inner = {
  vl_heaplets_initialized = false;
  vl_heaplet_map = (fun _ -> None);
  vl_heaplet_sets = (fun _ -> Set.empty);
  vl_old_heap = h;
  vl_buffers = Seq.empty;
  vl_mod_loc = LowStar.Modifies.loc_none;
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

