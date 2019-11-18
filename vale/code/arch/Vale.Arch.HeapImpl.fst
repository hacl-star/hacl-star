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
    vale_heap

let _ih (vh:vale_heap) : GTot interop_heap = Ghost.reveal vh.ih

let mi_heap_upd (vh:vale_heap) (mh':machine_heap) : Pure vale_heap
  (requires is_machine_heap_update vh.mh mh')
  (ensures fun vh' -> vh'.mh == mh')
  =
  up_down_identity (_ih vh) mh';
  ValeHeap mh' (Ghost.hide (up_mem mh' (_ih vh)))

