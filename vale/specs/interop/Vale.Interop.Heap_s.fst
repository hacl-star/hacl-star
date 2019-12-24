module Vale.Interop.Heap_s
open FStar.Mul
open Vale.Def.Opaque_s
open Vale.Def.Words_s
open Vale.Arch.MachineHeap_s
include Vale.Interop.Types
module L = FStar.List.Tot
module B = LowStar.Buffer
module DV = LowStar.BufferView.Down
module HS = FStar.HyperStack

[@__reduce__]
let disjoint_or_eq_b8 (ptr1 ptr2:b8) =
  B.loc_disjoint (B.loc_buffer ptr1.bsrc) (B.loc_buffer ptr2.bsrc) \/
  ptr1 == ptr2

let list_disjoint_or_eq_def (ptrs:list b8) =
  forall (p1 p2:b8).{:pattern (L.memP p1 ptrs); (L.memP p2 ptrs)}
    L.memP p1 ptrs /\
    L.memP p2 ptrs ==> disjoint_or_eq_b8 p1 p2
[@"opaque_to_smt"] let list_disjoint_or_eq = opaque_make list_disjoint_or_eq_def
irreducible let list_disjoint_or_eq_reveal = opaque_revealer (`%list_disjoint_or_eq) list_disjoint_or_eq list_disjoint_or_eq_def

unfold
let list_live mem (ptrs:list b8) =
  forall (p:b8).{:pattern (L.memP p ptrs)} L.memP p ptrs ==> B.live mem p.bsrc

assume val global_addrs_map : addr_map

let mk_addr_map (ptrs:list b8{list_disjoint_or_eq ptrs}) : GTot addr_map =
  global_addrs_map

noeq type interop_heap =
  | InteropHeap :
    ptrs : list b8{list_disjoint_or_eq ptrs} ->
    addrs : addr_map{addrs == mk_addr_map ptrs} ->
    hs : HS.mem{list_live hs ptrs} ->
    interop_heap

unfold let hs_of_mem (m:interop_heap) : HS.mem = InteropHeap?.hs m
unfold let ptrs_of_mem (m:interop_heap) : l:list b8{list_disjoint_or_eq l} = InteropHeap?.ptrs m
unfold let addrs_of_mem (m:interop_heap) : addr_map = InteropHeap?.addrs m

let rec addrs_ptr (i:nat) (addrs:addr_map) (ptr:b8{i <= DV.length (get_downview ptr.bsrc)}) (acc:Set.set int)
  : GTot (Set.set int)
    (decreases (DV.length (get_downview ptr.bsrc) - i))
  =
  if i = DV.length (get_downview ptr.bsrc) then acc
  else addrs_ptr (i + 1) addrs ptr (Set.union (Set.singleton (addrs ptr + i)) acc)

let addrs_set (mem:interop_heap) : GTot (Set.set int) =
  L.fold_right_gtot (ptrs_of_mem mem) (addrs_ptr 0 (addrs_of_mem mem)) Set.empty

let correct_down_p (mem:interop_heap) (h:machine_heap) (p:b8) =
  let b = get_downview p.bsrc in
  let length = DV.length b in
  let contents = DV.as_seq (hs_of_mem mem) b in
  let addr = addrs_of_mem mem p in
  (forall i.{:pattern (Seq.index contents i)} 0 <= i /\ i < length ==>
    h.[addr + i] == UInt8.v (FStar.Seq.index contents i))

let correct_down (mem:interop_heap) (h:machine_heap) =
  Set.equal (addrs_set mem) (Map.domain h) /\
  (forall p.{:pattern (L.memP p (ptrs_of_mem mem))}
    L.memP p (ptrs_of_mem mem) ==> correct_down_p mem h p)

let down_mem_t = m:interop_heap -> GTot (h:machine_heap{correct_down m h})

let mem_of_hs_roots (ptrs:list b8{list_disjoint_or_eq ptrs}) (h:HS.mem{list_live h ptrs})
  : GTot interop_heap
  =
  InteropHeap ptrs (mk_addr_map ptrs) h

