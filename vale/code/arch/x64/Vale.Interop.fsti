module Vale.Interop
open FStar.Mul
module List = FStar.List.Tot.Base
module HS = FStar.Monotonic.HyperStack
module MB = LowStar.Monotonic.Buffer
module DV = LowStar.BufferView.Down

open Vale.Def.Opaque_s
open Vale.Interop.Types
open Vale.Interop.Heap_s
//open Vale.Interop.Base
open Vale.Arch.MachineHeap_s

unfold let (.[]) = Map.sel
unfold let (.[]<-) = Map.upd

let disjoint (ptr1 ptr2:b8) = MB.loc_disjoint (MB.loc_buffer ptr1.bsrc) (MB.loc_buffer ptr2.bsrc)

let valid_addr (mem:interop_heap) (x:int) = Set.mem x (addrs_set mem)

val addrs_set_lemma (mem:interop_heap) (x:int)
  : Lemma (let addrs = addrs_of_mem mem in
           let ptrs = ptrs_of_mem mem in
           valid_addr mem x <==>
           (exists (b:b8{List.memP b ptrs}).{:pattern (addrs b)} addrs b <= x /\ x < addrs b + DV.length (get_downview b.bsrc)))

val addrs_set_lemma_all (_:unit) : Lemma
  (forall (mem:interop_heap) (x:int).{:pattern (Set.mem x (addrs_set mem))}
    let addrs = addrs_of_mem mem in
    let ptrs = ptrs_of_mem mem in
    valid_addr mem x <==>
    (exists (b:b8{List.memP b ptrs}).{:pattern (addrs b)} addrs b <= x /\ x < addrs b + DV.length (get_downview b.bsrc)))

val addrs_set_mem (mem:interop_heap) (a:b8) (i:int)
  : Lemma
    (requires (let ptrs = ptrs_of_mem mem in
               let addrs = addrs_of_mem mem in
               List.memP a ptrs /\ i >= addrs a /\ i < addrs a + DV.length (get_downview a.bsrc)))
    (ensures valid_addr mem i)

(* Takes a Low* Hyperstack and a list of buffers and create a vale memory + keep track of the vale addresses *)
val down_mem: down_mem_t

val same_unspecified_down
    (hs1: HS.mem)
    (hs2: HS.mem)
    (ptrs:list b8{list_disjoint_or_eq ptrs /\ list_live hs1 ptrs /\ list_live hs2 ptrs})
  : Lemma (
    let mem1 = mem_of_hs_roots ptrs hs1 in
    let mem2 = mem_of_hs_roots ptrs hs2 in
    let addrs = addrs_of_mem mem1 in
    let heap1 = down_mem mem1 in
    let heap2 = down_mem mem2 in
    forall i. not (valid_addr mem1 i) ==> // REVIEW: the 'forall' lacks a {:pattern ...}
         heap1.[i] == heap2.[i])

let get_seq_heap (heap:machine_heap) (addrs:addr_map) (b:b8)
  : GTot (Seq.lseq UInt8.t (DV.length (get_downview b.bsrc)))
  = let length = DV.length (get_downview b.bsrc) in
    let contents (i:nat{i < length}) = UInt8.uint_to_t heap.[addrs b + i] in
    Seq.init length contents

val up_mem (heap:machine_heap) (mem:interop_heap{Set.equal (addrs_set mem) (Map.domain heap)})
  : GTot (new_mem:interop_heap{ptrs_of_mem mem == ptrs_of_mem new_mem /\
                         correct_down new_mem heap})

val down_up_identity (mem:interop_heap)
  : Lemma (mem == up_mem (down_mem mem) mem)

val up_down_identity
    (mem:interop_heap)
    (heap:machine_heap{Set.equal (addrs_set mem) (Map.domain heap)})
  : Lemma
      (requires
        (forall x.{:pattern Map.sel heap x \/ Map.sel (down_mem mem) x}
          not (Map.contains heap x) ==> Map.sel heap x == Map.sel (down_mem mem) x))
      (ensures (down_mem (up_mem heap mem) == heap))

val update_buffer_up_mem
    (mem:interop_heap)
    (b:b8{List.memP b (ptrs_of_mem mem)})
    (heap1:machine_heap{correct_down mem heap1})
    (heap2:machine_heap{Set.equal (Map.domain heap1) (Map.domain heap2)})
 : Lemma
      (requires
        (forall x.{:pattern heap1.[x] \/ heap2.[x]}
          x < addrs_of_mem mem b \/ x >= addrs_of_mem mem b + DV.length (get_downview b.bsrc)
            ==> heap1.[x] == heap2.[x]))
      (ensures hs_of_mem (up_mem heap2 mem) ==
               DV.upd_seq (hs_of_mem mem) (get_downview b.bsrc) (get_seq_heap heap2 (addrs_of_mem mem) b))
