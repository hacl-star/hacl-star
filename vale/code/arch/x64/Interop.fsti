module Interop
module IB = Interop.Base
module List = FStar.List.Tot.Base
module HS = FStar.Monotonic.HyperStack
module HH = FStar.Monotonic.HyperHeap
module B = LowStar.Buffer
module M = LowStar.Modifies

open Opaque_s
open X64.Machine_s
open X64.Bytes_Semantics_s
open X64.Bytes_Semantics

let op_String_Access = Map.sel
let op_String_Assignment = Map.upd

inline_for_extraction
let b8 = B.buffer UInt8.t

let sub l i = l - i

let rec loc_locs_disjoint_rec (l:b8) (ls:list b8) : Type0 =
  match ls with
  | [] -> True
  | h::t -> M.loc_disjoint (M.loc_buffer l) (M.loc_buffer h) /\ loc_locs_disjoint_rec l t

let rec locs_disjoint_rec (ls:list b8) : Type0 =
  match ls with
  | [] -> True
  | h::t -> loc_locs_disjoint_rec h t /\ locs_disjoint_rec t

unfold
let bufs_disjoint (ls:list b8) : Type0 =
  norm [iota; zeta; delta; delta_only [`%loc_locs_disjoint_rec;
                                       `%locs_disjoint_rec]] (locs_disjoint_rec ls)

unfold
let buf_disjoint_from (b:b8) (ls:list b8) : Type0 =
  norm [iota; zeta; delta; delta_only [`%loc_locs_disjoint_rec;
                                       `%locs_disjoint_rec]] (loc_locs_disjoint_rec b ls)

unfold
let disjoint (#a:Type0) (ptr1 ptr2:B.buffer a) = M.loc_disjoint (M.loc_buffer ptr1) (M.loc_buffer ptr2)

unfold
let disjoint_or_eq ptr1 ptr2 = IB.disjoint_or_eq_b8 ptr1 ptr2

unfold
let list_disjoint_or_eq = IB.list_disjoint_or_eq

unfold
let disjoint_addr = IB.disjoint_addr

type addr_map = IB.addr_map

unfold
let list_live = IB.list_live

let valid_addr (mem:IB.mem) (x:int) = Set.mem x (IB.addrs_set mem)

val addrs_set_lemma (mem:IB.mem) (x:int)
  : Lemma (let addrs = IB.addrs_of_mem mem in
           let ptrs = IB.ptrs_of_mem mem in
           valid_addr mem x <==>
           (exists (b:b8{List.memP b ptrs}).{:pattern (addrs b)} addrs b <= x /\ x < addrs b + B.length b))
          [SMTPat (Set.mem x (IB.addrs_set mem))]
  
let addrs_set_mem (mem:IB.mem) (a:b8) (i:int)
  : Lemma
    (requires (let ptrs = IB.ptrs_of_mem mem in
               let addrs = IB.addrs_of_mem mem in
               List.memP a ptrs /\ i >= addrs a /\ i < addrs a + B.length a))
    (ensures valid_addr mem i)
  = ()
  
(* Takes a Low* Hyperstack and a list of buffers and create a vale memory + keep track of the vale addresses *)
val down_mem: IB.down_mem_t

val same_unspecified_down: 
  (hs1: HS.mem) -> 
  (hs2: HS.mem) -> 
  (ptrs:list b8{list_disjoint_or_eq ptrs /\ list_live hs1 ptrs /\ list_live hs2 ptrs}) ->
  Lemma (
    let mem1 = IB.mem_of_hs_roots ptrs hs1 in
    let mem2 = IB.mem_of_hs_roots ptrs hs2 in
    let addrs = IB.addrs_of_mem mem1 in
    let heap1 = down_mem mem1 in
    let heap2 = down_mem mem2 in
    forall i. not (valid_addr mem1 i) ==>
         heap1.[i] == heap2.[i])

let get_seq_heap (heap:heap) (addrs:addr_map) (b:b8) 
  : GTot (Seq.lseq UInt8.t (B.length b)) 
  = let length = B.length b in
    let contents (i:nat{i < length}) = UInt8.uint_to_t heap.[addrs b + i] in
    Seq.init length contents

val up_mem (heap:heap) (mem:IB.mem{Set.equal (IB.addrs_set mem) (Map.domain heap)})
  : GTot (new_mem:IB.mem{IB.ptrs_of_mem mem == IB.ptrs_of_mem mem /\
                         IB.correct_down new_mem heap})

val down_up_identity (mem:IB.mem)
  : Lemma (mem == up_mem (down_mem mem) mem)

val up_down_identity (mem:IB.mem)
                     (heap:heap{Set.equal (IB.addrs_set mem) (Map.domain heap)})
  : Lemma
      (requires (forall x. not (Map.contains heap x) ==> Map.sel heap x == Map.sel (down_mem mem) x))
      (ensures (down_mem (up_mem heap mem) == heap))

val update_buffer_up_mem
      (mem:IB.mem)
      (b:b8{List.memP b (IB.ptrs_of_mem mem)})
      (heap1:heap{IB.correct_down mem heap1})
      (heap2:heap{Set.equal (Map.domain heap1) (Map.domain heap2)})
 : Lemma
      (requires (forall x. not (valid_addr mem x) ==> heap1.[x] == heap2.[x]))
      (ensures IB.hs_of_mem (up_mem heap2 mem) ==
               B.g_upd_seq b (get_seq_heap heap2 (IB.addrs_of_mem mem) b) (IB.hs_of_mem mem))
