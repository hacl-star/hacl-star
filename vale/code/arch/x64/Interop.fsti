module Interop

module List = FStar.List.Tot.Base
module HS = FStar.Monotonic.HyperStack
module HH = FStar.Monotonic.HyperHeap
module B = LowStar.Buffer
module M = LowStar.Modifies
module S8 = SecretByte

open Opaque_s
open X64.Machine_s
open X64.Bytes_Semantics_s
open X64.Bytes_Semantics

let op_String_Access = Map.sel
let op_String_Assignment = Map.upd

inline_for_extraction
let b8 = B.buffer UInt8.t
let s8 = B.buffer S8.t

let sub l i = l - i

let rec loc_locs_disjoint_rec (l:s8) (ls:list s8) : Type0 =
  match ls with
  | [] -> True
  | h::t -> M.loc_disjoint (M.loc_buffer l) (M.loc_buffer h) /\ loc_locs_disjoint_rec l t

let rec locs_disjoint_rec (ls:list s8) : Type0 =
  match ls with
  | [] -> True
  | h::t -> loc_locs_disjoint_rec h t /\ locs_disjoint_rec t

unfold
let bufs_disjoint (ls:list s8) : Type0 =
  norm [iota; zeta; delta; delta_only [`%loc_locs_disjoint_rec;
                                       `%locs_disjoint_rec]] (locs_disjoint_rec ls)

unfold
let buf_disjoint_from (b:s8) (ls:list s8) : Type0 =
  norm [iota; zeta; delta; delta_only [`%loc_locs_disjoint_rec;
                                       `%locs_disjoint_rec]] (loc_locs_disjoint_rec b ls)

unfold
let disjoint (#a:Type0) (ptr1 ptr2:B.buffer a) = M.loc_disjoint (M.loc_buffer ptr1) (M.loc_buffer ptr2)

unfold
let disjoint_or_eq ptr1 ptr2 = disjoint ptr1 ptr2 \/ ptr1 == ptr2

let list_disjoint_or_eq (#a:Type0) (ptrs:list (B.buffer a)) =
  forall p1 p2. List.memP p1 ptrs /\ List.memP p2 ptrs ==> disjoint_or_eq p1 p2

let disjoint_addr addr1 length1 addr2 length2 =
  (* The first buffer is completely before the second, or the opposite *)
  addr1 + length1 < addr2 || addr2 + length2 < addr1

type addr_map = (m:(s8 -> nat64){
  (forall (buf1 buf2:s8).{:pattern (m buf1); (m buf2)} disjoint buf1 buf2 ==> 
    disjoint_addr (m buf1) (B.length buf1) (m buf2) (B.length buf2)) /\
  (forall (b:s8).{:pattern (m b)} m b + B.length b < pow2_64)})

unfold
let list_live (#a:Type0) mem (ptrs:list (B.buffer a)) = forall p . List.memP p ptrs ==> B.live mem p

let correct_down_p (mem:HS.mem) (addrs:addr_map) (heap:heap) (p:s8) =
  let length = B.length p in
  let contents = B.as_seq mem p in
  let addr = addrs p in
  (forall i.  0 <= i /\ i < length ==> heap.[addr + i] == SecretByte.v (FStar.Seq.index contents i))

val addrs_set: (ptrs:list s8) -> (addrs:addr_map) -> GTot (s:Set.set int{
  forall x. not (Set.mem x s) <==> 
    (forall (b:s8{List.memP b ptrs}). x < addrs b \/ x >= addrs b + B.length b)})
    
val addrs_set_lemma: (ptrs1:list s8) -> (ptrs2:list s8) ->
  (addrs:addr_map) -> Lemma
  (requires forall b. List.memP b ptrs1 <==> List.memP b ptrs2)
  (ensures addrs_set ptrs1 addrs == addrs_set ptrs2 addrs)

val addrs_set_concat: (ptrs:list s8) -> (a:s8) ->
  (addrs:addr_map) -> Lemma
  (addrs_set (a::ptrs) addrs == Set.union (addrs_set ptrs addrs) (addrs_set [a] addrs))
  
val addrs_set_mem: (ptrs:list s8) -> (a:s8) ->
  (addrs:addr_map) -> (i:int) -> Lemma
  (requires List.memP a ptrs /\ i >= addrs a /\ i < addrs a + B.length a)
  (ensures Set.mem i (addrs_set ptrs addrs))
  
let correct_down mem (addrs:addr_map) (ptrs: list s8) heap =
  Set.equal (addrs_set ptrs addrs) (Map.domain heap) /\ 
  (forall p. List.memP p ptrs ==> correct_down_p mem addrs heap p)

(* Takes a Low* Hyperstack and a list of buffers and create a vale memory + keep track of the vale addresses *)
val down_mem: (mem:HS.mem) -> (addrs: addr_map) -> (ptrs:list s8{list_disjoint_or_eq ptrs}) -> GTot (heap :heap {correct_down mem addrs ptrs heap})

val same_unspecified_down: 
  (mem1: HS.mem) -> 
  (mem2: HS.mem) -> 
  (addrs:addr_map) ->
  (ptrs:list s8{list_disjoint_or_eq ptrs}) ->
  Lemma (
    let heap1 = down_mem mem1 addrs ptrs in
    let heap2 = down_mem mem2 addrs ptrs in
    forall i. (forall (b:s8{List.memP b ptrs}). 
      let base = addrs b in
      i < base \/ i >= base + B.length b) ==>
      heap1.[i] == heap2.[i])

let get_seq_heap (heap:heap) (addrs:addr_map) (b:s8) : GTot (Seq.lseq SecretByte.t (B.length b)) =
  let length = B.length b in
  let contents (i:nat{i < length}) = SecretByte.uint_to_t heap.[addrs b + i] in
  Seq.init length contents

val up_mem: 
  (heap:heap) -> 
  (addrs:addr_map) -> 
  (ptrs: list s8{list_disjoint_or_eq ptrs}) -> 
  (mem:HS.mem{list_live mem ptrs /\ Set.equal (addrs_set ptrs addrs) (Map.domain heap)}) -> 
  GTot (new_mem:HS.mem{correct_down new_mem addrs ptrs heap /\ list_live new_mem ptrs})

val down_up_identity: 
  (mem:HS.mem) -> 
  (addrs:addr_map) -> 
  (ptrs:list s8{list_disjoint_or_eq ptrs /\ list_live mem ptrs }) -> 
  Lemma (
    let heap = down_mem mem addrs ptrs in 
    let new_mem = up_mem heap addrs ptrs mem in
    mem == new_mem)

val up_down_identity:
  (mem:HS.mem) ->
  (addrs:addr_map) ->
  (ptrs:list s8{list_disjoint_or_eq ptrs /\ list_live mem ptrs}) ->
  (heap:heap{Set.equal (addrs_set ptrs addrs) (Map.domain heap)}) -> 
  Lemma
    (requires (forall x. not (Map.contains heap x) ==> Map.sel heap x == Map.sel (down_mem mem addrs ptrs) x))
    (ensures (down_mem (up_mem heap addrs ptrs mem) addrs ptrs == heap))

val update_buffer_up_mem:
  (ptrs:list s8{list_disjoint_or_eq ptrs}) ->
  (addrs:addr_map) ->
  (mem:HS.mem{list_live mem ptrs}) ->
  (b:s8{List.memP b ptrs}) ->
  (heap1:heap{correct_down mem addrs ptrs heap1}) ->
  (heap2:heap{Set.equal (Map.domain heap1) (Map.domain heap2)}) -> Lemma
  (requires (forall x. x < addrs b \/ x >= addrs b + B.length b ==> heap1.[x] == heap2.[x]))
  (ensures up_mem heap2 addrs ptrs mem == 
    B.g_upd_seq b (get_seq_heap heap2 addrs b) mem)
