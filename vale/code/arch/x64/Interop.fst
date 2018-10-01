module Interop

(** Attempt to define down and up functions, to express relation between
    Low*'s and Vale's memory models.
    Currently only supports buffers of UInt8
*)


module List = FStar.List.Tot.Base
module HS = FStar.Monotonic.HyperStack
module HH = FStar.Monotonic.HyperHeap
module B = LowStar.Buffer
module M = LowStar.Modifies

open Opaque_s
open X64.Machine_s
open X64.Bytes_Semantics_s
open X64.Bytes_Semantics

#reset-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1"

let op_String_Access = Map.sel
let op_String_Assignment = Map.upd

let sub l i = l - i

inline_for_extraction
let b8 = B.buffer UInt8.t

unfold
let disjoint_or_eq ptr1 ptr2 = B.disjoint ptr1 ptr2 \/ ptr1 == ptr2

let list_disjoint_or_eq (#a:Type0) (ptrs:list (B.buffer a)) =
  forall p1 p2. List.memP p1 ptrs /\ List.memP p2 ptrs ==> disjoint_or_eq p1 p2

let disjoint_addr addr1 length1 addr2 length2 =
  (* The first buffer is completely before the second, or the opposite *)
  addr1 + length1 < addr2 || addr2 + length2 < addr1

type addr_map = (m:(b8 -> nat64){
  (forall (buf1 buf2:b8). B.disjoint buf1 buf2 ==>
    disjoint_addr (m buf1) (B.length buf1) (m buf2) (B.length buf2)) /\
  (forall (b:b8). m b + B.length b < pow2_64)})

unfold
let list_live mem ptrs = forall p . List.memP p ptrs ==> B.live mem p

(* Additional hypotheses, which should be added to the corresponding libraries at some point *)

//This lemma will be available in the next version of Low*
assume val buffers_disjoint (b1 b2:b8) : Lemma
  (requires M.loc_disjoint (M.loc_buffer b1) (M.loc_buffer b2))
  (ensures B.disjoint b1 b2)
  [SMTPat (B.disjoint b1 b2)]

(* If two refs have the same address, and are in the heap, they are equal *)
assume val ref_extensionality (#a:Type0) (#rel:Preorder.preorder a) (h:Heap.heap) (r1 r2:Heap.mref a rel) : Lemma
  (Heap.contains h r1 /\ Heap.contains h r2 /\ Heap.addr_of r1 = Heap.addr_of r2 ==> r1 == r2)

(* Write a buffer in the vale memory *)

let rec write_vale_mem (contents:Seq.seq UInt8.t) (length:nat{length = FStar.Seq.Base.length contents}) addr (i:nat{i <= length})
      (curr_heap:heap{forall j. {:pattern (Seq.index contents j)}
        0 <= j /\ j < i ==> curr_heap.[addr+j] == UInt8.v (Seq.index contents j)}) : Tot heap (decreases %[sub length i]) =
    if i >= length then curr_heap
    else (
      let heap = curr_heap.[addr + i] <- UInt8.v (FStar.Seq.index contents i) in
      write_vale_mem contents length addr (i+1) heap
    )

let rec frame_write_vale_mem (contents:Seq.seq UInt8.t) (length:nat{length = FStar.Seq.Base.length contents}) addr (i:nat{i <= length})
      (curr_heap:heap{forall j. {:pattern (Seq.index contents j)} 0 <= j /\ j < i ==> curr_heap.[addr + j] == UInt8.v (Seq.index contents j)}) : Lemma
      (requires True)
      (ensures (let new_heap = write_vale_mem contents length addr i curr_heap in
      forall j. j < addr \/ j >= addr + length ==> curr_heap.[j] == new_heap.[j]))
      (decreases %[sub length i])=
      if i >= length then ()
      else begin
        let heap = curr_heap.[addr + i] <- UInt8.v (FStar.Seq.index contents i) in
        frame_write_vale_mem contents length addr (i+1) heap
      end

let rec load_store_write_vale_mem
  (contents:Seq.seq UInt8.t)
  (length:nat{length = FStar.Seq.Base.length contents})
  addr
  (i:nat{i <= length})
  (curr_heap:heap{forall j. {:pattern (Seq.index contents j)} 0 <= j /\ j < i ==>
    curr_heap.[addr + j] == UInt8.v (Seq.index contents j)}) : Lemma
      (requires True)
      (ensures (let new_heap = write_vale_mem contents length addr i curr_heap in
      forall j. 0 <= j /\ j < length ==> UInt8.v (Seq.index contents j) == new_heap.[addr + j]))
      (decreases %[sub length i])=
      if i >= length then ()
      else begin
        let heap = curr_heap.[addr + i] <- UInt8.v (FStar.Seq.index contents i) in
        load_store_write_vale_mem contents length addr (i+1) heap
      end

let rec domain_write_vale_mem
  (contents:Seq.seq UInt8.t)
  (length:nat{length = FStar.Seq.Base.length contents})
  addr
  (i:nat{i <= length})
  (curr_heap:heap{forall j. {:pattern (Seq.index contents j)} 0 <= j /\ j < i ==>
    curr_heap.[addr + j] == UInt8.v (Seq.index contents j)}) : Lemma
      (requires True)
      (ensures (let new_heap = write_vale_mem contents length addr i curr_heap in
      forall j. Set.mem j (Map.domain new_heap) /\ not (Set.mem j (Map.domain curr_heap)) ==>
        addr <= j /\ j < addr + length))
      (decreases %[sub length i])=
   if i >= length then ()
   else begin
     let heap = curr_heap.[addr + i] <- UInt8.v (FStar.Seq.index contents i) in
     domain_write_vale_mem contents length addr (i+1) heap
    end

let rec domain2_write_vale_mem
  (contents:Seq.seq UInt8.t)
  (length:nat{length = FStar.Seq.Base.length contents})
  addr
  (i:nat{i <= length})
  (curr_heap:heap{forall j. {:pattern (Seq.index contents j)} 0 <= j /\ j < i ==>
    curr_heap.[addr + j] == UInt8.v (Seq.index contents j)}) : Lemma
      (requires forall j. addr <= j /\ j < addr + i ==> Set.mem j (Map.domain curr_heap))
      (ensures (let new_heap = write_vale_mem contents length addr i curr_heap in
        forall j. addr <= j /\ j < addr + length ==> Set.mem j (Map.domain new_heap)))
      (decreases %[sub length i])=
   if i >= length then ()
   else begin
     let heap = curr_heap.[addr + i] <- UInt8.v (FStar.Seq.index contents i) in
     domain2_write_vale_mem contents length addr (i+1) heap
    end

let rec monotone_domain_write_vale_mem
  (contents:Seq.seq UInt8.t)
  (length:nat{length = FStar.Seq.Base.length contents})
  addr
  (i:nat{i <= length})
  (curr_heap:heap{forall j. {:pattern (Seq.index contents j)} 0 <= j /\ j < i ==>
    curr_heap.[addr + j] == UInt8.v (Seq.index contents j)}) : Lemma
      (requires True)
      (ensures (let new_heap = write_vale_mem contents length addr i curr_heap in
      forall j. Set.mem j (Map.domain curr_heap) ==> Set.mem j (Map.domain new_heap)))
      (decreases %[sub length i])=
   if i >= length then ()
   else begin
     let heap = curr_heap.[addr + i] <- UInt8.v (FStar.Seq.index contents i) in
     monotone_domain_write_vale_mem contents length addr (i+1) heap
    end

let correct_down_p (mem:HS.mem) (addrs:addr_map) (heap:heap) (p:b8) =
  let length = B.length p in
  let contents = B.as_seq mem p in
  let addr = addrs p in
  (forall i.  0 <= i /\ i < length ==> heap.[addr + i] == UInt8.v (FStar.Seq.index contents i))

#set-options "--z3rlimit 40"

let correct_down_p_cancel mem (addrs:addr_map) heap (p:b8) : Lemma
  (forall p'. p == p' ==>
      (let length = B.length p in
      let contents = B.as_seq mem p in
      let addr = addrs p in
      let new_heap = write_vale_mem contents length addr 0 heap in
      correct_down_p mem addrs new_heap p')) =
  let rec aux (p':b8) : Lemma
    (p == p'  ==> (let length = B.length p in
      let contents = B.as_seq mem p in
      let addr = addrs p in
      let new_heap = write_vale_mem contents length addr 0 heap in
      correct_down_p mem addrs new_heap p')) =
        let length = B.length p in
        let contents = B.as_seq mem p in
        let addr = addrs p in
        let new_heap = write_vale_mem contents length addr 0 heap in
        load_store_write_vale_mem contents length addr 0 heap
  in
  Classical.forall_intro aux

let correct_down_p_frame mem (addrs:addr_map) (heap:heap) (p:b8) : Lemma
  (forall p'. B.disjoint p p' /\ correct_down_p mem addrs heap p' ==>
      (let length = B.length p in
      let contents = B.as_seq mem p in
      let addr = addrs p in
      let new_heap = write_vale_mem contents length addr 0 heap in
      correct_down_p mem addrs new_heap p')) =
  let rec aux (p':b8) : Lemma
    (B.disjoint p p' /\ correct_down_p mem addrs heap p' ==> (let length = B.length p in
      let contents = B.as_seq mem p in
      let addr = addrs p in
      let new_heap = write_vale_mem contents length addr 0 heap in
      correct_down_p mem addrs new_heap p')) =
        let length = B.length p in
        let contents = B.as_seq mem p in
        let addr = addrs p in
        let new_heap = write_vale_mem contents length addr 0 heap in
        frame_write_vale_mem contents length addr 0 heap
  in
  Classical.forall_intro aux

val addrs_set: (ptrs:list b8) -> (addrs:addr_map) -> GTot (s:Set.set int{
  forall x. not (Set.mem x s) <==>
    (forall (b:b8{List.memP b ptrs}). x < addrs b \/ x >= addrs b + B.length b)})

private let add_buffer_domain (b:b8) (addrs:addr_map) (accu:Set.set int) : GTot (s:Set.set int{
  forall x. Set.mem x s <==> (Set.mem x accu \/ (x >= addrs b /\ x < addrs b + B.length b))}) =
  let rec aux (j:nat{j <= B.length b}) (acc:Set.set int{forall x. Set.mem x acc <==>
    Set.mem x accu \/ (x >= addrs b /\ x < addrs b + j)}) :
    GTot (s:Set.set int{forall x. Set.mem x s <==>
    Set.mem x accu \/ (x >= addrs b /\ x < addrs b + B.length b)})
    (decreases %[B.length b - j]) =
    if j >= B.length b then acc else begin
      let s = Set.union acc (Set.singleton (addrs b + j)) in
      aux (j+1) s
    end in
  aux 0 accu


private let rec addrs_set_aux (ptrs:list b8)
                              (ps2: list b8)
                              (ps:list b8{forall b. List.memP b ptrs <==> List.memP b ps \/ List.memP b ps2})
                              (addrs:addr_map)
                              (accu:Set.set int{forall (x:int). not (Set.mem x accu) <==>
                                (forall (b:b8{List.memP b ps}). x < addrs b \/ x >= addrs b + B.length b)}) :
                         GTot (s:Set.set int{forall (x:int). not (Set.mem x s) <==>
                                (forall (b:b8{List.memP b ptrs}). x < addrs b \/ x >= addrs b + B.length b)}) =
  match ps2 with
  | [] -> accu
  | a::q ->
    let s = add_buffer_domain a addrs accu in
    let aux (x:int) : Lemma
      (requires True)
      (ensures not (Set.mem x s) <==>
      (forall (b:b8{List.memP b (a::ps)}).
        x < addrs b \/ x >= addrs b + B.length b)) = ()
    in
    Classical.forall_intro aux;
    addrs_set_aux ptrs q (a::ps) addrs s

let addrs_set ptrs addrs = addrs_set_aux ptrs ptrs [] addrs Set.empty

val addrs_set_lemma: (ptrs1:list b8) -> (ptrs2:list b8) ->
  (addrs:addr_map) -> Lemma
  (requires forall b. List.memP b ptrs1 <==> List.memP b ptrs2)
  (ensures addrs_set ptrs1 addrs == addrs_set ptrs2 addrs)

let addrs_set_lemma ptrs1 ptrs2 addrs =
  let s1 = addrs_set_aux ptrs1 ptrs1 [] addrs Set.empty in
  let s2 = addrs_set_aux ptrs2 ptrs2 [] addrs Set.empty in
  assert (Set.equal s1 s2)

val addrs_set_concat: (ptrs:list b8) -> (a:b8) ->
  (addrs:addr_map) -> Lemma
  (addrs_set (a::ptrs) addrs == Set.union (addrs_set ptrs addrs) (addrs_set [a] addrs))

let addrs_set_concat ptrs a addrs =
  let s1 = addrs_set ptrs addrs in
  let s2 = addrs_set [a] addrs in
  assert (Set.equal (addrs_set (a::ptrs) addrs) (Set.union s1 s2));
  ()

val addrs_set_mem: (ptrs:list b8) -> (a:b8) ->
  (addrs:addr_map) -> (i:int) -> Lemma
  (requires List.memP a ptrs /\ i >= addrs a /\ i < addrs a + B.length a)
  (ensures Set.mem i (addrs_set ptrs addrs))

let addrs_set_mem ptrs a addrs i = ()

let write_buffer_vale (a:b8) (heap:heap) (mem:HS.mem) (addrs:addr_map) =
  let length = B.length a in
  let contents = B.as_seq mem a in
  let addr = addrs a in
  write_vale_mem contents length addr 0 heap

let domain_write_buffer (a:b8) (heap:heap) (mem:HS.mem) (addrs:addr_map) : Lemma
  (let new_heap = write_buffer_vale a heap mem addrs in
   Set.equal (Set.union (Map.domain heap) (addrs_set [a] addrs)) (Map.domain new_heap)) =
   let new_heap = write_buffer_vale a heap mem addrs in
   let s1 = Map.domain heap in
   let s2 = addrs_set [a] addrs in
   let s3 = Map.domain new_heap in
   let length = B.length a in
   let contents = B.as_seq mem a in
   let addr = addrs a in
   domain_write_vale_mem contents length addr 0 heap;
   domain2_write_vale_mem contents length addr 0 heap;
   monotone_domain_write_vale_mem contents length addr 0 heap;
   ()

let correct_down mem (addrs:addr_map) (ptrs: list b8) heap =
  Set.equal (addrs_set ptrs addrs) (Map.domain heap) /\
  (forall p. List.memP p ptrs ==> correct_down_p mem addrs heap p)

(* Takes a Low* Hyperstack and a list of buffers and create a vale memory + keep track of the vale addresses *)
val down_mem: (mem:HS.mem) -> (addrs: addr_map) -> (ptrs:list b8{list_disjoint_or_eq ptrs}) -> GTot (heap :heap {correct_down mem addrs ptrs heap})

let rec down_mem_aux (ptrs:list b8{list_disjoint_or_eq ptrs})
  (addrs:addr_map)
  (mem:HS.mem)
  (ps:list b8)
  (accu:list b8{forall p. List.memP p ptrs <==> List.memP p ps \/ List.memP p accu})
  (h:heap{correct_down mem addrs accu h}) :
  GTot (heap:heap{correct_down mem addrs ptrs heap}) =
  match ps with
    | [] -> addrs_set_lemma accu ptrs addrs; h
    | a::q ->
      let new_heap = write_buffer_vale a h mem addrs in
      let length = B.length a in
      let contents = B.as_seq mem a in
      let addr = addrs a in
      load_store_write_vale_mem contents length addr 0 h;
      correct_down_p_cancel mem addrs h a;
      correct_down_p_frame mem addrs h a;
      assert (forall p. List.memP p accu ==> disjoint_or_eq p a);
      domain_write_buffer a h mem addrs;
      addrs_set_concat accu a addrs;
      down_mem_aux ptrs addrs mem q (a::accu) new_heap

let down_mem mem addrs ptrs =
  (* Dummy heap *)
  let heap = FStar.Map.const 0 in
  let heap = Map.restrict Set.empty heap in
  down_mem_aux ptrs addrs mem ptrs [] heap

private
let rec frame_down_mem_aux (ptrs:list b8{list_disjoint_or_eq ptrs})
  (addrs:addr_map)
  (mem:HS.mem)
  (ps:list b8)
  (accu:list b8{forall p. List.memP p ptrs <==> List.memP p ps \/ List.memP p accu})
  (h:heap{correct_down mem addrs accu h}) : Lemma
  (let heap = down_mem_aux ptrs addrs mem ps accu h in
   forall i. (forall (b:b8{List.memP b ptrs}).
      let base = addrs b in
      i < base \/ i >= base + B.length b) ==>
      h.[i] == heap.[i]) =
  match ps with
  | [] -> ()
  | a::q ->
    let new_heap = write_buffer_vale a h mem addrs in
    let length = B.length a in
    let contents = B.as_seq mem a in
    let addr = addrs a in
    load_store_write_vale_mem contents length addr 0 h;
    correct_down_p_cancel mem addrs h a;
    correct_down_p_frame mem addrs h a;
    assert (forall p. List.memP p accu ==> disjoint_or_eq p a);
    domain_write_buffer a h mem addrs;
    addrs_set_concat accu a addrs;
    frame_down_mem_aux ptrs addrs mem q (a::accu) new_heap;
    frame_write_vale_mem contents length addr 0 h;
    ()

val same_unspecified_down:
  (mem1: HS.mem) ->
  (mem2: HS.mem) ->
  (addrs:addr_map) ->
  (ptrs:list b8{list_disjoint_or_eq ptrs}) ->
  Lemma (
    let heap1 = down_mem mem1 addrs ptrs in
    let heap2 = down_mem mem2 addrs ptrs in
    forall i. (forall (b:b8{List.memP b ptrs}).
      let base = addrs b in
      i < base \/ i >= base + B.length b) ==>
      heap1.[i] == heap2.[i])

let same_unspecified_down mem1 mem2 addrs ptrs =
  let heap = Map.const 0 in
  let heap = Map.restrict Set.empty heap in
  let heapf1 = down_mem_aux ptrs addrs mem1 ptrs [] heap in
  let heapf2 = down_mem_aux ptrs addrs mem2 ptrs [] heap in
  frame_down_mem_aux ptrs addrs mem1 ptrs [] heap;
  frame_down_mem_aux ptrs addrs mem2 ptrs [] heap;
  ()
