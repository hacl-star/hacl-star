module Interop

module List = FStar.List.Tot.Base
module HS = FStar.Monotonic.HyperStack
module HH = FStar.Monotonic.HyperHeap
module MB = LowStar.Monotonic.Buffer
module M = LowStar.Modifies
module DV = LowStar.BufferView.Down

open Opaque_s
open Interop.Base
open BufferViewHelpers
// open X64.Machine_s
// open X64.Bytes_Semantics_s
// open X64.Bytes_Semantics

#reset-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1"

(* Write a buffer in the vale memory *)

let rec write_vale_mem (contents:Seq.seq UInt8.t) (length:nat{length = FStar.Seq.Base.length contents}) addr (i:nat{i <= length}) 
      (curr_heap:heap{forall j. {:pattern (Seq.index contents j)} 
	0 <= j /\ j < i ==> curr_heap.[addr+j] == UInt8.v (Seq.index contents j)}) : Tot heap (decreases (length - i)) =
    if i >= length then curr_heap
    else (
      let heap = curr_heap.[addr + i] <- UInt8.v (FStar.Seq.index contents i) in
      write_vale_mem contents length addr (i+1) heap
    )      

let rec frame_write_vale_mem 
  (contents:Seq.seq UInt8.t) 
  (length:nat{length = FStar.Seq.Base.length contents})
  addr 
  (i:nat{i <= length}) 
  (curr_heap:heap{forall j. {:pattern (Seq.index contents j)} 
    0 <= j /\ j < i ==> curr_heap.[addr + j] == UInt8.v (Seq.index contents j)})
  (j:int) : Lemma
  (requires j < addr \/ j >= addr + length)
  (ensures (let new_heap = write_vale_mem contents length addr i curr_heap in
      curr_heap.[j] == new_heap.[j]))
  (decreases (length - i))=
    if i >= length then ()
    else (
      let heap = curr_heap.[addr + i] <- UInt8.v (FStar.Seq.index contents i) in
      frame_write_vale_mem contents length addr (i+1) heap j
    )
      
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
      (decreases (length - i))=
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
      (decreases (length - i))=
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
      (decreases (length - i))=
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
      (decreases (length - i))=
   if i >= length then ()
   else begin
     let heap = curr_heap.[addr + i] <- UInt8.v (FStar.Seq.index contents i) in
     monotone_domain_write_vale_mem contents length addr (i+1) heap
    end

#set-options "--z3rlimit 40"

let correct_down_p_cancel (mem:mem) heap (p:b8) : Lemma
  (forall p'. p == p' ==>       
      (let b = get_downview p.bsrc in
      let length = DV.length b in
      let contents = DV.as_seq (hs_of_mem mem) b in
      let addr = addrs_of_mem mem p in
      let new_heap = write_vale_mem contents length addr 0 heap in
      correct_down_p mem new_heap p')) = 
  let rec aux (p':b8) : Lemma 
    (p == p'  ==> (
      let b = get_downview p.bsrc in
      let length = DV.length b in
      let contents = DV.as_seq (hs_of_mem mem) b in
      let addr = addrs_of_mem mem p in
      let new_heap = write_vale_mem contents length addr 0 heap in
      correct_down_p mem new_heap p')) =
        let b = get_downview p.bsrc in
        let length = DV.length b in
        let contents = DV.as_seq (hs_of_mem mem) b in
        let addr = addrs_of_mem mem p in
        let new_heap = write_vale_mem contents length addr 0 heap in
	load_store_write_vale_mem contents length addr 0 heap
  in
  Classical.forall_intro aux
      
let correct_down_p_frame (mem:mem) (heap:heap) (p:b8) : Lemma
  (forall p'. disjoint p p' /\ correct_down_p mem heap p' ==>       
      (let b = get_downview p.bsrc in
      let length = DV.length b in
      let contents = DV.as_seq (hs_of_mem mem) b in
      let addr = addrs_of_mem mem p in
      let new_heap = write_vale_mem contents length addr 0 heap in
      correct_down_p mem new_heap p')) = 
  let rec aux (p':b8) : Lemma 
    (disjoint p p' /\ correct_down_p mem heap p' ==> (
      let b = get_downview p.bsrc in
      let length = DV.length b in
      let contents = DV.as_seq (hs_of_mem mem) b in
      let addr = addrs_of_mem mem p in
      let new_heap = write_vale_mem contents length addr 0 heap in
      correct_down_p mem new_heap p')) =
        let b = get_downview p.bsrc in
        let length = DV.length b in
        let contents = DV.as_seq (hs_of_mem mem) b in
        let addr = addrs_of_mem mem p in
        let new_heap = write_vale_mem contents length addr 0 heap in
	Classical.forall_intro (Classical.move_requires (frame_write_vale_mem contents length addr 0 heap))
  in
  Classical.forall_intro aux

let rec addrs_ptr_lemma
  (i:nat) 
  (addrs:addr_map)
  (ptr:b8{i <= DV.length (get_downview ptr.bsrc)}) 
  (acc:Set.set int) 
  (x:int) : Lemma
  (requires True)
  (ensures Set.mem x (addrs_ptr i addrs ptr acc) <==>
    ((addrs ptr + i <= x /\ x < addrs ptr + DV.length (get_downview ptr.bsrc)) \/ Set.mem x acc))
  (decreases (DV.length (get_downview ptr.bsrc) - i)) =
  if i = DV.length (get_downview ptr.bsrc) then ()
  else addrs_ptr_lemma (i+1) addrs ptr (Set.union (Set.singleton (addrs ptr + i)) acc) x

let rec addrs_set_lemma_aux (addrs:addr_map) (ptrs:list b8) (acc:Set.set int) (x:int) : Lemma
  (requires True)
  (ensures Set.mem x (List.fold_right_gtot ptrs (addrs_ptr 0 addrs) acc) <==>
    ((exists (b:b8{List.memP b ptrs}). 
      addrs b <= x /\ x < addrs b + DV.length (get_downview b.bsrc)) \/ Set.mem x acc)) =
  match ptrs with
  | [] -> ()
  | a::q -> 
    let acc' = List.fold_right_gtot q (addrs_ptr 0 addrs) acc in
    addrs_ptr_lemma 0 addrs a acc' x;
    addrs_set_lemma_aux addrs q acc x

let addrs_set_lemma mem x =
  addrs_set_lemma_aux (addrs_of_mem mem) (ptrs_of_mem mem) Set.empty x

let write_buffer_vale (a:b8) (heap:heap) (mem:mem) =
  let b = get_downview a.bsrc in
  let length = DV.length b in
  let contents = DV.as_seq (hs_of_mem mem) b in
  let addr = addrs_of_mem mem a in
  write_vale_mem contents length addr 0 heap

let rec down_mem_aux 
  (ptrs:list b8{list_disjoint_or_eq ptrs})
  (mem:mem)
  (ps:list b8)
  (accu:list b8{forall p. List.memP p ptrs <==> List.memP p ps \/ List.memP p accu})
  (h:heap{forall p. {:pattern List.memP p accu} 
    List.memP p accu ==> correct_down_p mem h p}) : GTot 
  (heap:heap{forall p. {:pattern List.memP p ptrs}
    List.memP p ptrs ==> correct_down_p mem heap p}) =
  match ps with
    | [] -> h
    | a::q ->
      let new_heap = write_buffer_vale a h mem in
      let b = get_downview a.bsrc in
      let length = DV.length b in
      let contents = DV.as_seq (hs_of_mem mem) b in
      let addr = addrs_of_mem mem a in      
      load_store_write_vale_mem contents length addr 0 h;
      correct_down_p_cancel mem h a;
      correct_down_p_frame mem h a;
      down_mem_aux ptrs mem q (a::accu) new_heap

let lemma_write_buffer_domain (a:b8) (heap:heap) (mem:mem) : Lemma
   (Set.equal 
     (Set.union (Map.domain heap) (addrs_ptr 0 (addrs_of_mem mem) a Set.empty)) 
     (Map.domain (write_buffer_vale a heap mem))) =
   let new_heap = write_buffer_vale a heap mem in
   let s1 = Map.domain heap in
   let s2 = addrs_ptr 0 (addrs_of_mem mem) a Set.empty in
   let s3 = Map.domain new_heap in
   let b = get_downview a.bsrc in
   let length = DV.length b in
   let contents = DV.as_seq (hs_of_mem mem) b in
   let addr = addrs_of_mem mem a in   
   domain_write_vale_mem contents length addr 0 heap;
   domain2_write_vale_mem contents length addr 0 heap;
   Classical.forall_intro (addrs_ptr_lemma 0 (addrs_of_mem mem) a Set.empty);
   monotone_domain_write_vale_mem contents length addr 0 heap

let rec lemma_down_mem_aux_domain
  (ptrs:list b8{list_disjoint_or_eq ptrs})
  (mem:mem)
  (ps:list b8)
  (accu:list b8{forall p. List.memP p ptrs <==> List.memP p ps \/ List.memP p accu})
  (h:heap{forall p. {:pattern correct_down_p mem h p} 
    List.memP p accu ==> correct_down_p mem h p})
  (x:int) : Lemma
  (requires Set.mem x (Map.domain h) <==>
    (exists (b:b8{List.memP b accu}).{:pattern (addrs_of_mem mem b)}
      addrs_of_mem mem b <= x /\ x < addrs_of_mem mem b + DV.length (get_downview b.bsrc))
  )
  (ensures Set.mem x (Map.domain (down_mem_aux ptrs mem ps accu h)) <==>
    (exists (b:b8{List.memP b ptrs}).{:pattern (addrs_of_mem mem b)}
      addrs_of_mem mem b <= x /\ x < addrs_of_mem mem b + DV.length (get_downview b.bsrc))
  ) = match ps with
  | [] -> ()
  | a::tl -> 
    lemma_write_buffer_domain a h mem;
    addrs_ptr_lemma 0 (addrs_of_mem mem) a Set.empty x;    
    let new_heap = write_buffer_vale a h mem in
    let b = get_downview a.bsrc in
    let length = DV.length b in
    let contents = DV.as_seq (hs_of_mem mem) b in
    let addr = addrs_of_mem mem a in      
    load_store_write_vale_mem contents length addr 0 h;
    correct_down_p_cancel mem h a;
    correct_down_p_frame mem h a;    
    lemma_down_mem_aux_domain ptrs mem tl (a::accu) new_heap x

let down_mem mem =
  (* Dummy heap *)
  let heap = FStar.Map.const 0 in
  let heap = Map.restrict Set.empty heap in
  let ptrs = ptrs_of_mem mem in
  let heap_f = down_mem_aux ptrs mem ptrs [] heap in
  let aux (x:int) : Lemma (Set.mem x (addrs_set mem) <==> Set.mem x (Map.domain heap_f)) =
    lemma_down_mem_aux_domain ptrs mem ptrs [] heap x
  in Classical.forall_intro aux;
  heap_f

private
let rec frame_down_mem_aux (ptrs:list b8{list_disjoint_or_eq ptrs})
  (mem:mem)
  (ps:list b8)
  (accu:list b8{forall p. List.memP p ptrs <==> List.memP p ps \/ List.memP p accu})
  (h:heap{forall p. {:pattern List.memP p accu} 
    List.memP p accu ==> correct_down_p mem h p})
  (i:int) : Lemma
  (requires (forall (b:b8{List.memP b ps}). 
      let base = addrs_of_mem mem b in
      i < base \/ i >= base + DV.length (get_downview b.bsrc)))
  (ensures h.[i] == (down_mem_aux ptrs mem ps accu h).[i]) =
  match ps with
  | [] -> ()
  | a::q ->
    let new_heap = write_buffer_vale a h mem in
    let b = get_downview a.bsrc in
    let length = DV.length b in
    let contents = DV.as_seq (hs_of_mem mem) b in
    let addr = addrs_of_mem mem a in      
    load_store_write_vale_mem contents length addr 0 h;
    correct_down_p_cancel mem h a;
    correct_down_p_frame mem h a;  
    frame_down_mem_aux ptrs mem q (a::accu) new_heap i;
    frame_write_vale_mem contents length addr 0 h i

val same_unspecified_down_aux: 
  (hs1: HS.mem) -> 
  (hs2: HS.mem) -> 
  (ptrs:list b8{list_disjoint_or_eq ptrs /\ list_live hs1 ptrs /\ list_live hs2 ptrs}) ->
  (i:int) ->
  Lemma (
    let mem1 = mem_of_hs_roots ptrs hs1 in
    let mem2 = mem_of_hs_roots ptrs hs2 in
    let addrs = addrs_of_mem mem1 in
    let heap1 = down_mem mem1 in
    let heap2 = down_mem mem2 in
    not (valid_addr mem1 i) ==>
         heap1.[i] == heap2.[i])

let same_unspecified_down_aux hs1 hs2 ptrs i =
  let heap = Map.const 0 in
  let heap = Map.restrict Set.empty heap in
  let mem1 = mem_of_hs_roots ptrs hs1 in
  let mem2 = mem_of_hs_roots ptrs hs2 in
  let addrs = addrs_of_mem mem1 in  
  let heapf1 = down_mem_aux ptrs mem1 ptrs [] heap in
  let heapf2 = down_mem_aux ptrs mem2 ptrs [] heap in
  addrs_set_lemma mem1 i;
  addrs_set_lemma mem1 i;
  Classical.move_requires (frame_down_mem_aux ptrs mem1 ptrs [] heap) i;
  Classical.move_requires (frame_down_mem_aux ptrs mem2 ptrs [] heap) i

let same_unspecified_down hs1 hs2 ptrs = 
  Classical.forall_intro (same_unspecified_down_aux hs1 hs2 ptrs)

let get_seq_heap_as_seq (heap1 heap2:heap) (mem:mem) (b:b8) : Lemma
  (requires correct_down_p mem heap1 b /\
    (forall x. x >= addrs_of_mem mem b /\ x < addrs_of_mem mem b + DV.length (get_downview b.bsrc) ==> heap1.[x] == heap2.[x]))
  (ensures DV.as_seq (hs_of_mem mem) (get_downview b.bsrc) == get_seq_heap heap2 (addrs_of_mem mem) b) =
  assert (Seq.equal (DV.as_seq (hs_of_mem mem) (get_downview b.bsrc)) (get_seq_heap heap2 (addrs_of_mem mem) b))

let rec up_mem_aux
  (h:heap)
  (ps:list b8)
  (accu:list b8)
  (m:mem{Set.equal (addrs_set m) (Map.domain h) /\
    (forall p. List.memP p accu ==> correct_down_p m h p) /\
    (forall p. List.memP p (ptrs_of_mem m) <==> List.memP p ps \/ List.memP p accu)}) : GTot
  (m':mem{ptrs_of_mem m == ptrs_of_mem m' /\
    correct_down m' h}) =
  match ps with
  | [] -> m
  | hd::tl ->
    let s = get_seq_heap h (addrs_of_mem m) hd in
    let b = get_downview hd.bsrc in
    DV.upd_seq_spec (hs_of_mem m) b s;
    let m' = DV.upd_seq (hs_of_mem m) b s in
    let aux1 (p:b8) : Lemma
      (requires MB.live (hs_of_mem m) p.bsrc /\
        MB.loc_disjoint (MB.loc_buffer p.bsrc) (MB.loc_buffer hd.bsrc))
      (ensures DV.as_seq (hs_of_mem m) (get_downview p.bsrc) == DV.as_seq m' (get_downview p.bsrc))
      = lemma_dv_equal (down_view p.src) p.bsrc (hs_of_mem m) m'
    in Classical.forall_intro (Classical.move_requires aux1);
    up_mem_aux h tl (hd::accu) (Mem m.ptrs m.addrs m')

let up_mem heap mem = up_mem_aux heap (ptrs_of_mem mem) [] mem

let rec down_up_identity_aux
  (h:heap)
  (ps:list b8)
  (accu:list b8)
  (m:mem{correct_down m h /\
    (forall p. List.memP p (ptrs_of_mem m) <==> List.memP p ps \/ List.memP p accu)})
  : Lemma (m == up_mem_aux h ps accu m) =
  match ps with
  | [] -> ()
  | hd::tl ->
    let s = get_seq_heap h (addrs_of_mem m) hd in
    let b = get_downview hd.bsrc in
    let m' = DV.upd_seq (hs_of_mem m) b s in
    DV.upd_seq_spec (hs_of_mem m) b s;    
    assert (Seq.equal s (DV.as_seq (hs_of_mem m) b));
    (* The previous assertion and lemma ensure that m == m' *)    
    down_up_identity_aux h tl (hd::accu) (Mem m.ptrs m.addrs m')

let down_up_identity mem =
  let heap = down_mem mem in
  down_up_identity_aux heap (ptrs_of_mem mem) [] mem

// Selecting a buffer index in any corresponding map of bytes always yields the same result
let correct_down_p_same_sel
  (mem:mem) 
  (heap1 heap2:heap)
  (x:int) 
  (b:b8) : Lemma
  (requires (x >= addrs_of_mem mem b /\ x < addrs_of_mem mem b + DV.length (get_downview b.bsrc) 
    /\ correct_down_p mem heap1 b /\ correct_down_p mem heap2 b))
  (ensures Map.sel heap1 x == Map.sel heap2 x) = 
    let addrs = addrs_of_mem mem in
    let i = x - addrs b in
    assert (heap1.[x] == UInt8.v (Seq.index (DV.as_seq (hs_of_mem mem) (get_downview b.bsrc)) i));
    assert (heap2.[x] == UInt8.v (Seq.index (DV.as_seq (hs_of_mem mem) (get_downview b.bsrc)) i))    

let rec up_down_identity_aux
  (mem:mem)
  (init_heap:heap{correct_down mem init_heap})
  (x:int) : Lemma 
  (requires Map.contains init_heap x)
  (ensures Map.sel init_heap x == Map.sel (down_mem mem) x) =
  let ptrs = ptrs_of_mem mem in
  let addrs = addrs_of_mem mem in
  Classical.forall_intro 
    (Classical.move_requires 
      (correct_down_p_same_sel mem (down_mem mem) init_heap x)
    )

let up_down_identity mem heap =
  let new_heap = down_mem (up_mem heap mem) in
  same_unspecified_down (hs_of_mem mem) (hs_of_mem (up_mem heap mem)) (ptrs_of_mem mem);
  let aux (x:int) : Lemma
    (requires Map.contains heap x)
    (ensures Map.sel heap x == Map.sel new_heap x) =
    up_down_identity_aux (up_mem heap mem) heap x
  in Classical.forall_intro (Classical.move_requires aux);
  assert (Map.equal heap new_heap)

#reset-options "--z3rlimit 50 --max_fuel 1 --max_ifuel 1 --initial_fuel 1 --initial_ifuel 1"

let rec update_buffer_up_mem_aux
  (h1 h2:heap)
  (ps:list b8)
  (accu:list b8)
  (b:b8)
  (m:mem{forall p. List.memP p (ptrs_of_mem m) <==> List.memP p ps \/ List.memP p accu}) : Lemma
  (requires 
    List.memP b (ptrs_of_mem m) /\
    Set.equal (Map.domain h1) (addrs_set m) /\ 
    Set.equal (Map.domain h2) (addrs_set m) /\
    (forall p. List.memP p accu ==> correct_down_p m h2 p) /\
    (List.memP b accu ==> DV.as_seq (hs_of_mem m) (get_downview b.bsrc) == get_seq_heap h2 (addrs_of_mem m) b) /\  
    (forall p. (p =!= b /\ List.memP p (ptrs_of_mem m)) ==> correct_down_p m h1 p) /\
    (forall x. x < addrs_of_mem m b \/ x >= addrs_of_mem m b + DV.length (get_downview b.bsrc) ==>
      h1.[x] == h2.[x])
  )
  (ensures
    (List.memP b accu ==> up_mem_aux h2 ps accu m == m) /\
    (~(List.memP b accu) ==> hs_of_mem (up_mem_aux h2 ps accu m) ==
      DV.upd_seq (hs_of_mem m) (get_downview b.bsrc) (get_seq_heap h2 (addrs_of_mem m) b))) =
  match ps with
  | [] -> ()
  | hd::tl -> 
    let db = get_downview hd.bsrc in
    let addrs = addrs_of_mem m in
    let mem = hs_of_mem m in
    let ptrs = ptrs_of_mem m in
    let s = get_seq_heap h2 addrs hd in
    DV.upd_seq_spec mem db s;
    let m' = DV.upd_seq mem db s in
    let aux1 (p:b8) : Lemma
      (requires MB.live (hs_of_mem m) p.bsrc /\
        MB.loc_disjoint (MB.loc_buffer p.bsrc) (MB.loc_buffer hd.bsrc))
      (ensures DV.as_seq (hs_of_mem m) (get_downview p.bsrc) == DV.as_seq m' (get_downview p.bsrc))
      = lemma_dv_equal (down_view p.src) p.bsrc (hs_of_mem m) m'
    in Classical.forall_intro (Classical.move_requires aux1);    
    let aux2 () : Lemma 
      (requires hd =!= b)
      (ensures DV.as_seq mem db == get_seq_heap h2 addrs hd) =
      get_seq_heap_as_seq h1 h2 m hd
    in Classical.move_requires aux2 ();
    update_buffer_up_mem_aux h1 h2 tl (hd::accu) b (Mem ptrs addrs m')

let update_buffer_up_mem m b h1 h2 = 
  let ptrs = ptrs_of_mem m in
  update_buffer_up_mem_aux h1 h2 ptrs [] b m
