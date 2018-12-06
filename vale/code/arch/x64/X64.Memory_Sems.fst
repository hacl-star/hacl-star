module X64.Memory_Sems

open Prop_s
open X64.Machine_s
open X64.Memory
open Words_s
module I = Interop
module S = X64.Bytes_Semantics_s
module B = LowStar.Buffer
module BV = LowStar.BufferView

friend X64.Memory

let same_domain h m = Set.equal (I.addrs_set h.ptrs h.addrs) (Map.domain m)

let lemma_same_domains h m1 m2 = ()

let get_heap h = I.down_mem h.hs h.addrs h.ptrs

let get_hs h m = 
  {h with hs = I.up_mem m h.addrs h.ptrs h.hs}

let get_hs_heap h = I.down_up_identity h.hs h.addrs h.ptrs

let get_heap_hs m h = I.up_down_identity h.hs h.addrs h.ptrs m


let bytes_valid ptr h =
  let t = TBase TUInt64 in
  let b = get_addr_ptr t ptr h h.ptrs in
  let i = get_addr_in_ptr t (buffer_length b) (buffer_addr b h) ptr 0 in
  in_bounds64 h b i;
  I.addrs_set_mem h.ptrs b h.addrs ptr;
  I.addrs_set_mem h.ptrs b h.addrs (ptr+1);
  I.addrs_set_mem h.ptrs b h.addrs (ptr+2);
  I.addrs_set_mem h.ptrs b h.addrs (ptr+3);
  I.addrs_set_mem h.ptrs b h.addrs (ptr+4);
  I.addrs_set_mem h.ptrs b h.addrs (ptr+5);
  I.addrs_set_mem h.ptrs b h.addrs (ptr+6);
  I.addrs_set_mem h.ptrs b h.addrs (ptr+7);
  ()

val same_mem_get_heap_val128 (b:buffer128)
                          (i:nat{i < buffer_length b})
                          (v:quad32)
                          (k:nat{k < buffer_length b})
                          (h1:mem{List.memP b h1.ptrs})
                          (h2:mem{h2 == buffer_write b i v h1})
                          (mem1:S.heap{I.correct_down_p h1.hs h1.addrs mem1 b})
                          (mem2:S.heap{I.correct_down_p h2.hs h2.addrs mem2 b}) : Lemma
  (requires (Seq.index (buffer_as_seq h1 b) k == Seq.index (buffer_as_seq h2 b) k))
  (ensures (let ptr = buffer_addr b h1 + 16 `op_Multiply` k in
    forall i. {:pattern (mem1.[ptr+i])} i >= 0 /\ i < 16 ==> mem1.[ptr+i] == mem2.[ptr+i]))

val same_mem_eq_slices128 (b:buffer128)
                       (i:nat{i < buffer_length b})
                       (v:quad32)
                       (k:nat{k < buffer_length b})
                       (h1:mem{List.memP b h1.ptrs})
                       (h2:mem{h2 == buffer_write b i v h1})
                       (mem1:S.heap{I.correct_down_p h1.hs h1.addrs mem1 b})
                       (mem2:S.heap{I.correct_down_p h2.hs h2.addrs mem2 b}) : Lemma
  (requires (Seq.index (buffer_as_seq h1 b) k == Seq.index (buffer_as_seq h2 b) k))
  (ensures (let open FStar.Mul in
    k * 16 + 16 <= B.length b /\
    Seq.slice (B.as_seq h1.hs b) (k * 16) (k * 16 + 16) ==
    Seq.slice (B.as_seq h2.hs b) (k * 16) (k * 16 + 16)))

let same_mem_eq_slices128 b i v k h1 h2 mem1 mem2 =
    let t = TBase TUInt128 in
    BV.as_seq_sel h1.hs (BV.mk_buffer_view b (uint_view t)) k;
    BV.as_seq_sel h2.hs (BV.mk_buffer_view b (uint_view t)) k;
    BV.put_sel h1.hs (BV.mk_buffer_view b (uint_view t)) k;
    BV.put_sel h2.hs (BV.mk_buffer_view b (uint_view t)) k;
    BV.as_buffer_mk_buffer_view b (uint_view t);
    BV.get_view_mk_buffer_view b (uint_view t);
    BV.view_indexing (BV.mk_buffer_view b (uint_view t)) k;
    BV.length_eq (BV.mk_buffer_view b (uint_view t))

let length_up128 (b:buffer128) (h:mem) (k:nat{k < buffer_length b}) (i:nat{i < 16}) : Lemma
  (16 `op_Multiply` k + i <= B.length b) =
  let vb = BV.mk_buffer_view b uint128_view in
  BV.length_eq vb;
  BV.as_buffer_mk_buffer_view b uint128_view;
  BV.get_view_mk_buffer_view b uint128_view;
  ()

let same_mem_get_heap_val128 b j v k h1 h2 mem1 mem2 =
  let ptr = buffer_addr b h1 + 16 `op_Multiply` k in
  let addr = buffer_addr b h1 in
  let aux (i:nat{i < 16}) : Lemma (mem1.[addr+(16 `op_Multiply` k + i)] == mem2.[addr+(16 `op_Multiply` k +i)]) =
    BV.as_seq_sel h1.hs (BV.mk_buffer_view b uint128_view) k;
    BV.as_seq_sel h2.hs (BV.mk_buffer_view b uint128_view) k;
    same_mem_eq_slices128 b j v k h1 h2 mem1 mem2;
    let open FStar.Mul in
    let s1 = (Seq.slice (B.as_seq h1.hs b) (k * 16) (k * 16 + 16)) in
    let s2 = (Seq.slice (B.as_seq h2.hs b) (k * 16) (k * 16 + 16)) in
    assert (Seq.index s1 i == Seq.index (B.as_seq h1.hs b) (k * 16 + i));
    length_up128 b h1 k i;
    assert (mem1.[addr+(16 * k + i)] == UInt8.v (Seq.index (B.as_seq h1.hs b) (k * 16 + i)));
    assert (Seq.index s2 i == Seq.index (B.as_seq h2.hs b) (k * 16 + i));
    length_up128 b h2 k i;
    assert (mem2.[addr+(16 * k + i)] == UInt8.v (Seq.index (B.as_seq h2.hs b) (k * 16 + i)));
    ()
  in
  Classical.forall_intro aux;
  assert (forall i. addr + (16 `op_Multiply` k + i) == ptr + i);
  ()

let rec written_buffer_down128_aux1 (b:buffer128) (i:nat{i < buffer_length b}) (v:quad32)
      (ps:list b8{I.list_disjoint_or_eq ps /\ List.memP b ps})
      (h:mem{forall x. List.memP x ps ==> List.memP x h.ptrs})
      (base:nat{base == buffer_addr b h})
      (k:nat) (h1:mem{h1 == buffer_write b i v h})
      (mem1:S.heap{I.correct_down h.hs h.addrs ps mem1})
      (mem2:S.heap{
      (I.correct_down h1.hs h.addrs ps mem2) /\
      (forall j. base <= j /\ j < base + k `op_Multiply` 16 ==> mem1.[j] == mem2.[j])}) :
      Lemma (requires True)
      (ensures (forall j. j >= base /\ j < base + 16 `op_Multiply` i ==> mem1.[j] == mem2.[j]))
      (decreases %[i-k]) =
    if k >= i then ()
    else begin
      let ptr = base + 16 `op_Multiply` k in
      same_mem_get_heap_val128 b i v k h h1 mem1 mem2;
      heap_shift mem1 mem2 ptr 16;
      written_buffer_down128_aux1 b i v ps h base (k+1) h1 mem1 mem2
    end

let rec written_buffer_down128_aux2 (b:buffer128) (i:nat{i < buffer_length b}) (v:quad32)
      (ps:list b8{I.list_disjoint_or_eq ps /\ List.memP b ps})
      (h:mem{forall x. List.memP x ps ==> List.memP x h.ptrs})
      (base:nat{base == buffer_addr b h})
      (n:nat{n == buffer_length b})
      (k:nat{k > i}) (h1:mem{h1 == buffer_write b i v h})
      (mem1:S.heap{I.correct_down h.hs h.addrs ps mem1})
      (mem2:S.heap{
      (I.correct_down h1.hs h.addrs ps mem2) /\
      (forall j. base + 16 `op_Multiply` (i+1) <= j /\ j < base + k `op_Multiply` 16 ==>
      mem1.[j] == mem2.[j])}) :
      Lemma
      (requires True)
      (ensures (forall j. j >= base + 16 `op_Multiply` (i+1) /\ j < base + 16 `op_Multiply` n ==>
        mem1.[j] == mem2.[j]))
      (decreases %[n-k]) =
    if k >= n then ()
    else begin
      let ptr = base + 16 `op_Multiply` k in
      same_mem_get_heap_val128 b i v k h h1 mem1 mem2;
      heap_shift mem1 mem2 ptr 16;
      written_buffer_down128_aux2 b i v ps h base n (k+1) h1 mem1 mem2
    end

let written_buffer_down128 (b:buffer128) (i:nat{i < buffer_length b}) (v:quad32)
  (ps: list b8{I.list_disjoint_or_eq ps /\ List.memP b ps}) (h:mem{forall x. List.memP x ps ==> List.memP x h.ptrs}) :
  Lemma (
    let mem1 = I.down_mem h.hs h.addrs ps in
    let h1 = buffer_write b i v h in
    let mem2 = I.down_mem h1.hs h.addrs ps in
    let base = buffer_addr b h in
    let n = buffer_length b in
    forall j. (base <= j /\ j < base + 16 `op_Multiply` i) \/
         (base + 16 `op_Multiply` (i+1) <= j /\ j < base + 16 `op_Multiply` n) ==>
         mem1.[j] == mem2.[j]) =
    let mem1 = I.down_mem h.hs h.addrs ps in
    let h1 = buffer_write b i v h in
    let mem2 = I.down_mem h1.hs h.addrs ps in
    let base = buffer_addr b h in
    let n = buffer_length b in
    written_buffer_down128_aux1 b i v ps h base 0 h1 mem1 mem2;
    written_buffer_down128_aux2 b i v ps h base n (i+1) h1 mem1 mem2

let store_buffer_down128_mem (b:buffer128) (i:nat{i < buffer_length b}) (v:quad32)
  (ps: list b8{I.list_disjoint_or_eq ps /\ List.memP b ps})
  (h:mem{forall x. List.memP x ps ==> List.memP x h.ptrs}) :
  Lemma (
    let mem1 = I.down_mem h.hs h.addrs ps in
    let h1 = buffer_write b i v h in
    let mem2 = I.down_mem h1.hs h.addrs ps in
    let base = buffer_addr b h in
    forall j. j < base + 16 `op_Multiply` i \/ j >= base + 16 `op_Multiply` (i+1) ==>
      mem1.[j] == mem2.[j]) =
    let mem1 = I.down_mem h.hs h.addrs ps in
    let h1 = buffer_write b i v h in
    let mem2 = I.down_mem h1.hs h.addrs ps in
    let base = buffer_addr b h in
    let n = buffer_length b in
    let aux (j:int) : Lemma
      (j < base + 16 `op_Multiply` i \/ j >= base + 16 `op_Multiply` (i+1) ==>
      mem1.[j] == mem2.[j]) =
        if j >= base && j < base + B.length b then begin
          written_buffer_down128 b i v ps h;
          length_t_eq (TBase TUInt128) b
        end
        else (
        I.same_unspecified_down h.hs h1.hs h.addrs ps;
        unwritten_buffer_down (TBase TUInt128) b i v ps h;
        ()
        )
    in Classical.forall_intro aux

let store_buffer_aux_down128_mem (ptr:int) (v:quad32) (h:mem{valid_mem128 ptr h}) : Lemma (
  let mem1 = I.down_mem h.hs h.addrs h.ptrs in
  let h1 = store_mem_aux (TBase TUInt128) ptr h.ptrs v h in
  let mem2 = I.down_mem h1.hs h.addrs h.ptrs in
  forall j. j < ptr \/ j >= ptr + 16 ==> mem1.[j] == mem2.[j]) =
  let t = TBase TUInt128 in
  let h1 = store_mem_aux t ptr h.ptrs v h in
  let b = get_addr_ptr t ptr h h.ptrs in
  length_t_eq t b;
  let i = get_addr_in_ptr t (buffer_length b) (buffer_addr b h) ptr 0 in
  store_buffer_write t ptr v h h.ptrs;
  assert (buffer_addr b h + 16 `op_Multiply` i == ptr);
  assert (buffer_addr b h + 16 `op_Multiply` (i+1) == ptr + 16);
  store_buffer_down128_mem b i v h.ptrs h

let store_buffer_aux_down128_mem2 (ptr:int) (v:quad32) (h:mem{valid_mem128 ptr h}) : Lemma (
  let h1 = store_mem_aux (TBase TUInt128) ptr h.ptrs v h in
  let mem2 = I.down_mem h1.hs h.addrs h.ptrs in
  Mkfour
    (S.get_heap_val32 ptr mem2)
    (S.get_heap_val32 (ptr+4) mem2)
    (S.get_heap_val32 (ptr+8) mem2)
    (S.get_heap_val32 (ptr+12) mem2)
  == v) =
  let t = TBase TUInt128 in
  let b = get_addr_ptr t ptr h h.ptrs in
  length_t_eq t b;
  let i = get_addr_in_ptr t (buffer_length b) (buffer_addr b h) ptr 0 in
  let h1 = store_mem_aux t ptr h.ptrs v h in
  let mem2 = I.down_mem h1.hs h.addrs h.ptrs in
  store_buffer_write t ptr v h h.ptrs;
  assert (Seq.index (buffer_as_seq h1 b) i == v);
  index128_get_heap_val128 h1 b mem2 i;
  ()

let in_bounds128 (h:mem) (b:buffer128) (i:nat{i < buffer_length b}) : Lemma
  (forall j. j >= h.addrs b + 16 `op_Multiply` i /\ j < h.addrs b + 16 `op_Multiply` i + 16 ==>
    j < h.addrs b + B.length b) =
  length_t_eq (TBase TUInt128) b;
  ()

let bytes_valid128 ptr h =
  let t = TBase TUInt128 in
  let b = get_addr_ptr t ptr h h.ptrs in
  let i = get_addr_in_ptr t (buffer_length b) (buffer_addr b h) ptr 0 in
  in_bounds128 h b i;
  I.addrs_set_mem h.ptrs b h.addrs ptr;
  I.addrs_set_mem h.ptrs b h.addrs (ptr+1);
  I.addrs_set_mem h.ptrs b h.addrs (ptr+2);
  I.addrs_set_mem h.ptrs b h.addrs (ptr+3);
  I.addrs_set_mem h.ptrs b h.addrs (ptr+4);
  I.addrs_set_mem h.ptrs b h.addrs (ptr+5);
  I.addrs_set_mem h.ptrs b h.addrs (ptr+6);
  I.addrs_set_mem h.ptrs b h.addrs (ptr+7);
  I.addrs_set_mem h.ptrs b h.addrs (ptr+8);
  I.addrs_set_mem h.ptrs b h.addrs (ptr+9);
  I.addrs_set_mem h.ptrs b h.addrs (ptr+10);
  I.addrs_set_mem h.ptrs b h.addrs (ptr+11);
  I.addrs_set_mem h.ptrs b h.addrs (ptr+12);
  I.addrs_set_mem h.ptrs b h.addrs (ptr+13);
  I.addrs_set_mem h.ptrs b h.addrs (ptr+14);
  I.addrs_set_mem h.ptrs b h.addrs (ptr+15);
  ()
  
let equiv_load_mem ptr h =
  let t = TBase TUInt64 in
  let b = get_addr_ptr t ptr h h.ptrs in
  let i = get_addr_in_ptr t (buffer_length b) (buffer_addr b h) ptr 0 in
  let addr = buffer_addr b h in
  let contents = B.as_seq h.hs b in
  let heap = get_heap h in
  index64_get_heap_val64 h b heap i;
  lemma_load_mem64 b i h

let low_lemma_valid_mem64 b i h = 
  lemma_valid_mem64 b i h;
  bytes_valid (buffer_addr b h + 8 `op_Multiply` i) h

let low_lemma_load_mem64 b i h =
  lemma_valid_mem64 b i h;
  lemma_load_mem64 b i h;
  equiv_load_mem (buffer_addr b h + 8 `op_Multiply` i) h

let same_domain_update64 b i v h =
  low_lemma_valid_mem64 b i h;
  X64.Bytes_Semantics.same_domain_update (buffer_addr b h + 8 `op_Multiply` i) v (get_heap h)

open X64.BufferViewStore

let low_lemma_store_mem64_aux 
  (b:buffer64)
  (heap:S.heap)
  (i:nat{i < buffer_length b})
  (v:nat64)
  (h:mem{buffer_readable h b})
  : Lemma
    (requires I.correct_down_p h.hs h.addrs heap b)
    (ensures (let heap' = S.update_heap64 (buffer_addr b h + 8 `op_Multiply` i) v heap in
     let h' = store_mem64 (buffer_addr b h + 8 `op_Multiply` i) v h in
     h'.hs == B.g_upd_seq b (I.get_seq_heap heap' h.addrs b) h.hs)) =
   let ptr = buffer_addr b h + 8 `op_Multiply` i in
   let heap' = S.update_heap64 ptr v heap in
   let h' = store_mem64 ptr v h in
   length_t_eq (TBase TUInt64) b;
   store_buffer_write (TBase TUInt64) ptr v h h.ptrs;
   let b' = get_addr_ptr (TBase TUInt64) ptr h h.ptrs in
   assert (I.disjoint_or_eq b b');
   length_t_eq (TBase TUInt64) b';
   bv_upd_update_heap64 b heap i v h.addrs h.ptrs h.hs


val valid_state_store_mem64_aux: (i:int) -> (v:nat64) -> (h:mem) -> Lemma 
  (requires valid_mem64 i h)
  (ensures (
    let heap = get_heap h in
    let heap' = S.update_heap64 i v heap in
    let h' = store_mem64 i v h in
    heap' == I.down_mem h'.hs h'.addrs h'.ptrs 
  ))

let valid_state_store_mem64_aux i v h =
  let heap = get_heap h in
  let heap' = S.update_heap64 i v heap in
  let h1 = store_mem_aux (TBase TUInt64) i h.ptrs v h in
  store_buffer_aux_down64_mem i v h;
  store_buffer_aux_down64_mem2 i v h;
  let mem1 = heap' in
  let mem2 = I.down_mem h1.hs h.addrs h.ptrs in
  let aux () : Lemma (forall j. mem1.[j] == mem2.[j]) =
    Bytes_Semantics.same_mem_get_heap_val i mem1 mem2;
    Bytes_Semantics.correct_update_get i v heap;
    Bytes_Semantics.frame_update_heap i v heap
  in let aux2 () : Lemma (Set.equal (Map.domain mem1) (Map.domain mem2)) =
    bytes_valid i h;
    Bytes_Semantics.same_domain_update i v heap
  in aux(); aux2();
  Map.lemma_equal_intro mem1 mem2;
  ()
  
let low_lemma_store_mem64 b i v h =
  lemma_valid_mem64 b i h;
  lemma_store_mem64 b i v h;
  valid_state_store_mem64_aux (buffer_addr b h + 8 `op_Multiply` i) v h;
  let heap = get_heap h in
  let heap' = S.update_heap64 (buffer_addr b h + 8 `op_Multiply` i) v heap in
  let h' = store_mem64 (buffer_addr b h + 8 `op_Multiply` i) v h in
  low_lemma_store_mem64_aux b heap i v h;
  length_t_eq (TBase TUInt64) b;
  X64.Bytes_Semantics.frame_update_heap (buffer_addr b h + 8 `op_Multiply` i) v heap;
  I.update_buffer_up_mem h.ptrs h.addrs h.hs b heap heap'  

let low_lemma_valid_mem128 b i h =
  lemma_valid_mem128 b i h;
  bytes_valid128 (buffer_addr b h + 16 `op_Multiply` i) h

val equiv_load_mem128_aux: (ptr:int) -> (h:mem) -> Lemma
  (requires valid_mem128 ptr h)
  (ensures load_mem128 ptr h == S.get_heap_val128 ptr (get_heap h))

let equiv_load_mem128_aux ptr h =
  let t = TBase TUInt128 in
  let b = get_addr_ptr t ptr h h.ptrs in
  let i = get_addr_in_ptr t (buffer_length b) (buffer_addr b h) ptr 0 in
  let addr = buffer_addr b h in
  let contents = B.as_seq h.hs b in
  let heap = get_heap h in
  Opaque_s.reveal_opaque S.get_heap_val128_def;
  index128_get_heap_val128 h b heap i;
  lemma_load_mem128 b i h

let low_lemma_load_mem128 b i h =
  lemma_valid_mem128 b i h;
  lemma_load_mem128 b i h;
  equiv_load_mem128_aux (buffer_addr b h + 16 `op_Multiply` i) h  

let same_domain_update128 b i v h =
  low_lemma_valid_mem128 b i h;
  X64.Bytes_Semantics.same_domain_update128 (buffer_addr b h + 16 `op_Multiply` i) v (get_heap h)

let low_lemma_store_mem128_aux 
  (b:buffer128)
  (heap:S.heap)
  (i:nat{i < buffer_length b})
  (v:quad32)
  (h:mem{buffer_readable h b})
  : Lemma
    (requires I.correct_down_p h.hs h.addrs heap b)
    (ensures (let heap' = S.update_heap128 (buffer_addr b h + 16 `op_Multiply` i) v heap in
     let h' = store_mem128 (buffer_addr b h + 16 `op_Multiply` i) v h in
     h'.hs == B.g_upd_seq b (I.get_seq_heap heap' h.addrs b) h.hs)) =
   let ptr = buffer_addr b h + 16 `op_Multiply` i in
   let heap' = S.update_heap128 ptr v heap in
   let h' = store_mem128 ptr v h in
   length_t_eq (TBase TUInt128) b;
   store_buffer_write (TBase TUInt128) ptr v h h.ptrs;
   let b' = get_addr_ptr (TBase TUInt128) ptr h h.ptrs in
   assert (I.disjoint_or_eq b b');
   length_t_eq (TBase TUInt128) b';
   bv_upd_update_heap128 b heap i v h.addrs h.ptrs h.hs

val valid_state_store_mem128_aux: (i:int) -> (v:quad32) -> (h:mem) -> Lemma 
  (requires valid_mem128 i h)
  (ensures (
    let heap = get_heap h in
    let heap' = S.update_heap128 i v heap in
    let h' = store_mem128 i v h in
    heap' == I.down_mem h'.hs h'.addrs h'.ptrs 
  ))

let valid_state_store_mem128_aux i v h =
  let heap = get_heap h in
  let heap' = S.update_heap128 i v heap in
  let h1 = store_mem_aux (TBase TUInt128) i h.ptrs v h in
  store_buffer_aux_down128_mem i v h;
  store_buffer_aux_down128_mem2 i v h;
  let mem1 = heap' in
  let mem2 = I.down_mem h1.hs h.addrs h.ptrs in
  let aux () : Lemma (forall j. mem1.[j] == mem2.[j]) =
    Bytes_Semantics.correct_update_get128 i v heap;
    Opaque_s.reveal_opaque Bytes_Semantics_s.get_heap_val128_def;
    Bytes_Semantics.same_mem_get_heap_val32 i mem1 mem2;
    Bytes_Semantics.same_mem_get_heap_val32 (i+4) mem1 mem2;
    Bytes_Semantics.same_mem_get_heap_val32 (i+8) mem1 mem2;
    Bytes_Semantics.same_mem_get_heap_val32 (i+12) mem1 mem2;
    Bytes_Semantics.frame_update_heap128 i v heap
  in
  let aux2 () : Lemma (Set.equal (Map.domain mem1) (Map.domain mem2)) =
    bytes_valid128 i h;
    Bytes_Semantics.same_domain_update128 i v heap
  in aux (); aux2 ();
  Map.lemma_equal_intro mem1 mem2

let low_lemma_store_mem128 b i v h =
  lemma_valid_mem128 b i h;
  lemma_store_mem128 b i v h;
  valid_state_store_mem128_aux (buffer_addr b h + 16 `op_Multiply` i) v h;
  let heap = get_heap h in
  let heap' = S.update_heap128 (buffer_addr b h + 16 `op_Multiply` i) v heap in
  let h' = store_mem128 (buffer_addr b h + 16 `op_Multiply` i) v h in
  low_lemma_store_mem128_aux b heap i v h;  
  length_t_eq (TBase TUInt128) b;
  X64.Bytes_Semantics.frame_update_heap128 (buffer_addr b h + 16 `op_Multiply` i) v heap;
  I.update_buffer_up_mem h.ptrs h.addrs h.hs b heap heap'
