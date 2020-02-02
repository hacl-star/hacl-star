module Vale.X64.Memory_Sems

open FStar.Mul
open Vale.Def.Prop_s
open Vale.Def.Opaque_s
open Vale.X64.Machine_s
open Vale.X64.Memory
open Vale.Def.Words_s
module I = Vale.Interop
module S = Vale.X64.Machine_Semantics_s
module MB = LowStar.Monotonic.Buffer
module UV = LowStar.BufferView.Up
module DV = LowStar.BufferView.Down
open Vale.Lib.BufferViewHelpers
open Vale.Arch.HeapImpl
open Vale.Arch.Heap

friend Vale.X64.Memory
module IB = Vale.Interop.Base

let same_domain h m = Set.equal (IB.addrs_set (_ih h)) (Map.domain m)

let lemma_same_domains h m1 m2 = ()

let get_heap h = I.down_mem (_ih h)

let upd_heap h m = mi_heap_upd h m

//let lemma_upd_get_heap h = I.down_up_identity (_ih h)

let lemma_get_upd_heap h m = I.up_down_identity (_ih h) m

let lemma_heap_impl = ()

let lemma_heap_get_heap h = ()

let lemma_heap_taint h = ()

//let lemma_heap_upd_heap h mh mt = ()

[@"opaque_to_smt"]
let rec set_of_range (a:int) (n:nat) : Pure (Set.set int)
  (requires True)
  (ensures fun s -> (forall (i:int).{:pattern Set.mem i s} Set.mem i s <==> a <= i /\ i < a + n))
  =
  if n = 0 then Set.empty else Set.union (set_of_range a (n - 1)) (Set.singleton (a + n - 1))

let buffer_info_has_addr (bi:buffer_info) (a:int) =
  let b = bi.bi_buffer in
  let addr = Vale.Interop.Heap_s.global_addrs_map b in
  let len = DV.length (get_downview b.bsrc) in
  addr <= a /\ a < addr + len

let buffer_info_has_addr_opt (bi:option buffer_info) (a:int) =
  match bi with
  | None -> False
  | Some bi -> buffer_info_has_addr bi a

#set-options "--z3rlimit 100"
let rec make_owns_rec (h:vale_heap) (bs:Seq.seq buffer_info) (n:nat{n <= Seq.length bs}) :
  GTot ((int -> option (n:nat{n < Seq.length bs})) & (heaplet_id -> Set.set int))
  =
  if n = 0 then ((fun _ -> None), (fun _ -> Set.empty)) else
  let (m0, s0) = make_owns_rec h bs (n - 1) in
  let bi = Seq.index bs (n - 1) in
  let b = bi.bi_buffer in
  let hi = bi.bi_heaplet in
  let addr = Vale.Interop.Heap_s.global_addrs_map b in
  let len = DV.length (get_downview b.bsrc) in
  let s_b = set_of_range addr len in
  let s i = if i = hi then Set.union (s0 i) s_b else s0 i in
  let m a = if addr <= a && a < addr + len then Some (n - 1) else m0 a in
  (m, s)

[@"opaque_to_smt"]
let make_owns (h:vale_heap) (bs:Seq.seq buffer_info) (n:nat{n <= Seq.length bs}) :
  GTot ((int -> option (n:nat{n < Seq.length bs})) & (heaplet_id -> Set.set int))
  =
  make_owns_rec h bs n

let rec lemma_make_owns (h:vale_heap) (bs:Seq.seq buffer_info) (n:nat) : Lemma
  (requires
    n <= Seq.length bs /\
    (forall (i:nat).{:pattern Seq.index bs i} i < Seq.length bs ==> buffer_readable h (Seq.index bs i).bi_buffer) /\
    (forall (i1 i2:nat).{:pattern (Seq.index bs i1); (Seq.index bs i2)}
      i1 < Seq.length bs /\ i2 < Seq.length bs ==> buffer_info_disjoint (Seq.index bs i1) (Seq.index bs i2))
  )
  (ensures (
    let (m, s) = make_owns h bs n in
    (forall (i:heaplet_id) (a:int).{:pattern Set.mem a (s i)}
      (Set.mem a (s i) <==> Option.mapTot (fun n -> (Seq.index bs n).bi_heaplet) (m a) == Some i) /\
      (Set.mem a (s i) ==> buffer_info_has_addr_opt (Option.mapTot (fun n -> Seq.index bs n) (m a)) a) /\
      (Set.mem a (s i) ==> Set.mem a (Map.domain h.mh))
    ) /\
    (forall (k:nat) (a:int).{:pattern Set.mem a (s (Seq.index bs k).bi_heaplet)}
      k < n /\ buffer_info_has_addr (Seq.index bs k) a ==> Set.mem a (s (Seq.index bs k).bi_heaplet))
  ))
  =
  reveal_opaque (`%make_owns) make_owns;
  if n = 0 then () else
  let _ = make_owns h bs (n - 1) in
  let (m, s) = make_owns h bs n in
  lemma_make_owns h bs (n - 1);
  let bi = Seq.index bs (n - 1) in
  let b = bi.bi_buffer in
  let hi = bi.bi_heaplet in
  let addr = Vale.Interop.Heap_s.global_addrs_map b in
  let len = DV.length (get_downview b.bsrc) in
  let s_b = set_of_range addr len in
  let lem1 (a:int) : Lemma
    (requires Set.mem a s_b)
    (ensures Set.mem a (Map.domain h.mh))
    [SMTPat (Set.mem a (Map.domain h.mh))]
    =
    I.addrs_set_mem h.ih b a
    in
  let lem2 (i:heaplet_id) (a:int) : Lemma
    (requires i =!= hi /\ Set.mem a (Set.intersect s_b (s i)))
    (ensures False)
    [SMTPat (Set.mem a (s i))]
    =
    reveal_opaque (`%addr_map_pred) addr_map_pred
    in
  ()

#push-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 2 --max_ifuel 2"
let rec lemma_loc_mutable_buffers_rec (l:list buffer_info) (s:Seq.seq buffer_info) (n:nat) : Lemma
  (requires
    n + List.length l == Seq.length s /\
    list_to_seq_post l s n
  )
  (ensures (
    let modloc = loc_mutable_buffers l in
    forall (i:nat).{:pattern Seq.index s i} n <= i /\ i < Seq.length s ==> (
      let bi = Seq.index s i in
      bi.bi_mutable == Mutable ==> loc_includes modloc (loc_buffer bi.bi_buffer))
  ))
  (decreases l)
  =
  match l with
  | [] -> ()
  | h::t -> lemma_loc_mutable_buffers_rec t s (n + 1)
#pop-options

let lemma_loc_mutable_buffers (l:list buffer_info) : Lemma
  (ensures (
    let s = list_to_seq l in
    forall (i:nat).{:pattern Seq.index s i} i < Seq.length s ==> (
      let bi = Seq.index s i in
      bi.bi_mutable == Mutable ==> loc_includes (loc_mutable_buffers l) (loc_buffer bi.bi_buffer))
  ))
  =
  lemma_list_to_seq l;
  lemma_loc_mutable_buffers_rec l (list_to_seq l) 0

let create_heaplets buffers h1 =
  let bs = list_to_seq buffers in
  let modloc = loc_mutable_buffers buffers in
  let layout1 = h1.vf_layout in
  let layin1 = layout1.vl_inner in
  let (hmap, hsets) = make_owns h1.vf_heap bs (Seq.length bs) in
  let hmap a = Option.mapTot (fun n -> (Seq.index bs n).bi_heaplet) (hmap a) in
  let l = {
    vl_heaplets_initialized = true;
    vl_heaplet_map = hmap;
    vl_heaplet_sets = hsets;
    vl_old_heap = h1.vf_heap;
    vl_buffers = bs;
    vl_mod_loc = modloc;
  } in
  let layout2 = {layout1 with vl_inner = l} in
  let h2 = {
    vf_layout = layout2;
    vf_heap = h1.vf_heap;
    vf_heaplets = h1.vf_heaplets;
  } in
  h2

let lemma_create_heaplets buffers h1 =
  let bs = list_to_seq buffers in
  let h2 = create_heaplets buffers h1 in
  assert (h2.vf_layout.vl_inner.vl_buffers == bs); // REVIEW: why is this necessary, even with extra ifuel?
  lemma_make_owns h1.vf_heap bs (Seq.length bs);
  lemma_loc_mutable_buffers buffers;
  reveal_opaque (`%valid_layout_buffer_id) valid_layout_buffer_id;
  ()

let destroy_heaplets h1 =
  h1

let lemma_destroy_heaplets h1 =
  ()

val heap_shift (m1 m2:S.machine_heap) (base:int) (n:nat) : Lemma
  (requires (forall i. 0 <= i /\ i < n ==> m1.[base + i] == m2.[base + i]))
  (ensures (forall i. {:pattern (m1.[i])} base <= i /\ i < base + n ==> m1.[i] == m2.[i]))

#push-options "--smtencoding.l_arith_repr boxwrap"
let heap_shift m1 m2 base n =
  assert (forall i. base <= i /\ i < base + n ==>
    m1.[base + (i - base)] == m2.[base + (i - base)])
#pop-options

val same_mem_eq_slices64 (b:buffer64{buffer_writeable b})
                       (i:nat{i < buffer_length b})
                       (v:nat64)
                       (k:nat{k < buffer_length b})
                       (h1:vale_heap{List.memP b (IB.ptrs_of_mem (_ih h1))})
                       (h2:vale_heap{h2 == buffer_write b i v h1})
                       (mem1:S.machine_heap{IB.correct_down_p (_ih h1) mem1 b})
                       (mem2:S.machine_heap{IB.correct_down_p (_ih h2) mem2 b}) : Lemma
  (requires (Seq.index (buffer_as_seq h1 b) k == Seq.index (buffer_as_seq h2 b) k))
  (ensures (
    k * 8 + 8 <= DV.length (get_downview b.bsrc) /\
    Seq.slice (DV.as_seq (IB.hs_of_mem (_ih h1)) (get_downview b.bsrc)) (k * 8) (k * 8 + 8) ==
    Seq.slice (DV.as_seq (IB.hs_of_mem (_ih h2)) (get_downview b.bsrc)) (k * 8) (k * 8 + 8)))

let same_mem_eq_slices64 b i v k h1 h2 mem1 mem2 =
    let t = TUInt64 in
    let db = get_downview b.bsrc in
    let ub = UV.mk_buffer db (uint_view t) in
    UV.as_seq_sel (IB.hs_of_mem (_ih h1)) ub k;
    UV.as_seq_sel (IB.hs_of_mem (_ih h2)) ub k;
    UV.put_sel (IB.hs_of_mem (_ih h1)) ub k;
    UV.put_sel (IB.hs_of_mem (_ih h2)) ub k;
    UV.length_eq ub

let length_up64 (b:buffer64) (h:vale_heap) (k:nat{k < buffer_length b}) (i:nat{i < 8}) : Lemma
  (scale8 k + i <= DV.length (get_downview b.bsrc)) =
  let vb = UV.mk_buffer (get_downview b.bsrc) uint64_view in
  UV.length_eq vb

val same_mem_get_heap_val64 (b:buffer64{buffer_writeable b})
                          (i:nat{i < buffer_length b})
                          (v:nat64)
                          (k:nat{k < buffer_length b})
                          (h1:vale_heap{List.memP b (IB.ptrs_of_mem (_ih h1))})
                          (h2:vale_heap{h2 == buffer_write b i v h1})
                          (mem1:S.machine_heap{IB.correct_down_p (_ih h1) mem1 b})
                          (mem2:S.machine_heap{IB.correct_down_p (_ih h2) mem2 b}) : Lemma
  (requires (Seq.index (buffer_as_seq h1 b) k == Seq.index (buffer_as_seq h2 b) k))
  (ensures (let ptr = buffer_addr b h1 + scale8 k in
    forall (x:int).{:pattern (mem1.[x])} ptr <= x /\ x < ptr + 8 ==> mem1.[x] == mem2.[x]))

let same_mem_get_heap_val64 b j v k h1 h2 mem1 mem2 =
  let ptr = buffer_addr b h1 + scale8 k in
  let addr = buffer_addr b h1 in
  let aux (x:int{ptr <= x /\ x < ptr + 8}) : Lemma (mem1.[x] == mem2.[x]) =
    let i = x - ptr in
    let db = get_downview b.bsrc in
    let ub = UV.mk_buffer db uint64_view in
    UV.as_seq_sel (IB.hs_of_mem (_ih h1)) ub k;
    UV.as_seq_sel (IB.hs_of_mem (_ih h2)) ub k;
    same_mem_eq_slices64 b j v k h1 h2 mem1 mem2;
    let s1 = (Seq.slice (DV.as_seq (IB.hs_of_mem (_ih h1)) db) (k * 8) (k * 8 + 8)) in
    let s2 = (Seq.slice (DV.as_seq (IB.hs_of_mem (_ih h2)) db) (k * 8) (k * 8 + 8)) in
    assert (Seq.index s1 i == Seq.index (DV.as_seq (IB.hs_of_mem (_ih h1)) db) (k * 8 + i));
    length_up64 b h1 k i;
    assert (mem1.[addr+(scale8 k + i)] == UInt8.v (Seq.index (DV.as_seq (IB.hs_of_mem (_ih h1)) db) (k * 8 + i)));
    assert (Seq.index s2 i == Seq.index (DV.as_seq (IB.hs_of_mem (_ih h2)) db) (k * 8 + i));
    length_up64 b h2 k i;
    assert (mem2.[addr+(scale8 k + i)] == UInt8.v (Seq.index (DV.as_seq (IB.hs_of_mem (_ih h2)) db) (k * 8 + i)))
  in
  Classical.forall_intro aux;
  assert (forall i. addr + (scale8 k + i) == ptr + i)

let rec written_buffer_down64_aux1
  (b:buffer64{buffer_writeable b})
  (i:nat{i < buffer_length b})
  (v:nat64)
  (h:vale_heap{List.memP b (IB.ptrs_of_mem (_ih h))})
  (base:nat{base == buffer_addr b h})
  (k:nat) (h1:vale_heap{h1 == buffer_write b i v h})
  (mem1:S.machine_heap{IB.correct_down (_ih h) mem1})
  (mem2:S.machine_heap{IB.correct_down (_ih h1) mem2 /\
               (forall j.{:pattern (mem1.[j]) \/ (mem2.[j])}
                 base <= j /\ j < base + k * 8 ==>
                 mem1.[j] == mem2.[j])})
  : Lemma
      (ensures (forall j. {:pattern (mem1.[j]) \/ (mem1.[j])}
                  j >= base /\ j < base + scale8 i ==>
                  mem1.[j] == mem2.[j]))
      (decreases %[i-k]) =
    if k >= i then ()
    else begin
      let ptr = base + scale8 k in
      same_mem_get_heap_val64 b i v k h h1 mem1 mem2;
      heap_shift mem1 mem2 ptr 8;
      written_buffer_down64_aux1 b i v h base (k+1) h1 mem1 mem2
    end

let rec written_buffer_down64_aux2
  (b:buffer64{buffer_writeable b})
  (i:nat{i < buffer_length b})
  (v:nat64)
  (h:vale_heap{List.memP b (IB.ptrs_of_mem (_ih h))})
  (base:nat{base == buffer_addr b h})
  (n:nat{n == buffer_length b})
  (k:nat{k > i}) (h1:vale_heap{h1 == buffer_write b i v h})
  (mem1:S.machine_heap{IB.correct_down (_ih h) mem1})
  (mem2:S.machine_heap{IB.correct_down (_ih h1) mem2 /\
               (forall j. {:pattern (mem1.[j]) \/ (mem2.[j])}
                 base + scale8 (i+1) <= j /\ j < base + k * 8 ==>
                 mem1.[j] == mem2.[j])})
  : Lemma
      (ensures (forall j. {:pattern (mem1.[j]) \/ (mem2.[j])}
                     j >= base + scale8 (i+1) /\ j < base + scale8 n ==>
                     mem1.[j] == mem2.[j]))
      (decreases %[n-k]) =
    if k >= n then ()
    else begin
      let ptr = base + scale8 k in
      same_mem_get_heap_val64 b i v k h h1 mem1 mem2;
      heap_shift mem1 mem2 ptr 8;
      written_buffer_down64_aux2 b i v h base n (k+1) h1 mem1 mem2
    end

let written_buffer_down64 (b:buffer64{buffer_writeable b}) (i:nat{i < buffer_length b}) (v:nat64) (h:vale_heap)
  : Lemma
      (requires List.memP b (IB.ptrs_of_mem (_ih h)))
      (ensures (
          let mem1 = I.down_mem (_ih h) in
          let h1 = buffer_write b i v h in
          let mem2 = I.down_mem (_ih h1) in
          let base = buffer_addr b h in
          let n = buffer_length b in
          forall j. {:pattern (mem1.[j]) \/ (mem2.[j])}
               (base <= j /\ j < base + scale8 i) \/
               (base + scale8 (i+1) <= j /\ j < base + scale8 n) ==>
               mem1.[j] == mem2.[j]))
  = let mem1 = I.down_mem (_ih h) in
    let h1 = buffer_write b i v h in
    let mem2 = I.down_mem (_ih h1) in
    let base = buffer_addr b h in
    let n = buffer_length b in
    written_buffer_down64_aux1 b i v h base 0 h1 mem1 mem2;
    written_buffer_down64_aux2 b i v h base n (i+1) h1 mem1 mem2

let unwritten_buffer_down (t:base_typ) (b:buffer t{buffer_writeable b})
                          (i:nat{i < buffer_length b})
                          (v:base_typ_as_vale_type t)
                          (h:vale_heap{List.memP b (IB.ptrs_of_mem (_ih h))})
  : Lemma
      (ensures (
        let mem1 = I.down_mem (_ih h) in
        let h1 = buffer_write b i v h in
        let mem2 = I.down_mem (_ih h1) in
        forall  (a:b8{List.memP a (IB.ptrs_of_mem (_ih h)) /\ a =!= b}) j. {:pattern mem1.[j]; List.memP a (IB.ptrs_of_mem (_ih h)) \/ mem2.[j]; List.memP a (IB.ptrs_of_mem (_ih h))}
          let base = (IB.addrs_of_mem (_ih h)) a in
          j >= base /\ j < base + DV.length (get_downview a.bsrc) ==> mem1.[j] == mem2.[j]))
  = let aux (a:b8{a =!= b /\ List.memP a (IB.ptrs_of_mem (_ih h))})
      : Lemma
        (ensures (
          let base = (IB.addrs_of_mem (_ih h)) a in
          let mem1 = I.down_mem (_ih h) in
          let h1 = buffer_write b i v h in
          let mem2 = I.down_mem (_ih h1) in
          forall j.
            j >= base /\ j < base + DV.length (get_downview a.bsrc) ==>
            mem1.[j] == mem2.[j]))
      = let db = get_downview a.bsrc in
        if DV.length db = 0 then ()
        else
          let mem1 = I.down_mem (_ih h) in
          let h1 = buffer_write b i v h in
          let mem2 = I.down_mem (_ih h1) in
          let base = (IB.addrs_of_mem (_ih h)) a in
          let s0 = DV.as_seq (IB.hs_of_mem (_ih h)) db in
          let s1 = DV.as_seq (IB.hs_of_mem (_ih h1)) db in
          opaque_assert (`%IB.list_disjoint_or_eq) IB.list_disjoint_or_eq IB.list_disjoint_or_eq_def (MB.disjoint a.bsrc b.bsrc);
          lemma_dv_equal (IB.down_view a.src) a.bsrc (IB.hs_of_mem (_ih h)) (IB.hs_of_mem (_ih h1));
          assert (Seq.equal s0 s1);
          assert (forall (j:int).{:pattern (mem1.[j])}
            base <= j /\ j < base + Seq.length s0 ==> v_to_typ TUInt8 (Seq.index s0 (j - base)) == mem1.[j]);
          heap_shift mem1 mem2 base (DV.length db)
    in
    Classical.forall_intro aux

let store_buffer_down64_mem
  (b:buffer64{buffer_writeable b})
  (i:nat{i < buffer_length b})
  (v:nat64)
  (h:vale_heap{List.memP b (IB.ptrs_of_mem (_ih h))})
  : Lemma
      (ensures (
        let mem1 = I.down_mem (_ih h) in
        let h1 = buffer_write b i v h in
        let mem2 = I.down_mem (_ih h1) in
        let base = buffer_addr b h in
        forall (j:int). {:pattern mem1.[j] \/ mem2.[j]}
          j < base + scale8 i \/ j >= base + scale8 (i+1) ==>
          mem1.[j] == mem2.[j]))
  = let mem1 = I.down_mem (_ih h) in
    let h1 = buffer_write b i v h in
    let mem2 = I.down_mem (_ih h1) in
    let base = buffer_addr b h in
    let n = buffer_length b in
    let aux (j:int)
      : Lemma
          (j < base + scale8 i \/ j >= base + scale8 (i+1) ==>
           mem1.[j] == mem2.[j])
      =
      I.addrs_set_lemma_all ();
      if j >= base && j < base + DV.length (get_downview b.bsrc) then begin
          written_buffer_down64 b i v h;
          length_t_eq (TUInt64) b
        end
        else if not (I.valid_addr (_ih h) j)
        then I.same_unspecified_down (IB.hs_of_mem (_ih h)) (IB.hs_of_mem (_ih h1)) (IB.ptrs_of_mem (_ih h))
        else unwritten_buffer_down TUInt64 b i v h
    in
    Classical.forall_intro aux

let store_buffer_aux_down64_mem (ptr:int) (v:nat64) (h:vale_heap{writeable_mem64 ptr h})
  : Lemma
      (ensures (
        let mem1 = I.down_mem (_ih h) in
        let h1 = store_mem (TUInt64) ptr v h in
        let mem2 = I.down_mem (_ih h1) in
        forall j. {:pattern mem1.[j] \/ mem2.[j]}
          j < ptr \/ j >= ptr + 8 ==>
          mem1.[j] == mem2.[j]))
  = let t = TUInt64 in
    let h1 = store_mem t ptr v h in
    let b = Some?.v (find_writeable_buffer t ptr h) in
    length_t_eq t b;
    let i = get_addr_in_ptr t (buffer_length b) (buffer_addr b h) ptr 0 in
    store_buffer_write t ptr v h;
    assert (buffer_addr b h + scale8 i == ptr);
    assert (buffer_addr b h + scale8 (i+1) == ptr + 8);
    store_buffer_down64_mem b i v h

let store_buffer_aux_down64_mem2 (ptr:int) (v:nat64) (h:vale_heap{writeable_mem64 ptr h})
  : Lemma
      (ensures (
        let h1 = store_mem (TUInt64) ptr v h in
        let mem2 = I.down_mem (_ih h1) in
        S.get_heap_val64 ptr mem2 == v))
  = let t = TUInt64 in
    let b = Some?.v (find_writeable_buffer t ptr h) in
    length_t_eq t b;
    let i = get_addr_in_ptr t (buffer_length b) (buffer_addr b h) ptr 0 in
    let h1 = store_mem t ptr v h in
    let mem2 = I.down_mem (_ih h1) in
    store_buffer_write t ptr v h;
    assert (Seq.index (buffer_as_seq h1 b) i == v);
    index64_get_heap_val64 h1 b mem2 i

let in_bounds64 (h:vale_heap) (b:buffer64) (i:nat{i < buffer_length b})
  : Lemma (scale8 i + 8 <= DV.length (get_downview b.bsrc))
  =
  length_t_eq TUInt64 b

let bytes_valid64 ptr h =
  reveal_opaque (`%S.valid_addr64) S.valid_addr64;
  let t = TUInt64 in
  let b = get_addr_ptr t ptr h in
  let i = get_addr_in_ptr t (buffer_length b) (buffer_addr b h) ptr 0 in
  in_bounds64 h b i;
  I.addrs_set_mem (_ih h) b  ptr;
  I.addrs_set_mem (_ih h) b  (ptr+1);
  I.addrs_set_mem (_ih h) b  (ptr+2);
  I.addrs_set_mem (_ih h) b  (ptr+3);
  I.addrs_set_mem (_ih h) b  (ptr+4);
  I.addrs_set_mem (_ih h) b  (ptr+5);
  I.addrs_set_mem (_ih h) b  (ptr+6);
  I.addrs_set_mem (_ih h) b  (ptr+7)

val same_mem_get_heap_val128 (b:buffer128)
                          (i:nat{i < buffer_length b})
                          (v:quad32)
                          (k:nat{k < buffer_length b})
                          (h1:vale_heap{List.memP b (IB.ptrs_of_mem (_ih h1)) /\ buffer_writeable b})
                          (h2:vale_heap{h2 == buffer_write b i v h1})
                          (mem1:S.machine_heap{IB.correct_down_p (_ih h1) mem1 b})
                          (mem2:S.machine_heap{IB.correct_down_p (_ih h2) mem2 b}) : Lemma
  (requires (Seq.index (buffer_as_seq h1 b) k == Seq.index (buffer_as_seq h2 b) k))
  (ensures (let ptr = buffer_addr b h1 + scale16 k in
    forall i.{:pattern mem1.[i]} i >= ptr /\ i < ptr+16 ==> mem1.[i] == mem2.[i]))

val same_mem_eq_slices128 (b:buffer128)
                       (i:nat{i < buffer_length b})
                       (v:quad32)
                       (k:nat{k < buffer_length b})
                       (h1:vale_heap{List.memP b (IB.ptrs_of_mem (_ih h1)) /\ buffer_writeable b})
                       (h2:vale_heap{h2 == buffer_write b i v h1})
                       (mem1:S.machine_heap{IB.correct_down_p (_ih h1) mem1 b})
                       (mem2:S.machine_heap{IB.correct_down_p (_ih h2) mem2 b}) : Lemma
  (requires (Seq.index (buffer_as_seq h1 b) k == Seq.index (buffer_as_seq h2 b) k))
  (ensures (
    k * 16 + 16 <= DV.length (get_downview b.bsrc) /\
    Seq.slice (DV.as_seq (IB.hs_of_mem (_ih h1)) (get_downview b.bsrc)) (k * 16) (k * 16 + 16) ==
    Seq.slice (DV.as_seq (IB.hs_of_mem (_ih h2)) (get_downview b.bsrc)) (k * 16) (k * 16 + 16)))

let same_mem_eq_slices128 b i v k h1 h2 mem1 mem2 =
    let t = TUInt128 in
    let db = get_downview b.bsrc in
    let ub = UV.mk_buffer db (uint_view t) in
    UV.as_seq_sel (IB.hs_of_mem (_ih h1)) ub k;
    UV.as_seq_sel (IB.hs_of_mem (_ih h2)) ub k;
    UV.put_sel (IB.hs_of_mem (_ih h1)) ub k;
    UV.put_sel (IB.hs_of_mem (_ih h2)) ub k;
    UV.length_eq ub

let length_up128 (b:buffer128) (h:vale_heap) (k:nat{k < buffer_length b}) (i:nat{i < 16}) : Lemma
  (scale16 k + i <= DV.length (get_downview b.bsrc)) =
  let vb = UV.mk_buffer (get_downview b.bsrc) uint128_view in
  UV.length_eq vb

let same_mem_get_heap_val128 b j v k h1 h2 mem1 mem2 =
  let ptr = buffer_addr b h1 + scale16 k in
  let addr = buffer_addr b h1 in
  let aux (i:nat{ptr <= i /\ i < ptr+16}) : Lemma (mem1.[i] == mem2.[i]) =
    let db = get_downview b.bsrc in
    let ub = UV.mk_buffer db uint128_view in
    UV.as_seq_sel (IB.hs_of_mem (_ih h1)) ub k;
    UV.as_seq_sel (IB.hs_of_mem (_ih h2)) ub k;
    same_mem_eq_slices128 b j v k h1 h2 mem1 mem2;
    let s1 = (Seq.slice (DV.as_seq (IB.hs_of_mem (_ih h1)) db) (k * 16) (k * 16 + 16)) in
    let s2 = (Seq.slice (DV.as_seq (IB.hs_of_mem (_ih h2)) db) (k * 16) (k * 16 + 16)) in
    assert (Seq.index s1 (i - ptr) == Seq.index (DV.as_seq (IB.hs_of_mem (_ih h1)) db) (k * 16 + (i-ptr)));
    length_up128 b h1 k (i-ptr);
    assert (mem1.[i] == UInt8.v (Seq.index (DV.as_seq (IB.hs_of_mem (_ih h1)) db) (k * 16 + (i-ptr))));
    assert (Seq.index s2 (i-ptr) == Seq.index (DV.as_seq (IB.hs_of_mem (_ih h2)) db) (k * 16 + (i-ptr)));
    length_up128 b h2 k (i-ptr);
    assert (mem2.[addr+(scale16 k + (i-ptr))] == UInt8.v (Seq.index (DV.as_seq (IB.hs_of_mem (_ih h2)) db) (k * 16 + (i-ptr))));
    assert (forall i. addr + (scale16 k + (i-ptr)) == i)
  in
  Classical.forall_intro aux

let in_bounds128 (h:vale_heap) (b:buffer128) (i:nat{i < buffer_length b}) : Lemma
  (scale16 i + 16 <= DV.length (get_downview b.bsrc))
  =
  length_t_eq TUInt128 b

#push-options "--z3rlimit 20"
#restart-solver
let bytes_valid128 ptr h =
  reveal_opaque (`%S.valid_addr128) S.valid_addr128;
  IB.list_disjoint_or_eq_reveal ();
  let t = TUInt128 in
  let b = get_addr_ptr t ptr h in
  let i = get_addr_in_ptr t (buffer_length b) (buffer_addr b h) ptr 0 in
  in_bounds128 h b i;
  I.addrs_set_mem (_ih h) b ptr;
  I.addrs_set_mem (_ih h) b (ptr+1);
  I.addrs_set_mem (_ih h) b (ptr+2);
  I.addrs_set_mem (_ih h) b (ptr+3);
  I.addrs_set_mem (_ih h) b (ptr+4);
  I.addrs_set_mem (_ih h) b (ptr+5);
  I.addrs_set_mem (_ih h) b (ptr+6);
  I.addrs_set_mem (_ih h) b (ptr+7);
  I.addrs_set_mem (_ih h) b (ptr+8);
  I.addrs_set_mem (_ih h) b (ptr+9);
  I.addrs_set_mem (_ih h) b (ptr+10);
  I.addrs_set_mem (_ih h) b (ptr+11);
  I.addrs_set_mem (_ih h) b (ptr+12);
  I.addrs_set_mem (_ih h) b (ptr+13);
  I.addrs_set_mem (_ih h) b (ptr+14);
  I.addrs_set_mem (_ih h) b (ptr+15)
#pop-options

let equiv_load_mem64 ptr h =
  let t = TUInt64 in
  let b = get_addr_ptr t ptr h in
  let i = get_addr_in_ptr t (buffer_length b) (buffer_addr b h) ptr 0 in
  let addr = buffer_addr b h in
  let contents = DV.as_seq (_ih h).IB.hs (get_downview b.bsrc) in
  let heap = get_heap h in
  index64_get_heap_val64 h b heap i;
  lemma_load_mem64 b i h

//let low_lemma_valid_mem64 b i h =
//  lemma_valid_mem64 b i h;
//  bytes_valid64 (buffer_addr b h + scale8 i) h

//let low_lemma_load_mem64 b i h =
//  lemma_valid_mem64 b i h;
//  lemma_load_mem64 b i h;
//  equiv_load_mem64 (buffer_addr b h + scale8 i) h

//let same_domain_update64 b i v h =
//  low_lemma_valid_mem64 b i h;
//  Vale.Arch.MachineHeap.same_domain_update64 (buffer_addr b h + scale8 i) v (get_heap h)

open Vale.X64.BufferViewStore

let low_lemma_store_mem64_aux
  (b:buffer64)
  (heap:S.machine_heap)
  (i:nat{i < buffer_length b})
  (v:nat64)
  (h:vale_heap{buffer_readable h b /\ buffer_writeable b})
  : Lemma
    (requires IB.correct_down_p (_ih h) heap b)
    (ensures (let heap' = S.update_heap64 (buffer_addr b h + scale8 i) v heap in
     let h' = store_mem64 (buffer_addr b h + scale8 i) v h in
     (_ih h').IB.hs == DV.upd_seq (_ih h).IB.hs (get_downview b.bsrc) (I.get_seq_heap heap' (_ih h).IB.addrs b))) =
   let ptr = buffer_addr b h + scale8 i in
   let heap' = S.update_heap64 ptr v heap in
   let h' = store_mem64 ptr v h in
   lemma_store_mem64 b i v h;
   length_t_eq TUInt64 b;
   bv_upd_update_heap64 b heap i v (_ih h);
   let db = get_downview b.bsrc in
   let bv = UV.mk_buffer db Vale.Interop.Views.up_view64 in
   assert (UV.upd (_ih h).IB.hs bv i (UInt64.uint_to_t v) == (_ih h').IB.hs)

val valid_state_store_mem64_aux: (i:nat) -> (v:nat64) -> (h:vale_heap) -> Lemma
  (requires writeable_mem64 i h)
  (ensures (
    let heap = get_heap h in
    let heap' = S.update_heap64 i v heap in
    let h' = store_mem64 i v h in
    heap' == I.down_mem (_ih h')
  ))

let valid_state_store_mem64_aux i v h =
  let heap = get_heap h in
  let heap' = S.update_heap64 i v heap in
  let h1 = store_mem TUInt64 i v h in
  store_buffer_aux_down64_mem i v h;
  store_buffer_aux_down64_mem2 i v h;
  let mem1 = heap' in
  let mem2 = I.down_mem (_ih h1) in
  let aux () : Lemma (forall j. mem1.[j] == mem2.[j]) =
    Vale.Arch.MachineHeap.same_mem_get_heap_val64 i mem1 mem2;
    Vale.Arch.MachineHeap.correct_update_get64 i v heap;
    Vale.Arch.MachineHeap.frame_update_heap64 i v heap
  in let aux2 () : Lemma (Set.equal (Map.domain mem1) (Map.domain mem2)) =
    bytes_valid64 i h;
    Vale.Arch.MachineHeap.same_domain_update64 i v heap
  in aux(); aux2();
  Map.lemma_equal_intro mem1 mem2

let low_lemma_load_mem64_full b i vfh t hid =
  reveal_opaque (`%valid_layout_buffer_id) valid_layout_buffer_id;
  ()

#push-options "--z3rlimit 20"
#restart-solver
let low_lemma_store_mem64 b i v h =
  lemma_writeable_mem64 b i h;
  lemma_store_mem64 b i v h;
  valid_state_store_mem64_aux (buffer_addr b h + scale8 i) v h;
  let heap = get_heap h in
  let heap' = S.update_heap64 (buffer_addr b h + scale8 i) v heap in
  low_lemma_store_mem64_aux b heap i v h;
  Vale.Arch.MachineHeap.frame_update_heap64 (buffer_addr b h + scale8 i) v heap;
  in_bounds64 h b i;
  I.addrs_set_lemma_all ();
  I.update_buffer_up_mem (_ih h) b heap heap'
#pop-options

#set-options "--z3rlimit 100"
#restart-solver
let lemma_is_full_update
    (vfh:vale_full_heap) (h hk hk':vale_heap) (k:heaplet_id) (mh mh' mhk mhk':machine_heap) (mt mt':memtaint)
    (t:base_typ) (b:buffer t) (ptr:int) (v_size:nat)
    (index:nat) (v:base_typ_as_vale_type t) (tn:taint)
  : Lemma
  (requires
    vfh.vf_layout.vl_inner.vl_heaplets_initialized /\
    mem_inv vfh /\
    buffer_readable hk b /\
    buffer_writeable b /\
    index < Seq.length (buffer_as_seq hk b) /\
    mt == vfh.vf_layout.vl_taint /\
    h == vfh.vf_heap /\
    hk == Map16.sel vfh.vf_heaplets k /\
    mh == h.mh /\
    mhk == hk.mh /\
    ptr == buffer_addr b hk + scale_by v_size index /\
    mt' == S.update_n ptr v_size (heap_taint (coerce vfh)) tn /\
    hk' == buffer_write b index v hk /\
    valid_layout_buffer b vfh.vf_layout hk true /\
    valid_taint_buf b hk mt tn /\
    is_machine_heap_update mh mh' /\ upd_heap h mh' == buffer_write b index v h /\
    is_machine_heap_update mhk mhk' /\ upd_heap hk mhk' == buffer_write b index v hk /\
    (forall j.{:pattern mh.[j] \/ mh'.[j]} j < ptr \/ j >= ptr + v_size ==> mh.[j] == mh'.[j]) /\
    (forall j.{:pattern mhk.[j] \/ mhk'.[j]} j < ptr \/ j >= ptr + v_size ==> mhk.[j] == mhk'.[j]) /\
    0 <= scale_by v_size index /\ scale_by v_size index + v_size <= DV.length (get_downview b.bsrc) /\
    (forall i.{:pattern mh'.[i] \/ mhk'.[i]} i >= ptr /\ i < ptr + v_size ==> mh'.[i] == mhk'.[i]) /\
    True
  )
  (ensures is_full_update vfh hk' k mh' mt')
  =
  reveal_opaque (`%valid_layout_buffer_id) valid_layout_buffer_id;
  let vfh' = coerce (heap_upd (coerce vfh) mh' mt') in
  let dom_upd = Set.intersect (vfh.vf_layout.vl_inner.vl_heaplet_sets k) (Map.domain mhk) in
  let mhk'' = Map.concat mhk (Map.restrict dom_upd mh') in
  assert (Map.equal mhk'' mhk');
  let unchanged (j:heaplet_id) : Lemma
    (requires j =!= k)
    (ensures Map16.sel vfh'.vf_heaplets j == Map16.sel vfh.vf_heaplets j)
    [SMTPat (Map16.sel vfh'.vf_heaplets j)]
    =
    assert (Map.equal (Map16.sel vfh'.vf_heaplets j).mh (Map16.sel vfh.vf_heaplets j).mh);
    I.down_up_identity (Map16.sel vfh.vf_heaplets j).ih;
    ()
  in
  assert (Map16.equal vfh'.vf_heaplets (Map16.upd vfh.vf_heaplets k hk'));
  assert (Map.equal mt' mt);
  Vale.Interop.Heap_s.list_disjoint_or_eq_reveal ();
  ()

let low_lemma_store_mem64_full b i v vfh t hid =
  let (h, mt, hk) = (vfh.vf_heap, vfh.vf_layout.vl_taint, Map16.get vfh.vf_heaplets hid) in
  let ptr = buffer_addr b hk + scale8 i in
  let mh' = S.update_heap64 ptr v (heap_get (coerce vfh)) in
  let mt' = S.update_n ptr 8 (heap_taint (coerce vfh)) t in
  let hk' = buffer_write b i v hk in
  let mhk' = S.update_heap64 ptr v (get_heap hk) in
  reveal_opaque (`%valid_layout_buffer_id) valid_layout_buffer_id;
  low_lemma_store_mem64 b i v h;
  low_lemma_store_mem64 b i v (Map16.get vfh.vf_heaplets hid);
  Vale.Arch.MachineHeap.frame_update_heap64 ptr v h.mh;
  Vale.Arch.MachineHeap.frame_update_heap64 ptr v hk.mh;
  in_bounds64 hk b i;
  Vale.Arch.MachineHeap.same_mem_get_heap_val64 ptr mh' mhk';
  lemma_is_full_update vfh h hk hk' hid h.mh mh' hk.mh mhk' mt mt' TUInt64 b ptr 8 i v t;
  ()

val low_lemma_valid_mem128 (b:buffer128) (i:nat) (h:vale_heap) : Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b
  )
  (ensures
    S.valid_addr128 (buffer_addr b h + scale16 i) (get_heap h)
  )

let low_lemma_valid_mem128 b i h =
  lemma_valid_mem128 b i h;
  bytes_valid128 (buffer_addr b h + scale16 i) h

val equiv_load_mem128_aux: (ptr:int) -> (h:vale_heap) -> Lemma
  (requires valid_mem128 ptr h)
  (ensures load_mem128 ptr h == S.get_heap_val128 ptr (get_heap h))

let equiv_load_mem128_aux ptr h =
  let t = TUInt128 in
  let b = get_addr_ptr t ptr h in
  let i = get_addr_in_ptr t (buffer_length b) (buffer_addr b h) ptr 0 in
  let addr = buffer_addr b h in
  let contents = DV.as_seq (_ih h).IB.hs (get_downview b.bsrc) in
  let heap = get_heap h in
  S.get_heap_val128_reveal ();
  index128_get_heap_val128 h b heap i;
  lemma_load_mem128 b i h

let equiv_load_mem128 ptr h =
  equiv_load_mem128_aux ptr h

val low_lemma_load_mem128 (b:buffer128) (i:nat) (h:vale_heap) : Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b
  )
  (ensures
    S.get_heap_val128 (buffer_addr b h + scale16 i) (get_heap h) == buffer_read b i h
  )

let low_lemma_load_mem128 b i h =
  lemma_valid_mem128 b i h;
  lemma_load_mem128 b i h;
  equiv_load_mem128_aux (buffer_addr b h + scale16 i) h

//let same_domain_update128 b i v h =
//  low_lemma_valid_mem128 b i h;
//  Vale.Arch.MachineHeap.same_domain_update128 (buffer_addr b h + scale16 i) v (get_heap h)

let low_lemma_store_mem128_aux
  (b:buffer128)
  (heap:S.machine_heap)
  (i:nat{i < buffer_length b})
  (v:quad32)
  (h:vale_heap{buffer_readable h b /\ buffer_writeable b})
  : Lemma
    (requires IB.correct_down_p (_ih h) heap b)
    (ensures (let heap' = S.update_heap128 (buffer_addr b h + scale16 i) v heap in
     let h' = store_mem128 (buffer_addr b h + scale16 i) v h in
     (_ih h').IB.hs == DV.upd_seq (_ih h).IB.hs (get_downview b.bsrc) (I.get_seq_heap heap' (_ih h).IB.addrs b))) =
   let ptr = buffer_addr b h + scale16 i in
   let heap' = S.update_heap128 ptr v heap in
   let h' = store_mem128 ptr v h in
   lemma_store_mem128 b i v h;
   length_t_eq TUInt128 b;
   bv_upd_update_heap128 b heap i v (_ih h);
   let db = get_downview b.bsrc in
   let bv = UV.mk_buffer db Vale.Interop.Views.up_view128 in
   assert (UV.upd (_ih h).IB.hs bv i v == (_ih h').IB.hs)

val valid_state_store_mem128_aux (i:int) (v:quad32) (h:vale_heap) : Lemma
  (requires writeable_mem128 i h)
  (ensures (
    let heap = get_heap h in
    let heap' = S.update_heap128 i v heap in
    let h' = store_mem128 i v h in
    heap' == I.down_mem (_ih h')
  ))

#restart-solver
let rec written_buffer_down128_aux1
  (b:buffer128{buffer_writeable b})
  (i:nat{i < buffer_length b})
  (v:quad32)
  (h:vale_heap{List.memP b (_ih h).IB.ptrs})
  (base:nat{base == buffer_addr b h})
  (k:nat) (h1:vale_heap{h1 == buffer_write b i v h})
  (mem1:S.machine_heap{IB.correct_down (_ih h) mem1})
  (mem2:S.machine_heap{IB.correct_down (_ih h1) mem2 /\
               (forall j.{:pattern (mem1.[j]) \/ (mem2.[j])}
                 base <= j /\ j < base + k * 16 ==>
                 mem1.[j] == mem2.[j])})
  : Lemma
      (ensures (forall j. {:pattern (mem1.[j]) \/ (mem1.[j])}
                  j >= base /\ j < base + scale16 i ==>
                  mem1.[j] == mem2.[j]))
      (decreases %[i-k]) =
    if k >= i then ()
    else begin
      let ptr = base + scale16 k in
      same_mem_get_heap_val128 b i v k h h1 mem1 mem2;
      heap_shift mem1 mem2 ptr 16;
      written_buffer_down128_aux1 b i v h base (k+1) h1 mem1 mem2
    end

#restart-solver
let rec written_buffer_down128_aux2
  (b:buffer128{buffer_writeable b})
  (i:nat{i < buffer_length b})
  (v:quad32)
  (h:vale_heap{List.memP b (_ih h).IB.ptrs})
  (base:nat{base == buffer_addr b h})
  (n:nat{n == buffer_length b})
  (k:nat{k > i}) (h1:vale_heap{h1 == buffer_write b i v h})
  (mem1:S.machine_heap{IB.correct_down (_ih h) mem1})
  (mem2:S.machine_heap{IB.correct_down (_ih h1) mem2 /\
               (forall j. {:pattern (mem1.[j]) \/ (mem2.[j])}
                 base + scale16 (i+1) <= j /\ j < base + k * 16 ==>
                 mem1.[j] == mem2.[j])})
  : Lemma
      (ensures (forall j. {:pattern (mem1.[j]) \/ (mem2.[j])}
                     j >= base + scale16 (i+1) /\ j < base + scale16 n ==>
                     mem1.[j] == mem2.[j]))
      (decreases %[n-k]) =
    if k >= n then ()
    else begin
      let ptr = base + scale16 k in
      same_mem_get_heap_val128 b i v k h h1 mem1 mem2;
      heap_shift mem1 mem2 ptr 16;
      written_buffer_down128_aux2 b i v h base n (k+1) h1 mem1 mem2
    end

let written_buffer_down128 (b:buffer128) (i:nat{i < buffer_length b}) (v:quad32) (h:vale_heap)
  : Lemma
      (requires List.memP b (_ih h).IB.ptrs /\ buffer_writeable b)
      (ensures (
          let mem1 = I.down_mem (_ih h) in
          let h1 = buffer_write b i v h in
          let mem2 = I.down_mem (_ih h1) in
          let base = buffer_addr b h in
          let n = buffer_length b in
          forall j. {:pattern (mem1.[j]) \/ (mem2.[j])}
               (base <= j /\ j < base + scale16 i) \/
               (base + scale16 (i+1) <= j /\ j < base + scale16 n) ==>
               mem1.[j] == mem2.[j]))
  = let mem1 = I.down_mem (_ih h) in
    let h1 = buffer_write b i v h in
    let mem2 = I.down_mem (_ih h1) in
    let base = buffer_addr b h in
    let n = buffer_length b in
    written_buffer_down128_aux1 b i v h base 0 h1 mem1 mem2;
    written_buffer_down128_aux2 b i v h base n (i+1) h1 mem1 mem2

let store_buffer_down128_mem
  (b:buffer128{buffer_writeable b})
  (i:nat{i < buffer_length b})
  (v:quad32)
  (h:vale_heap{List.memP b (_ih h).IB.ptrs})
  : Lemma
      (ensures (
        let mem1 = I.down_mem (_ih h) in
        let h1 = buffer_write b i v h in
        let mem2 = I.down_mem (_ih h1) in
        let base = buffer_addr b h in
        forall (j:int). {:pattern mem1.[j] \/ mem2.[j]}
          j < base + scale16 i \/ j >= base + scale16 (i+1) ==>
          mem1.[j] == mem2.[j]))
  = let mem1 = I.down_mem (_ih h) in
    let h1 = buffer_write b i v h in
    let mem2 = I.down_mem (_ih h1) in
    let base = buffer_addr b h in
    let n = buffer_length b in
    let aux (j:int)
      : Lemma
          (j < base + scale16 i \/ j >= base + scale16 (i+1) ==>
           mem1.[j] == mem2.[j])
      =
      I.addrs_set_lemma_all ();
      if j >= base && j < base + DV.length (get_downview b.bsrc) then begin
          written_buffer_down128 b i v h;
          length_t_eq TUInt128 b
        end
        else if not (I.valid_addr (_ih h) j)
        then I.same_unspecified_down (_ih h).IB.hs (_ih h1).IB.hs (_ih h).IB.ptrs
        else unwritten_buffer_down TUInt128 b i v h
    in
    Classical.forall_intro aux

let store_buffer_aux_down128_mem (ptr:int) (v:quad32) (h:vale_heap{writeable_mem128 ptr h})
  : Lemma
      (ensures (
        let mem1 = I.down_mem (_ih h) in
        let h1 = store_mem TUInt128 ptr v h in
        let mem2 = I.down_mem (_ih h1) in
        forall j. {:pattern mem1.[j] \/ mem2.[j]}
          j < ptr \/ j >= ptr + 16 ==>
          mem1.[j] == mem2.[j]))
  = let t = TUInt128 in
    let h1 = store_mem t ptr v h in
    let b = Some?.v (find_writeable_buffer t ptr h) in
    length_t_eq t b;
    let i = get_addr_in_ptr t (buffer_length b) (buffer_addr b h) ptr 0 in
    store_buffer_write t ptr v h;
    assert (buffer_addr b h + scale16 i == ptr);
    assert (buffer_addr b h + scale16 (i+1) == ptr + 16);
    store_buffer_down128_mem b i v h

let store_buffer_aux_down128_mem2 (ptr:int) (v:quad32) (h:vale_heap{writeable_mem128 ptr h})
  : Lemma
      (ensures (
        let h1 = store_mem TUInt128 ptr v h in
        let mem2 = I.down_mem (_ih h1) in
        Mkfour
          (S.get_heap_val32 ptr mem2)
          (S.get_heap_val32 (ptr+4) mem2)
          (S.get_heap_val32 (ptr+8) mem2)
          (S.get_heap_val32 (ptr+12) mem2)
        == v)) =
    let t = TUInt128 in
    let b = Some?.v (find_writeable_buffer t ptr h) in
    length_t_eq t b;
    let i = get_addr_in_ptr t (buffer_length b) (buffer_addr b h) ptr 0 in
    let h1 = store_mem t ptr v h in
    let mem2 = I.down_mem (_ih h1) in
    store_buffer_write t ptr v h;
    assert (Seq.index (buffer_as_seq h1 b) i == v);
    index128_get_heap_val128 h1 b mem2 i

let valid_state_store_mem128_aux i v h =
  let heap = get_heap h in
  let heap' = S.update_heap128 i v heap in
  let h1 = store_mem TUInt128 i v h in
  store_buffer_aux_down128_mem i v h;
  store_buffer_aux_down128_mem2 i v h;
  let mem1 = heap' in
  let mem2 = I.down_mem (_ih h1) in
  let aux () : Lemma (forall j. mem1.[j] == mem2.[j]) =
    Vale.Arch.MachineHeap.correct_update_get128 i v heap;
    Vale.X64.Machine_Semantics_s.get_heap_val128_reveal ();
    Vale.Arch.MachineHeap.same_mem_get_heap_val32 i mem1 mem2;
    Vale.Arch.MachineHeap.same_mem_get_heap_val32 (i+4) mem1 mem2;
    Vale.Arch.MachineHeap.same_mem_get_heap_val32 (i+8) mem1 mem2;
    Vale.Arch.MachineHeap.same_mem_get_heap_val32 (i+12) mem1 mem2;
    Vale.Arch.MachineHeap.frame_update_heap128 i v heap
  in
  let aux2 () : Lemma (Set.equal (Map.domain mem1) (Map.domain mem2)) =
    bytes_valid128 i h;
    Vale.Arch.MachineHeap.same_domain_update128 i v heap
  in aux (); aux2 ();
  Map.lemma_equal_intro mem1 mem2

let low_lemma_load_mem128_full b i vfh t hid =
  reveal_opaque (`%valid_layout_buffer_id) valid_layout_buffer_id;
  ()

let low_lemma_store_mem128 b i v h =
  lemma_valid_mem128 b i h;
  lemma_store_mem128 b i v h;
  valid_state_store_mem128_aux (buffer_addr b h + scale16 i) v h;
  let heap = get_heap h in
  let heap' = S.update_heap128 (buffer_addr b h + scale16 i) v heap in
  let h' = store_mem128 (buffer_addr b h + scale16 i) v h in
  low_lemma_store_mem128_aux b heap i v h;
  Vale.Arch.MachineHeap.frame_update_heap128 (buffer_addr b h + scale16 i) v heap;
  in_bounds128 h b i;
  I.addrs_set_lemma_all ();
  I.update_buffer_up_mem (_ih h) b heap heap'

let low_lemma_store_mem128_full b i v vfh t hid =
  let (h, mt, hk) = (vfh.vf_heap, vfh.vf_layout.vl_taint, Map16.get vfh.vf_heaplets hid) in
  let ptr = buffer_addr b hk + scale16 i in
  let mh' = S.update_heap128 ptr v (heap_get (coerce vfh)) in
  let mt' = S.update_n ptr 16 (heap_taint (coerce vfh)) t in
  let hk' = buffer_write b i v hk in
  let mhk' = S.update_heap128 ptr v (get_heap hk) in
  reveal_opaque (`%valid_layout_buffer_id) valid_layout_buffer_id;
  low_lemma_store_mem128 b i v h;
  low_lemma_store_mem128 b i v (Map16.get vfh.vf_heaplets hid);
  Vale.Arch.MachineHeap.frame_update_heap128 ptr v h.mh;
  Vale.Arch.MachineHeap.frame_update_heap128 ptr v hk.mh;
  in_bounds128 hk b i;
  Vale.Arch.MachineHeap.same_mem_get_heap_val128 ptr mh' mhk';
  lemma_is_full_update vfh h hk hk' hid h.mh mh' hk.mh mhk' mt mt' TUInt128 b ptr 16 i v t;
  ()

#push-options "--smtencoding.l_arith_repr boxwrap"
let low_lemma_valid_mem128_64 b i h =
  reveal_opaque (`%S.valid_addr64) S.valid_addr64;
  reveal_opaque (`%S.valid_addr128) S.valid_addr128;
  low_lemma_valid_mem128 b i h;
  let ptr = buffer_addr b h + scale16 i in
  assert (buffer_addr b h + scale16 i + 8 = ptr + 8)
#pop-options

open Vale.Def.Words.Two_s
open Vale.Def.Words.Four_s

let low_lemma_load_mem128_lo64 b i h =
  low_lemma_load_mem128 b i h;
  lo64_reveal ();
  S.get_heap_val128_reveal ();
  S.get_heap_val64_reveal ();
  S.get_heap_val32_reveal ()

let low_lemma_load_mem128_hi64 b i h =
  low_lemma_load_mem128 b i h;
  hi64_reveal ();
  S.get_heap_val128_reveal ();
  S.get_heap_val64_reveal ();
  S.get_heap_val32_reveal ()

//let same_domain_update128_64 b i v h =
//  low_lemma_valid_mem128_64 b i (_ih h);
//  Vale.Arch.MachineHeap.same_domain_update64 (buffer_addr b h + scale16 i) v (get_heap h);
//  Vale.Arch.MachineHeap.same_domain_update64 (buffer_addr b h + scale16 i + 8) v (get_heap h)

open Vale.Def.Types_s

let frame_get_heap32 (ptr:int) (mem1 mem2:S.machine_heap) : Lemma
  (requires (forall i. i >= ptr /\ i < ptr + 4 ==> mem1.[i] == mem2.[i]))
  (ensures S.get_heap_val32 ptr mem1 == S.get_heap_val32 ptr mem2) =
  S.get_heap_val32_reveal ()

let update_heap128_lo (ptr:int) (v:quad32) (mem:S.machine_heap) : Lemma
  (requires
    S.valid_addr128 ptr mem /\
    v.hi2 == S.get_heap_val32 (ptr+8) mem /\
    v.hi3 == S.get_heap_val32 (ptr+12) mem
  )
  (ensures S.update_heap128 ptr v mem ==
    S.update_heap32 (ptr+4) v.lo1 (S.update_heap32 ptr v.lo0 mem)) =
  reveal_opaque (`%S.valid_addr128) S.valid_addr128;
  S.update_heap128_reveal ();
  let mem0 = S.update_heap32 ptr v.lo0 mem in
  let mem1 = S.update_heap32 (ptr+4) v.lo1 mem0 in
  Vale.Arch.MachineHeap.frame_update_heap32 ptr v.lo0 mem;
  Vale.Arch.MachineHeap.frame_update_heap32 (ptr+4) v.lo1 mem0;
  Vale.Arch.MachineHeap.same_domain_update32 ptr v.lo0 mem;
  Vale.Arch.MachineHeap.same_domain_update32 (ptr+4) v.lo1 mem0;
  frame_get_heap32 (ptr+8) mem mem1;
  frame_get_heap32 (ptr+12) mem mem1;
  Vale.Arch.MachineHeap.update_heap32_get_heap32 (ptr+8) mem1;
  Vale.Arch.MachineHeap.update_heap32_get_heap32 (ptr+12) mem1

let low_lemma_load_mem128_lo_hi_full b i vfh t hid =
  reveal_opaque (`%valid_layout_buffer_id) valid_layout_buffer_id;
  low_lemma_valid_mem128_64 b i vfh.vf_heap;
  ()

let low_lemma_store_mem128_lo64 b i v h =
  let ptr = buffer_addr b h + scale16 i in
  let v128 = buffer_read b i h in
  let v' = insert_nat64 v128 v 0 in
  low_lemma_load_mem128 b i h;
  low_lemma_store_mem128 b i v' h;
  S.get_heap_val128_reveal ();
  update_heap128_lo ptr v' (get_heap h);
  S.update_heap64_reveal ();
  S.update_heap32_reveal ();
  insert_nat64_reveal ()

let low_lemma_store_mem128_lo64_full b i v vfh t hid =
  let (h, mt, hk) = (vfh.vf_heap, vfh.vf_layout.vl_taint, Map16.get vfh.vf_heaplets hid) in
  let v' = insert_nat64 (buffer_read b i hk) v 0 in
  let ptr = buffer_addr b hk + scale16 i in
  let mh' = S.update_heap128 ptr v' (heap_get (coerce vfh)) in
  let mt' = S.update_n ptr 16 (heap_taint (coerce vfh)) t in
  let hk' = buffer_write b i v' hk in
  let mhk' = S.update_heap128 ptr v' (get_heap hk) in
  reveal_opaque (`%valid_layout_buffer_id) valid_layout_buffer_id;
  low_lemma_store_mem128 b i v' h;
  low_lemma_store_mem128 b i v' (Map16.get vfh.vf_heaplets hid);
  Vale.Arch.MachineHeap.frame_update_heap128 ptr v' h.mh;
  Vale.Arch.MachineHeap.frame_update_heap128 ptr v' hk.mh;
  in_bounds128 hk b i;
  Vale.Arch.MachineHeap.same_mem_get_heap_val128 ptr mh' mhk';
  lemma_is_full_update vfh h hk hk' hid h.mh mh' hk.mh mhk' mt mt' TUInt128 b ptr 16 i v' t;
  low_lemma_store_mem128_lo64 b i v h;
  low_lemma_valid_mem128_64 b i h;
  assert (Map.equal mt (S.update_n (buffer_addr b h + scale16 i) 8 mt t));
  ()

#push-options "--z3rlimit 20 --using_facts_from '* -LowStar.Monotonic.Buffer.loc_disjoint_includes_r'"
#restart-solver
let low_lemma_store_mem128_hi64 b i v h =
  reveal_opaque (`%S.valid_addr128) S.valid_addr128;
  let ptr = buffer_addr b h + scale16 i in
  let v128 = buffer_read b i h in
  let v' = insert_nat64 v128 v 1 in
  low_lemma_load_mem128 b i h;
  low_lemma_store_mem128 b i v' h;
  assert (S.valid_addr128 ptr (get_heap h));
  Vale.Arch.MachineHeap.update_heap32_get_heap32 ptr (get_heap h);
  Vale.Arch.MachineHeap.update_heap32_get_heap32 (ptr+4) (get_heap h);
  S.get_heap_val128_reveal ();
  S.update_heap128_reveal ();
  S.update_heap64_reveal ();
  S.update_heap32_reveal ();
  insert_nat64_reveal ()
#pop-options

let low_lemma_store_mem128_hi64_full b i v vfh t hid =
  reveal_opaque (`%valid_layout_buffer_id) valid_layout_buffer_id;
  let (h, mt, hk) = (vfh.vf_heap, vfh.vf_layout.vl_taint, Map16.get vfh.vf_heaplets hid) in
  let v' = insert_nat64 (buffer_read b i h) v 1 in
  let ptr = buffer_addr b hk + scale16 i in
  let mh' = S.update_heap128 ptr v' (heap_get (coerce vfh)) in
  let mt' = S.update_n ptr 16 (heap_taint (coerce vfh)) t in
  let hk' = buffer_write b i v' hk in
  let mhk' = S.update_heap128 ptr v' (get_heap hk) in
  reveal_opaque (`%valid_layout_buffer_id) valid_layout_buffer_id;
  low_lemma_store_mem128 b i v' h;
  low_lemma_store_mem128 b i v' (Map16.get vfh.vf_heaplets hid);
  Vale.Arch.MachineHeap.frame_update_heap128 ptr v' h.mh;
  Vale.Arch.MachineHeap.frame_update_heap128 ptr v' hk.mh;
  in_bounds128 hk b i;
  Vale.Arch.MachineHeap.same_mem_get_heap_val128 ptr mh' mhk';
  lemma_is_full_update vfh h hk hk' hid h.mh mh' hk.mh mhk' mt mt' TUInt128 b ptr 16 i v' t;
  low_lemma_store_mem128_hi64 b i v h;
  low_lemma_valid_mem128_64 b i h;
  assert (Map.equal mt (S.update_n (buffer_addr b h + 16 * i + 8) 8 mt t));
  ()

