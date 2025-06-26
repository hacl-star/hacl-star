module Vale.PPC64LE.Memory
include Vale.Interop.Types
friend Vale.Arch.Heap
open Vale.Def.Opaque_s
open Vale.Arch.HeapImpl
open Vale.Arch.Heap
open Vale.Interop.Base
module IB = Vale.Interop.Base
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module M = LowStar.Modifies
open LowStar.ModifiesPat
module UV = LowStar.BufferView.Up
module DV = LowStar.BufferView.Down
open Vale.Lib.BufferViewHelpers
module S = Vale.Arch.MachineHeap_s

#reset-options "--initial_fuel 2 --max_fuel 2 --initial_ifuel 1 --max_ifuel 1"

let b8 = IB.b8

unfold let (.[]) = Map.sel
unfold let (.[]<-) = Map.upd

let get_heaplet_id h =
  h.heapletId

let tuint8 = UInt8.t
let tuint16 = UInt16.t
let tuint32 = UInt32.t
let tuint64 = UInt64.t

let v_of_typ (t:base_typ) (v:base_typ_as_vale_type t) : base_typ_as_type t =
  match t with
  | TUInt8 -> UInt8.uint_to_t v
  | TUInt16 -> UInt16.uint_to_t v
  | TUInt32 -> UInt32.uint_to_t v
  | TUInt64 -> UInt64.uint_to_t v
  | TUInt128 -> v

let v_to_typ (t:base_typ) (v:base_typ_as_type t) : base_typ_as_vale_type t =
  match t with
  | TUInt8 -> UInt8.v v
  | TUInt16 -> UInt16.v v
  | TUInt32 -> UInt32.v v
  | TUInt64 -> UInt64.v v
  | TUInt128 -> v

let lemma_v_to_of_typ (t:base_typ) (v:base_typ_as_vale_type t) : Lemma
  (ensures v_to_typ t (v_of_typ t v) == v)
  [SMTPat (v_to_typ t (v_of_typ t v))]
  =
  ()

let uint8_view = Vale.Interop.Views.up_view8
let uint16_view = Vale.Interop.Views.up_view16
let uint32_view = Vale.Interop.Views.up_view32
let uint64_view = Vale.Interop.Views.up_view64
let uint128_view = Vale.Interop.Views.up_view128

let uint_view (t:base_typ) : (v:UV.view UInt8.t (IB.base_typ_as_type t){UV.View?.n v == view_n t}) =
  match t with
  | TUInt8 -> uint8_view
  | TUInt16 -> uint16_view
  | TUInt32 -> uint32_view
  | TUInt64 -> uint64_view
  | TUInt128 -> uint128_view

let buffer_as_seq #t h b =
  let s = UV.as_seq (IB.hs_of_mem (_ih h)) (UV.mk_buffer (get_downview b.bsrc) (uint_view t)) in
  Vale.Lib.Seqs_s.seq_map (v_to_typ t) s

let buffer_readable #t h b = List.memP b (IB.ptrs_of_mem (_ih h))
let buffer_writeable #t b = b.writeable
let buffer_length #t b = UV.length (UV.mk_buffer (get_downview b.bsrc) (uint_view t))
let loc = M.loc
let loc_none = M.loc_none
let loc_union = M.loc_union
let loc_buffer #t b = M.loc_buffer b.bsrc
let loc_disjoint = M.loc_disjoint
let loc_includes = M.loc_includes
let modifies s h h' =
  M.modifies s (_ih h).hs (_ih h').hs /\
  h.heapletId == h'.heapletId /\
  (_ih h).ptrs == (_ih h').ptrs /\
  (_ih h).addrs == (_ih h').addrs /\
  HST.equal_domains (_ih h).hs (_ih h').hs

let buffer_addr #t b h = IB.addrs_of_mem (_ih h) b

open FStar.Mul

#set-options "--z3rlimit 20"

let index64_heap_aux (s:Seq.lseq UInt8.t 8) (heap:S.machine_heap) (ptr:int) : Lemma
  (requires forall (j:nat{j < 8}). UInt8.v (Seq.index s j) == heap.[ptr+j])
  (ensures UInt64.v (Vale.Interop.Views.get64 s) == S.get_heap_val64 ptr heap) =
  let open Vale.Def.Words.Seq_s in
  reveal_opaque (`%seq_to_seq_four_LE) (seq_to_seq_four_LE #nat8);
  Vale.Interop.Views.get64_reveal ();
  S.get_heap_val64_reveal ();
  Vale.Def.Types_s.le_bytes_to_nat64_reveal ()

let index_helper (x y:int) (heap:S.machine_heap) : Lemma
  (requires x == y)
  (ensures heap.[x] == heap.[y])
  =
  ()

let index_mul_helper (addr i n j:int) : Lemma
  (addr + (i * n + j) == addr + n * i + j) =
 ()

#set-options "--max_fuel 0 --max_ifuel 0"

let index64_get_heap_val64
    (h:vale_heap)
    (b:buffer64{List.memP b (_ih h).ptrs})
    (heap:S.machine_heap{IB.correct_down (_ih h) heap})
    (i:nat{i < buffer_length b})
  : Lemma (Seq.index (buffer_as_seq h b) i == S.get_heap_val64 (buffer_addr b h + scale8 i) heap)
  =
  let db = get_downview b.bsrc in
  let ub = UV.mk_buffer db uint64_view in
  let ptr = buffer_addr b h + scale8 i in
  let s = DV.as_seq (_ih h).hs db in
  let t = TUInt64 in
  let addr = buffer_addr b h in
  UV.length_eq ub;
  UV.as_seq_sel (_ih h).hs ub i;
  UV.get_sel (_ih h).hs ub i;
  let s' = Seq.slice s (i*8) (i*8 + 8) in
  let aux (j:nat{j < 8}) : Lemma (UInt8.v (Seq.index s' j) == heap.[ptr+j]) =
    assert (UInt8.v (Seq.index s (i*8 + j)) == heap.[addr + (i*8+j)]);
    Seq.lemma_index_slice s (i*8) (i*8+8) j;
    assert (UInt8.v (Seq.index s' j) == heap.[addr+(i*8+j)]);
    index_mul_helper addr i 8 j;
    ()
  in Classical.forall_intro aux;
  index64_heap_aux s' heap ptr

#set-options "--z3rlimit 50"

open Vale.Def.Words_s
open Vale.Def.Types_s
open Vale.Def.Words.Seq_s
open Vale.Def.Words.Four_s
open Vale.Lib.Seqs_s

let index128_get_heap_val128_aux (s:Seq.lseq UInt8.t 16) (ptr:int) (heap:S.machine_heap) : Lemma
  (requires (forall (j:nat) . j < 16 ==> UInt8.v (Seq.index s j) == heap.[ptr+j]))
  (ensures Vale.Interop.Views.get128 s == Mkfour
    (S.get_heap_val32 ptr heap)
    (S.get_heap_val32 (ptr+4) heap)
    (S.get_heap_val32 (ptr+8) heap)
    (S.get_heap_val32 (ptr+12) heap)) =
  reveal_opaque (`%seq_to_seq_four_LE) (seq_to_seq_four_LE #nat8);
  S.get_heap_val32_reveal ();
  Vale.Interop.Views.get128_reveal ();
  Vale.Def.Types_s.le_bytes_to_quad32_reveal ()

let index128_get_heap_val128
    (h:vale_heap)
    (b:buffer128{List.memP b (_ih h).ptrs})
    (heap:S.machine_heap{IB.correct_down (_ih h) heap})
    (i:nat{i < buffer_length b})
  : Lemma
    (ensures (
      let addr = buffer_addr b h in
      Seq.index (buffer_as_seq h b) i ==
        Mkfour
          (S.get_heap_val32 (addr + scale16 i) heap)
          (S.get_heap_val32 (addr + scale16 i+4) heap)
          (S.get_heap_val32 (addr + scale16 i+8) heap)
          (S.get_heap_val32 (addr + scale16 i +12) heap)
    ))
  =
  let db = get_downview b.bsrc in
  let vb = UV.mk_buffer db uint128_view in
  let ptr = buffer_addr b h + scale16 i in
  let s = DV.as_seq (_ih h).hs db in
  let addr = buffer_addr b h in
  UV.length_eq vb;
  UV.as_seq_sel (_ih h).hs vb i;
  UV.get_sel (_ih h).hs vb i;
  let sl = Seq.slice s (i*16) (i*16+16) in
  let aux (j:nat{j < 16}) : Lemma (UInt8.v (Seq.index sl j) == heap.[ptr+j]) =
    assert (UInt8.v (Seq.index s (i*16 + j)) == heap.[addr + (i*16+j)]);
    Seq.lemma_index_slice s (i*16) (i*16+16) j;
    assert (UInt8.v (Seq.index sl j) == heap.[addr+(i*16+j)]);
    index_mul_helper addr i 16 j
  in Classical.forall_intro aux;
  index128_get_heap_val128_aux sl ptr heap

let modifies_goal_directed s h1 h2 = modifies s h1 h2
let lemma_modifies_goal_directed s h1 h2 = ()

let buffer_length_buffer_as_seq #t h b = ()

let same_underlying_seq (#t:base_typ) (h1 h2:vale_heap) (b:buffer t) : Lemma
  (requires Seq.equal (DV.as_seq (_ih h1).hs (get_downview b.bsrc)) (DV.as_seq (_ih h2).hs (get_downview b.bsrc)))
  (ensures Seq.equal (buffer_as_seq h1 b) (buffer_as_seq h2 b))
  =
  let db = get_downview b.bsrc in
  let rec aux (i:nat{i <= buffer_length b}) : Lemma
    (requires (forall (j:nat{j < i}). Seq.index (buffer_as_seq h1 b) j == Seq.index (buffer_as_seq h2 b) j) /\
    (Seq.equal (DV.as_seq (_ih h1).hs db) (DV.as_seq (_ih h2).hs db)))
    (ensures (forall (j:nat{j < buffer_length b}). Seq.index (buffer_as_seq h1 b) j == Seq.index (buffer_as_seq h2 b) j))
    (decreases %[(buffer_length b) - i]) =
    if i = buffer_length b then ()
    else (
      let bv = UV.mk_buffer db (uint_view t) in
      UV.get_sel (_ih h1).hs bv i;
      UV.get_sel (_ih h2).hs bv i;
      UV.as_seq_sel (_ih h1).hs bv i;
      UV.as_seq_sel (_ih h2).hs bv i;
      aux (i+1)
    )
  in aux 0

let modifies_buffer_elim #t1 b p h h' =
  let db = get_downview b.bsrc in
  lemma_dv_equal (down_view b.src) b.bsrc (_ih h).hs (_ih h').hs;
  same_underlying_seq h h' b;
  assert (Seq.equal (buffer_as_seq h b) (buffer_as_seq h' b))

let modifies_buffer_addr #t b p h h' = ()
let modifies_buffer_readable #t b p h h' = ()

let loc_disjoint_none_r s = M.loc_disjoint_none_r s
let loc_disjoint_union_r s s1 s2 = M.loc_disjoint_union_r s s1 s2
let loc_includes_refl s = M.loc_includes_refl s
let loc_includes_trans s1 s2 s3 = M.loc_includes_trans s1 s2 s3
let loc_includes_union_r s s1 s2 = M.loc_includes_union_r s s1 s2
let loc_includes_union_l s1 s2 s = M.loc_includes_union_l s1 s2 s
let loc_includes_union_l_buffer #t s1 s2 b = M.loc_includes_union_l s1 s2 (loc_buffer b)
let loc_includes_none s = M.loc_includes_none s
let modifies_refl s h = M.modifies_refl s (_ih h).hs
let modifies_goal_directed_refl s h = M.modifies_refl s (_ih h).hs
let modifies_loc_includes s1 h h' s2 = M.modifies_loc_includes s1 (_ih h).hs (_ih h').hs s2
let modifies_trans s12 h1 h2 s23 h3 = M.modifies_trans s12 (_ih h1).hs (_ih h2).hs s23 (_ih h3).hs

let modifies_goal_directed_trans s12 h1 h2 s13 h3 =
  modifies_trans s12 h1 h2 s13 h3;
  modifies_loc_includes s13 h1 h3 (loc_union s12 s13);
  ()

let modifies_goal_directed_trans2 s12 h1 h2 s13 h3 = modifies_goal_directed_trans s12 h1 h2 s13 h3

let default_of_typ (t:base_typ) : base_typ_as_vale_type t =
  allow_inversion base_typ;
  match t with
  | TUInt8 -> 0
  | TUInt16 -> 0
  | TUInt32 -> 0
  | TUInt64 -> 0
  | TUInt128 -> Vale.Def.Words_s.Mkfour #nat32 0 0 0 0

let buffer_read #t b i h =
  if i < 0 || i >= buffer_length b then default_of_typ t else
  Seq.index (buffer_as_seq h b) i

let seq_upd
    (#b:_)
    (h:HS.mem)
    (vb:UV.buffer b{UV.live h vb})
    (i:nat{i < UV.length vb})
    (x:b)
  : Lemma
    (Seq.equal
      (Seq.upd (UV.as_seq h vb) i x)
      (UV.as_seq (UV.upd h vb i x) vb))
  =
  let old_s = UV.as_seq h vb in
  let new_s = UV.as_seq (UV.upd h vb i x) vb in
  let upd_s = Seq.upd old_s i x in
  let rec aux (k:nat) : Lemma
    (requires (k <= Seq.length upd_s /\ (forall (j:nat). j < k ==> Seq.index upd_s j == Seq.index new_s j)))
    (ensures (forall (j:nat). j < Seq.length upd_s ==> Seq.index upd_s j == Seq.index new_s j))
    (decreases %[(Seq.length upd_s) - k]) =
    if k = Seq.length upd_s then ()
    else begin
      UV.sel_upd vb i k x h;
      UV.as_seq_sel h vb k;
      UV.as_seq_sel (UV.upd h vb i x) vb k;
      aux (k+1)
    end
  in aux 0

let buffer_write #t b i v h =
  if i < 0 || i >= buffer_length b then h else
  begin
    let view = uint_view t in
    let db = get_downview b.bsrc in
    let bv = UV.mk_buffer db view in
    UV.upd_modifies (_ih h).hs bv i (v_of_typ t v);
    UV.upd_equal_domains (_ih h).hs bv i (v_of_typ t v);
    let hs' = UV.upd (_ih h).hs bv i (v_of_typ t v) in
    let ih' = InteropHeap (_ih h).ptrs (_ih h).addrs hs' in
    let mh' = Vale.Interop.down_mem ih' in
    let h':vale_heap = ValeHeap mh' (Ghost.hide ih') h.heapletId in
    seq_upd (_ih h).hs bv i (v_of_typ t v);
    assert (Seq.equal (buffer_as_seq h' b) (Seq.upd (buffer_as_seq h b) i v));
    h'
  end

unfold let scale_t (t:base_typ) (index:int) : int = scale_by (view_n t) index

// Checks if address addr corresponds to one of the elements of buffer ptr
let addr_in_ptr (#t:base_typ) (addr:int) (ptr:buffer t) (h:vale_heap) : Ghost bool
  (requires True)
  (ensures fun b -> not b <==>
    (forall (i:int).{:pattern (scale_t t i)} 0 <= i /\ i < buffer_length ptr ==>
      addr <> (buffer_addr ptr h) + scale_t t i))
  =
  let n = buffer_length ptr in
  let base = buffer_addr ptr h in
  let rec aux (i:nat) : Tot (b:bool{not b <==> (forall j. i <= j /\ j < n ==>
    addr <> base + scale_t t j)})
    (decreases %[n-i]) =
    if i >= n then false
    else if addr = base + scale_t t i then true
    else aux (i+1)
  in aux 0

let valid_offset (t:base_typ) (n base:nat) (addr:int) (i:nat) =
  exists j.{:pattern (scale_t t j)} i <= j /\ j < n /\ base + scale_t t j == addr

let rec get_addr_in_ptr (t:base_typ) (n base addr:nat) (i:nat) : Ghost nat
  (requires valid_offset t n base addr i)
  (ensures fun j -> base + scale_t t j == addr)
  (decreases %[n - i])
  =
  if base + scale_t t i = addr then i
  else get_addr_in_ptr t n base addr (i + 1)

let valid_buffer (t:base_typ) (addr:int) (b:b8) (h:vale_heap) : GTot bool =
  DV.length (get_downview b.bsrc) % (view_n t) = 0 &&
  addr_in_ptr #t addr b h

let writeable_buffer (t:base_typ) (addr:int) (b:b8) (h:vale_heap) : GTot bool =
  valid_buffer t addr b h && b.writeable

#set-options "--max_fuel 1 --max_ifuel 1"
let sub_list (p1 p2:list 'a) = forall x. {:pattern List.memP x p2} List.memP x p1 ==> List.memP x p2

let rec valid_mem_aux (t:base_typ) addr (ps:list b8) (h:vale_heap) : Ghost bool
  (requires sub_list ps (_ih h).ptrs)
  (ensures fun b ->
    b <==> (exists (x:buffer t). {:pattern (List.memP x ps) \/ (valid_buffer t addr x h)}
      List.memP x ps /\ valid_buffer t addr x h))
  =
  match ps with
  | [] -> false
  | a::q -> valid_buffer t addr a h || valid_mem_aux t addr q h
let valid_mem (t:base_typ) addr (h:vale_heap) = valid_mem_aux t addr (_ih h).ptrs h
let valid_mem64 ptr h = valid_mem (TUInt64) ptr h

let rec find_valid_buffer_aux (t:base_typ) (addr:int) (ps:list b8) (h:vale_heap) : Ghost (option (buffer t))
  (requires sub_list ps (_ih h).ptrs)
  (ensures fun o ->
    match o with
    | None -> not (valid_mem_aux t addr ps h)
    | Some a -> valid_buffer t addr a h /\ List.memP a ps)
  =
  match ps with
  | [] -> None
  | a::q -> if valid_buffer t addr a h then Some a else find_valid_buffer_aux t addr q h

let find_valid_buffer (t:base_typ) (addr:int) (h:vale_heap) = find_valid_buffer_aux t addr (_ih h).ptrs h

let rec find_valid_buffer_aux_ps (t:base_typ) (addr:int) (ps:list b8) (h1:vale_heap) (h2:vale_heap) : Lemma
  (requires (_ih h1).ptrs == (_ih h2).ptrs /\ sub_list ps (_ih h1).ptrs)
  (ensures find_valid_buffer_aux t addr ps h1 == find_valid_buffer_aux t addr ps h2)
  =
  match ps with
  | [] -> ()
  | a::q -> find_valid_buffer_aux_ps t addr q h1 h2

let find_valid_buffer_ps (t:base_typ) (addr:int) (h1:vale_heap) (h2:vale_heap) : Lemma
  (requires (_ih h1).ptrs == (_ih h2).ptrs)
  (ensures find_valid_buffer t addr h1 == find_valid_buffer t addr h2)
  =
  find_valid_buffer_aux_ps t addr (_ih h1).ptrs h1 h2

let find_valid_buffer_valid_offset (t:base_typ) (addr:int) (h:vale_heap) : Lemma
  (ensures (
    match find_valid_buffer t addr h with
    | None -> True
    | Some a ->
      let base = buffer_addr a h in
      valid_offset t (buffer_length a) base addr 0
  ))
  =
  ()

let rec writeable_mem_aux (t:base_typ) addr (ps:list b8) (h:vale_heap) : Ghost bool
  (requires sub_list ps (_ih h).ptrs)
  (ensures fun b -> b <==>
    (exists (x:buffer t). {:pattern (List.memP x ps) \/ (valid_buffer t addr x h) \/ buffer_writeable x}
      List.memP x ps /\ valid_buffer t addr x h /\ buffer_writeable x))
  =
  match ps with
  | [] -> false
  | a::q -> writeable_buffer t addr a h || writeable_mem_aux t addr q h
let writeable_mem (t:base_typ) addr (h:vale_heap) = writeable_mem_aux t addr (_ih h).ptrs h
let writeable_mem64 ptr h = writeable_mem (TUInt64) ptr h

let rec find_writeable_buffer_aux (t:base_typ) (addr:int) (ps:list b8) (h:vale_heap) : Ghost (option (buffer t))
  (requires sub_list ps (_ih h).ptrs)
  (ensures fun o -> (
    match o with
    | None -> not (writeable_mem_aux t addr ps h)
    | Some a -> writeable_buffer t addr a h /\ List.memP a ps
  ))
  =
  match ps with
  | [] -> None
  | a::q -> if writeable_buffer t addr a h then Some a else find_writeable_buffer_aux t addr q h

let find_writeable_buffer (t:base_typ) (addr:int) (h:vale_heap) =
  find_writeable_buffer_aux t addr (_ih h).ptrs h

let load_mem (t:base_typ) (addr:int) (h:vale_heap) : GTot (base_typ_as_vale_type t) =
  match find_valid_buffer t addr h with
  | None -> default_of_typ t
  | Some a ->
    let base = buffer_addr a h in
    buffer_read a (get_addr_in_ptr t (buffer_length a) base addr 0) h

let load_mem64 ptr h =
  if not (valid_mem64 ptr h) then 0
  else load_mem (TUInt64) ptr h

let length_t_eq (t:base_typ) (b:buffer t) :
  Lemma (DV.length (get_downview b.bsrc) == buffer_length b * (view_n t)) =
  let db = get_downview b.bsrc in
  let ub = UV.mk_buffer db (uint_view t) in
  UV.length_eq ub;
  assert (buffer_length b == DV.length db / (view_n t));
  FStar.Math.Lib.lemma_div_def (DV.length db) (view_n t)

let get_addr_ptr (t:base_typ) (ptr:int) (h:vale_heap) : Ghost (buffer t)
  (requires valid_mem t ptr h)
  (ensures fun b -> List.memP b (_ih h).ptrs /\ valid_buffer t ptr b h)
  =
  Some?.v (find_valid_buffer t ptr h)

#reset-options "--max_fuel 0 --max_ifuel 0 --initial_fuel 0 --initial_ifuel 0 --z3rlimit 20"
let load_buffer_read (t:base_typ) (ptr:int) (h:vale_heap) : Lemma
  (requires valid_mem t ptr h)
  (ensures (
    let b = get_addr_ptr t ptr h in
    let i = get_addr_in_ptr t (buffer_length b) (buffer_addr b h) ptr 0 in
    load_mem t ptr h == buffer_read #t b i h
  ))
  =
  ()

let store_mem (t:base_typ) (addr:int) (v:base_typ_as_vale_type t) (h:vale_heap) : Ghost vale_heap
  (requires True)
  (ensures fun h1 -> (_ih h).addrs == (_ih h1).addrs /\ (_ih h).ptrs == (_ih h1).ptrs)
  =
  match find_writeable_buffer t addr h with
  | None -> h
  | Some a ->
    let base = buffer_addr a h in
    buffer_write a (get_addr_in_ptr t (buffer_length a) base addr 0) v h

let store_mem64 i v h =
  if not (valid_mem64 i h) then h
  else store_mem (TUInt64) i v h

let store_buffer_write
    (t:base_typ)
    (ptr:int)
    (v:base_typ_as_vale_type t)
    (h:vale_heap{writeable_mem t ptr h})
  : Lemma
    (ensures (
      let b = Some?.v (find_writeable_buffer t ptr h) in
      let i = get_addr_in_ptr t (buffer_length b) (buffer_addr b h) ptr 0 in
      store_mem t ptr v h == buffer_write b i v h
    ))
  =
  ()

let valid_mem128 ptr h = valid_mem_aux (TUInt128) ptr (_ih h).ptrs h
let writeable_mem128 ptr h = writeable_mem_aux (TUInt128) ptr (_ih h).ptrs h
let load_mem128 ptr h =
  if not (valid_mem128 ptr h) then (default_of_typ (TUInt128))
  else load_mem (TUInt128) ptr h
let store_mem128 ptr v h =
  if not (valid_mem128 ptr h) then h
  else store_mem (TUInt128) ptr v h

let lemma_valid_mem64 b i h = ()
let lemma_writeable_mem64 b i h = ()

let lemma_store_mem (t:base_typ) (b:buffer t) (i:nat) (v:base_typ_as_vale_type t) (h:vale_heap) : Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b /\
    buffer_writeable b
  )
  (ensures
    store_mem t (buffer_addr b h + scale_t t i) v h == buffer_write b i v h
  )
  =
  FStar.Pervasives.reveal_opaque (`%addr_map_pred) addr_map_pred;
  let view = uint_view t in
  let addr = buffer_addr b h + scale_t t i in
  match find_writeable_buffer t addr h with
  | None -> ()
  | Some a ->
    let da = get_downview a.bsrc in
    let db = get_downview b.bsrc in
    UV.length_eq (UV.mk_buffer da view);
    UV.length_eq (UV.mk_buffer db view);
    opaque_assert (`%list_disjoint_or_eq) list_disjoint_or_eq list_disjoint_or_eq_def (IB.disjoint_or_eq_b8 a b);
    assert (a == b)

let lemma_load_mem64 b i h =
  FStar.Pervasives.reveal_opaque (`%addr_map_pred) addr_map_pred;
  let addr = buffer_addr b h + scale8 i in
  let view = uint64_view in
  match find_valid_buffer TUInt64 addr h with
  | None -> ()
  | Some a ->
    let da = get_downview a.bsrc in
    let db = get_downview b.bsrc in
    UV.length_eq (UV.mk_buffer da view);
    UV.length_eq (UV.mk_buffer db view);
    opaque_assert (`%list_disjoint_or_eq) list_disjoint_or_eq list_disjoint_or_eq_def (IB.disjoint_or_eq_b8 a b);
    assert (a == b)

let lemma_store_mem64 b i v h = lemma_store_mem TUInt64 b i v h
let lemma_valid_mem128 b i h = ()
let lemma_writeable_mem128 b i h = ()

let lemma_load_mem128 b i h =
  FStar.Pervasives.reveal_opaque (`%addr_map_pred) addr_map_pred;
  let addr = buffer_addr b h + scale16 i in
  let view = uint128_view in
  match find_valid_buffer TUInt128 addr h with
  | None -> ()
  | Some a ->
    let da = get_downview a.bsrc in
    let db = get_downview b.bsrc in
    UV.length_eq (UV.mk_buffer da view);
    UV.length_eq (UV.mk_buffer db view);
    opaque_assert (`%list_disjoint_or_eq) list_disjoint_or_eq list_disjoint_or_eq_def (IB.disjoint_or_eq_b8 a b);
    assert (a == b)

let lemma_store_mem128 b i v h = lemma_store_mem TUInt128 b i v h

open Vale.X64.Machine_s

let valid_taint_b8 (b:b8) (h:vale_heap) (mt:memtaint) (tn:taint) : GTot prop0 =
  let addr = (_ih h).addrs b in
  (forall (i:int).{:pattern (mt.[i])}
    addr <= i /\ i < addr + DV.length (get_downview b.bsrc) ==> mt.[i] == tn)

let valid_taint_buf #t b h mt tn =
  valid_taint_b8 b h mt tn

let apply_taint_buf (#t:base_typ) (b:buffer t) (mem:vale_heap) (memTaint:memtaint) (tn:taint) (i:nat) : Lemma
  (requires i < DV.length (get_downview b.bsrc) /\ valid_taint_buf b mem memTaint tn)
  (ensures memTaint.[(_ih mem).addrs b + i] == tn)
  =
  ()

let lemma_valid_taint64 b memTaint mem i t =
  length_t_eq (TUInt64) b;
  let ptr = buffer_addr b mem + scale8 i in
  let aux (i':nat) : Lemma
    (requires i' >= ptr /\ i' < ptr + 8)
    (ensures memTaint.[i'] == t) =
    let extra = scale8 i + i' - ptr in
    assert (i' == (_ih mem).addrs b + extra);
    apply_taint_buf b mem memTaint t extra
  in
  Classical.forall_intro (Classical.move_requires aux)

let lemma_valid_taint128 b memTaint mem i t =
  length_t_eq (TUInt128) b;
  let ptr = buffer_addr b mem + scale16 i in
  let aux i' : Lemma
    (requires i' >= ptr /\ i' < ptr + 16)
    (ensures memTaint.[i'] == t) =
    let extra = scale16 i + i' - ptr in
    assert (i' == (_ih mem).addrs b + extra);
    apply_taint_buf b mem memTaint t extra
  in
  Classical.forall_intro (Classical.move_requires aux)

let same_memTaint (t:base_typ) (b:buffer t) (mem0 mem1:vale_heap) (memT0 memT1:memtaint) : Lemma
  (requires modifies (loc_buffer b) mem0 mem1 /\
    (forall p. Map.sel memT0 p == Map.sel memT1 p))
  (ensures memT0 == memT1) =
  assert (Map.equal memT0 memT1)

let same_memTaint64 b mem0 mem1 memtaint0 memtaint1 =
  same_memTaint (TUInt64) b mem0 mem1 memtaint0 memtaint1

let same_memTaint128 b mem0 mem1 memtaint0 memtaint1 =
  same_memTaint (TUInt128) b mem0 mem1 memtaint0 memtaint1

let modifies_valid_taint #t b p h h' mt tn =
  let dv = get_downview b.bsrc in
  let imp_left () : Lemma
    (requires valid_taint_buf b h mt tn)
    (ensures valid_taint_buf b h' mt tn) =
    let aux (i:nat{i < DV.length dv}) : Lemma (mt.[(_ih h').addrs b + i] = tn) =
      apply_taint_buf b h mt tn i
    in Classical.forall_intro aux
  in let imp_right () : Lemma
    (requires valid_taint_buf b h' mt tn)
    (ensures valid_taint_buf b h mt tn) =
    let aux (i:nat{i < DV.length dv}) : Lemma (mt.[(_ih h).addrs b + i] = tn) =
      apply_taint_buf b h' mt tn i
    in Classical.forall_intro aux
  in
  (Classical.move_requires imp_left());
  (Classical.move_requires imp_right())

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"
let modifies_same_heaplet_id l h1 h2 =
  ()

let valid_taint_bufs (mem:vale_heap) (memTaint:memtaint) (ps:list b8) (ts:b8 -> GTot taint) =
  forall b.{:pattern List.memP b ps} List.memP b ps ==> valid_taint_b8 b mem memTaint (ts b)

let rec write_taint_lemma (i:nat) (mem:IB.interop_heap) (ts:b8 -> GTot taint) (b:b8) (accu:memtaint) : Lemma
  (requires
    i <= DV.length (get_downview b.bsrc) /\
    (forall (j:int).{:pattern accu.[j]} mem.addrs b <= j /\ j < mem.addrs b + i ==> accu.[j] = ts b)
  )
  (ensures (
    let m = IB.write_taint i mem ts b accu in
    let addr = mem.addrs b in
    (forall j.{:pattern m.[j]} addr <= j /\ j < addr + DV.length (get_downview b.bsrc) ==>
      m.[j] = ts b) /\
    (forall j. {:pattern m.[j]} j < addr \/ j >= addr + DV.length (get_downview b.bsrc) ==>
      m.[j] == accu.[j])))
  (decreases %[DV.length (get_downview b.bsrc) - i])
  =
  let m = IB.write_taint i mem ts b accu in
  let addr = mem.addrs b in
  if i >= DV.length (get_downview b.bsrc) then ()
  else
    let new_accu = accu.[addr+i] <- ts b in
    assert (IB.write_taint i mem ts b accu == IB.write_taint (i + 1) mem ts b new_accu);
    assert (Set.equal (Map.domain new_accu) (Set.complement Set.empty));
    assert (forall j.{:pattern m.[j]} addr <= j /\ j < addr + i + 1 ==> new_accu.[j] == ts b);
    write_taint_lemma (i + 1) mem ts b new_accu

#restart-solver
let rec valid_memtaint (mem:vale_heap) (ps:list b8) (ts:b8 -> GTot taint) : Lemma
  (requires IB.list_disjoint_or_eq ps)
  (ensures valid_taint_bufs mem (IB.create_memtaint (_ih mem) ps ts) ps ts)
  =
  FStar.Pervasives.reveal_opaque (`%addr_map_pred) addr_map_pred;
  match ps with
    | [] -> ()
    | b :: q ->
      assert (List.memP b ps);
      assert (forall i. {:pattern List.memP i q} List.memP i q ==> List.memP i ps);
      opaque_assert (`%list_disjoint_or_eq) list_disjoint_or_eq list_disjoint_or_eq_def (IB.list_disjoint_or_eq q);
      valid_memtaint mem q ts;
      assert (IB.create_memtaint (_ih mem) ps ts ==
              IB.write_taint 0 (_ih mem) ts b (IB.create_memtaint (_ih mem) q ts));
      write_taint_lemma 0 (_ih mem) ts b (IB.create_memtaint (_ih mem) q ts);
      opaque_assert (`%list_disjoint_or_eq) list_disjoint_or_eq list_disjoint_or_eq_def (forall p. List.memP p q ==> IB.disjoint_or_eq_b8 p b)

let valid_layout_data_buffer (t:base_typ) (b:buffer t) (layout:vale_heap_layout_inner) (hid:heaplet_id) (write:bool) =
  exists (n:nat).{:pattern (Seq.index layout.vl_buffers n)} n < Seq.length layout.vl_buffers /\ (
    let bi = Seq.index layout.vl_buffers n in
    t == bi.bi_typ /\
    b == bi.bi_buffer /\
    (write ==> bi.bi_mutable == Mutable) /\
    hid == bi.bi_heaplet)

[@"opaque_to_smt"]
let valid_layout_buffer_id t b layout h_id write =
  match h_id with
  | None -> True
  | Some hid ->
    layout.vl_inner.vl_heaplets_initialized /\
    valid_layout_data_buffer t b layout.vl_inner hid write

let inv_heaplet_ids (hs:vale_heaplets) =
  forall (i:heaplet_id).{:pattern Map16.sel hs i} (Map16.sel hs i).heapletId == Some i

let inv_heaplet (owns:Set.set int) (h hi:vale_heap) =
  h.ih.IB.ptrs == hi.ih.IB.ptrs /\
  Map.domain h.mh == Map.domain hi.mh /\
  (forall (i:int).{:pattern Set.mem i owns \/ Set.mem i (Map.domain h.mh) \/ Map.sel h.mh i \/ Map.sel hi.mh i}
    Set.mem i owns ==>
      Set.mem i (Map.domain h.mh) /\
      Map.sel h.mh i == Map.sel hi.mh i /\
      True
  ) /\
  True

// heaplet state matches heap state
let inv_buffer_info (bi:buffer_info) (owners:heaplet_id -> Set.set int) (h:vale_heap) (hs:vale_heaplets) (mt:memTaint_t) (modloc:loc) =
  let t = bi.bi_typ in
  let hid = bi.bi_heaplet in
  let hi = Map16.get hs hid in
  let b = bi.bi_buffer in
  let owns = owners hid in
  (bi.bi_mutable == Mutable ==> loc_includes modloc (loc_buffer b)) /\
  buffer_readable h b /\
  buffer_as_seq hi b == buffer_as_seq h b /\
  (valid_taint_buf b hi mt bi.bi_taint <==> valid_taint_buf b h mt bi.bi_taint) /\
  (forall (i:int).{:pattern Set.mem i owns}
    buffer_addr b h <= i /\ i < buffer_addr b h + DV.length (get_downview b.bsrc) ==> Set.mem i owns) /\
  True

let inv_heaplets (layout:vale_heap_layout_inner) (h:vale_heap) (hs:vale_heaplets) (mt:memTaint_t) =
  let bs = layout.vl_buffers in
  modifies layout.vl_mod_loc layout.vl_old_heap h /\  // modifies for entire heap
  (forall (i:heaplet_id) (a:int).{:pattern Set.mem a (layout.vl_heaplet_sets i)}
    layout.vl_heaplet_map a == Some i <==> Set.mem a (layout.vl_heaplet_sets i)
  ) /\
  (forall (i:heaplet_id).{:pattern (Map16.sel hs i)}
    inv_heaplet (layout.vl_heaplet_sets i) h (Map16.sel hs i)) /\
  (forall (i:nat).{:pattern (Seq.index bs i)} i < Seq.length bs ==>
    inv_buffer_info (Seq.index bs i) layout.vl_heaplet_sets h hs mt layout.vl_mod_loc) /\
  (forall (i1 i2:nat).{:pattern (Seq.index bs i1); (Seq.index bs i2)}
    i1 < Seq.length bs /\ i2 < Seq.length bs ==> buffer_info_disjoint (Seq.index bs i1) (Seq.index bs i2)) /\
  True

let is_initial_heap layout h =
  h == layout.vl_inner.vl_old_heap /\
  not layout.vl_inner.vl_heaplets_initialized

let mem_inv h =
  h.vf_heap.heapletId == None /\
  inv_heaplet_ids h.vf_heaplets /\
  (if h.vf_layout.vl_inner.vl_heaplets_initialized
    then
      inv_heaplets h.vf_layout.vl_inner h.vf_heap
        h.vf_heaplets h.vf_layout.vl_taint
    else
      h.vf_heaplets == empty_vale_heaplets h.vf_layout.vl_inner.vl_old_heap
  )

let layout_heaplets_initialized layout = layout.vl_heaplets_initialized
let layout_old_heap layout = layout.vl_old_heap
let layout_modifies_loc layout = layout.vl_mod_loc
let layout_buffers layout = layout.vl_buffers

let heaps_match bs mt h1 h2 id =
  forall (i:nat).{:pattern Seq.index bs i} i < Seq.length bs ==> (
    let Mkbuffer_info t b hid tn _ = Seq.index bs i in
    hid == id ==>
    buffer_as_seq h1 b == buffer_as_seq h2 b /\
    buffer_addr b h1 == buffer_addr b h2 /\
    buffer_readable h1 b == buffer_readable h2 b /\
    (t == TUInt64 ==> (valid_taint_buf64 b h1 mt tn <==> valid_taint_buf64 b h2 mt tn)) /\
    (t == TUInt128 ==> (valid_taint_buf128 b h1 mt tn <==> valid_taint_buf128 b h2 mt tn)) /\
    (forall (i:int).{:pattern (buffer_read b i h1) \/ (buffer_read b i h2)}
      buffer_read b i h1 == buffer_read b i h2))

let lemma_heaps_match bs mt h1 h2 id i =
  ()

