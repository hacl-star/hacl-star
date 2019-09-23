module Vale.X64.Memory_Sems

open FStar.Mul
open Vale.Def.Prop_s
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

let lemma_upd_get_heap h = I.down_up_identity (_ih h)

let lemma_get_upd_heap h m = I.up_down_identity (_ih h) m

let lemma_heap_get_heap h = ()

let lemma_heap_upd_heap h m = ()

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
  (8 * k + i <= DV.length (get_downview b.bsrc)) =
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
  (ensures (let ptr = buffer_addr b h1 + 8 * k in
    forall i. {:pattern (mem1.[ptr+i])} i >= 0 /\ i < 8 ==> mem1.[ptr+i] == mem2.[ptr+i]))

let same_mem_get_heap_val64 b j v k h1 h2 mem1 mem2 =
  let ptr = buffer_addr b h1 + 8 * k in
  let addr = buffer_addr b h1 in
  let aux (i:nat{i < 8}) : Lemma (mem1.[addr+(8 * k + i)] == mem2.[addr+(8 * k +i)]) =
    let db = get_downview b.bsrc in
    let ub = UV.mk_buffer db uint64_view in
    UV.as_seq_sel (IB.hs_of_mem (_ih h1)) ub k;
    UV.as_seq_sel (IB.hs_of_mem (_ih h2)) ub k;
    same_mem_eq_slices64 b j v k h1 h2 mem1 mem2;
    let s1 = (Seq.slice (DV.as_seq (IB.hs_of_mem (_ih h1)) db) (k * 8) (k * 8 + 8)) in
    let s2 = (Seq.slice (DV.as_seq (IB.hs_of_mem (_ih h2)) db) (k * 8) (k * 8 + 8)) in
    assert (Seq.index s1 i == Seq.index (DV.as_seq (IB.hs_of_mem (_ih h1)) db) (k * 8 + i));
    length_up64 b h1 k i;
    assert (mem1.[addr+(8 * k + i)] == UInt8.v (Seq.index (DV.as_seq (IB.hs_of_mem (_ih h1)) db) (k * 8 + i)));
    assert (Seq.index s2 i == Seq.index (DV.as_seq (IB.hs_of_mem (_ih h2)) db) (k * 8 + i));
    length_up64 b h2 k i;
    assert (mem2.[addr+(8 * k + i)] == UInt8.v (Seq.index (DV.as_seq (IB.hs_of_mem (_ih h2)) db) (k * 8 + i)))
  in
  Classical.forall_intro aux;
  assert (forall i. addr + (8 * k + i) == ptr + i)

#push-options "--z3cliopt smt.arith.nl=true --smtencoding.l_arith_repr boxwrap"
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
                  j >= base /\ j < base + 8 * i ==>
                  mem1.[j] == mem2.[j]))
      (decreases %[i-k]) =
    if k >= i then ()
    else begin
      let ptr = base + 8 * k in
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
                 base + 8 * (i+1) <= j /\ j < base + k * 8 ==>
                 mem1.[j] == mem2.[j])})
  : Lemma
      (ensures (forall j. {:pattern (mem1.[j]) \/ (mem2.[j])}
                     j >= base + 8 * (i+1) /\ j < base + 8 * n ==>
                     mem1.[j] == mem2.[j]))
      (decreases %[n-k]) =
    if k >= n then ()
    else begin
      let ptr = base + 8 * k in
      same_mem_get_heap_val64 b i v k h h1 mem1 mem2;
      heap_shift mem1 mem2 ptr 8;
      written_buffer_down64_aux2 b i v h base n (k+1) h1 mem1 mem2
    end
#pop-options

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
               (base <= j /\ j < base + 8 * i) \/
               (base + 8 * (i+1) <= j /\ j < base + 8 * n) ==>
               mem1.[j] == mem2.[j]))
  = let mem1 = I.down_mem (_ih h) in
    let h1 = buffer_write b i v h in
    let mem2 = I.down_mem (_ih h1) in
    let base = buffer_addr b h in
    let n = buffer_length b in
    written_buffer_down64_aux1 b i v h base 0 h1 mem1 mem2;
    written_buffer_down64_aux2 b i v h base n (i+1) h1 mem1 mem2

#push-options "--z3cliopt smt.arith.nl=true"
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
          assert (MB.disjoint a.bsrc b.bsrc);
          lemma_dv_equal (IB.down_view a.src) a.bsrc (IB.hs_of_mem (_ih h)) (IB.hs_of_mem (_ih h1));
          assert (Seq.equal s0 s1);
          assert (forall (i:nat). {:pattern (mem1.[base + i])}
                    i < Seq.length s0 ==> v_to_typ TUInt8 (Seq.index s0 i) == mem1.[base + i]);
          heap_shift mem1 mem2 base (DV.length db)
    in
    Classical.forall_intro aux
#pop-options

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
          j < base + 8 * i \/ j >= base + 8 * (i+1) ==>
          mem1.[j] == mem2.[j]))
  = let mem1 = I.down_mem (_ih h) in
    let h1 = buffer_write b i v h in
    let mem2 = I.down_mem (_ih h1) in
    let base = buffer_addr b h in
    let n = buffer_length b in
    let aux (j:int)
      : Lemma
          (j < base + 8 * i \/ j >= base + 8 * (i+1) ==>
           mem1.[j] == mem2.[j])
      = if j >= base && j < base + DV.length (get_downview b.bsrc) then begin
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
    assert (buffer_addr b h + 8 * i == ptr);
    assert (buffer_addr b h + 8 * (i+1) == ptr + 8);
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
  : Lemma
      (ensures (forall j. (IB.addrs_of_mem (_ih h)) b + 8 * i <= j  /\
                     j < (IB.addrs_of_mem (_ih h)) b + 8 * i + 8 ==>
                     j < (IB.addrs_of_mem (_ih h)) b + DV.length (get_downview b.bsrc)))
  = length_t_eq (TUInt64) b

let bytes_valid64 ptr h =
  FStar.Pervasives.reveal_opaque (`%S.valid_addr64) S.valid_addr64;
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
  (ensures (let ptr = buffer_addr b h1 + 16 * k in
    forall i. {:pattern (mem1.[ptr+i])} i >= 0 /\ i < 16 ==> mem1.[ptr+i] == mem2.[ptr+i]))

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
  (16 * k + i <= DV.length (get_downview b.bsrc)) =
  let vb = UV.mk_buffer (get_downview b.bsrc) uint128_view in
  UV.length_eq vb

let same_mem_get_heap_val128 b j v k h1 h2 mem1 mem2 =
  let ptr = buffer_addr b h1 + 16 * k in
  let addr = buffer_addr b h1 in
  let aux (i:nat{i < 16}) : Lemma (mem1.[addr+(16 * k + i)] == mem2.[addr+(16 * k +i)]) =
    let db = get_downview b.bsrc in
    let ub = UV.mk_buffer db uint128_view in
    UV.as_seq_sel (IB.hs_of_mem (_ih h1)) ub k;
    UV.as_seq_sel (IB.hs_of_mem (_ih h2)) ub k;
    same_mem_eq_slices128 b j v k h1 h2 mem1 mem2;
    let s1 = (Seq.slice (DV.as_seq (IB.hs_of_mem (_ih h1)) db) (k * 16) (k * 16 + 16)) in
    let s2 = (Seq.slice (DV.as_seq (IB.hs_of_mem (_ih h2)) db) (k * 16) (k * 16 + 16)) in
    assert (Seq.index s1 i == Seq.index (DV.as_seq (IB.hs_of_mem (_ih h1)) db) (k * 16 + i));
    length_up128 b h1 k i;
    assert (mem1.[addr+(16 * k + i)] == UInt8.v (Seq.index (DV.as_seq (IB.hs_of_mem (_ih h1)) db) (k * 16 + i)));
    assert (Seq.index s2 i == Seq.index (DV.as_seq (IB.hs_of_mem (_ih h2)) db) (k * 16 + i));
    length_up128 b h2 k i;
    assert (mem2.[addr+(16 * k + i)] == UInt8.v (Seq.index (DV.as_seq (IB.hs_of_mem (_ih h2)) db) (k * 16 + i)))
  in
  Classical.forall_intro aux;
  assert (forall i. addr + (16 * k + i) == ptr + i)

let in_bounds128 (h:vale_heap) (b:buffer128) (i:nat{i < buffer_length b}) : Lemma
  (forall j. j >= (_ih h).IB.addrs b + 16 * i /\
          j < (_ih h).IB.addrs b + 16 * i + 16 ==>
          j < (_ih h).IB.addrs b + DV.length (get_downview b.bsrc)) =
  length_t_eq TUInt128 b

let bytes_valid128 ptr h =
  FStar.Pervasives.reveal_opaque (`%S.valid_addr128) S.valid_addr128;
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
//  bytes_valid64 (buffer_addr b h + 8 * i) h

//let low_lemma_load_mem64 b i h =
//  lemma_valid_mem64 b i h;
//  lemma_load_mem64 b i h;
//  equiv_load_mem64 (buffer_addr b h + 8 * i) h

//let same_domain_update64 b i v h =
//  low_lemma_valid_mem64 b i h;
//  Vale.Arch.MachineHeap.same_domain_update (buffer_addr b h + 8 * i) v (get_heap h)

open Vale.X64.BufferViewStore

let low_lemma_store_mem64_aux
  (b:buffer64)
  (heap:S.machine_heap)
  (i:nat{i < buffer_length b})
  (v:nat64)
  (h:vale_heap{buffer_readable h b /\ buffer_writeable b})
  : Lemma
    (requires IB.correct_down_p (_ih h) heap b)
    (ensures (let heap' = S.update_heap64 (buffer_addr b h + 8 * i) v heap in
     let h' = store_mem64 (buffer_addr b h + 8 * i) v h in
     (_ih h').IB.hs == DV.upd_seq (_ih h).IB.hs (get_downview b.bsrc) (I.get_seq_heap heap' (_ih h).IB.addrs b))) =
   let ptr = buffer_addr b h + 8 * i in
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
    Vale.Arch.MachineHeap.same_mem_get_heap_val i mem1 mem2;
    Vale.Arch.MachineHeap.correct_update_get i v heap;
    Vale.Arch.MachineHeap.frame_update_heap i v heap
  in let aux2 () : Lemma (Set.equal (Map.domain mem1) (Map.domain mem2)) =
    bytes_valid64 i h;
    Vale.Arch.MachineHeap.same_domain_update i v heap
  in aux(); aux2();
  Map.lemma_equal_intro mem1 mem2

#push-options "--z3rlimit 20"
#restart-solver
let low_lemma_store_mem64 b i v h =
  lemma_writeable_mem64 b i h;
  lemma_store_mem64 b i v h;
  valid_state_store_mem64_aux (buffer_addr b h + 8 * i) v h;
  let heap = get_heap h in
  let heap' = S.update_heap64 (buffer_addr b h + 8 * i) v heap in
  low_lemma_store_mem64_aux b heap i v h;
  Vale.Arch.MachineHeap.frame_update_heap (buffer_addr b h + 8 * i) v heap;
  in_bounds64 h b i;
  I.update_buffer_up_mem (_ih h) b heap heap'
#pop-options

val low_lemma_valid_mem128 (b:buffer128) (i:nat) (h:vale_heap) : Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b
  )
  (ensures
    S.valid_addr128 (buffer_addr b h + 16 * i) (get_heap h)
  )

let low_lemma_valid_mem128 b i h =
  lemma_valid_mem128 b i h;
  bytes_valid128 (buffer_addr b h + 16 * i) h

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
  Vale.Def.Opaque_s.reveal_opaque S.get_heap_val128_def;
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
    S.get_heap_val128 (buffer_addr b h + 16 * i) (get_heap h) == buffer_read b i h
  )

let low_lemma_load_mem128 b i h =
  lemma_valid_mem128 b i h;
  lemma_load_mem128 b i h;
  equiv_load_mem128_aux (buffer_addr b h + 16 * i) h

//let same_domain_update128 b i v h =
//  low_lemma_valid_mem128 b i h;
//  Vale.Arch.MachineHeap.same_domain_update128 (buffer_addr b h + 16 * i) v (get_heap h)

let low_lemma_store_mem128_aux
  (b:buffer128)
  (heap:S.machine_heap)
  (i:nat{i < buffer_length b})
  (v:quad32)
  (h:vale_heap{buffer_readable h b /\ buffer_writeable b})
  : Lemma
    (requires IB.correct_down_p (_ih h) heap b)
    (ensures (let heap' = S.update_heap128 (buffer_addr b h + 16 * i) v heap in
     let h' = store_mem128 (buffer_addr b h + 16 * i) v h in
     (_ih h').IB.hs == DV.upd_seq (_ih h).IB.hs (get_downview b.bsrc) (I.get_seq_heap heap' (_ih h).IB.addrs b))) =
   let ptr = buffer_addr b h + 16 * i in
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

#push-options "--z3cliopt smt.arith.nl=true --smtencoding.nl_arith_repr boxwrap"
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
                  j >= base /\ j < base + 16 * i ==>
                  mem1.[j] == mem2.[j]))
      (decreases %[i-k]) =
    if k >= i then ()
    else begin
      let ptr = base + 16 * k in
      same_mem_get_heap_val128 b i v k h h1 mem1 mem2;
      heap_shift mem1 mem2 ptr 16;
      written_buffer_down128_aux1 b i v h base (k+1) h1 mem1 mem2
    end
#pop-options

#push-options "--z3cliopt smt.arith.nl=true --smtencoding.l_arith_repr boxwrap"
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
                 base + 16 * (i+1) <= j /\ j < base + k * 16 ==>
                 mem1.[j] == mem2.[j])})
  : Lemma
      (ensures (forall j. {:pattern (mem1.[j]) \/ (mem2.[j])}
                     j >= base + 16 * (i+1) /\ j < base + 16 * n ==>
                     mem1.[j] == mem2.[j]))
      (decreases %[n-k]) =
    if k >= n then ()
    else begin
      let ptr = base + 16 * k in
      same_mem_get_heap_val128 b i v k h h1 mem1 mem2;
      heap_shift mem1 mem2 ptr 16;
      written_buffer_down128_aux2 b i v h base n (k+1) h1 mem1 mem2
    end
#pop-options

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
               (base <= j /\ j < base + 16 * i) \/
               (base + 16 * (i+1) <= j /\ j < base + 16 * n) ==>
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
          j < base + 16 * i \/ j >= base + 16 * (i+1) ==>
          mem1.[j] == mem2.[j]))
  = let mem1 = I.down_mem (_ih h) in
    let h1 = buffer_write b i v h in
    let mem2 = I.down_mem (_ih h1) in
    let base = buffer_addr b h in
    let n = buffer_length b in
    let aux (j:int)
      : Lemma
          (j < base + 16 * i \/ j >= base + 16 * (i+1) ==>
           mem1.[j] == mem2.[j])
      = if j >= base && j < base + DV.length (get_downview b.bsrc) then begin
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
    assert (buffer_addr b h + 16 * i == ptr);
    assert (buffer_addr b h + 16 * (i+1) == ptr + 16);
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
    Vale.Def.Opaque_s.reveal_opaque Vale.X64.Machine_Semantics_s.get_heap_val128_def;
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

let low_lemma_store_mem128 b i v h =
  lemma_valid_mem128 b i h;
  lemma_store_mem128 b i v h;
  valid_state_store_mem128_aux (buffer_addr b h + 16 * i) v h;
  let heap = get_heap h in
  let heap' = S.update_heap128 (buffer_addr b h + 16 * i) v heap in
  let h' = store_mem128 (buffer_addr b h + 16 * i) v h in
  low_lemma_store_mem128_aux b heap i v h;
  Vale.Arch.MachineHeap.frame_update_heap128 (buffer_addr b h + 16 * i) v heap;
  in_bounds128 h b i;
  I.update_buffer_up_mem (_ih h) b heap heap'

#push-options "--smtencoding.l_arith_repr boxwrap"
let low_lemma_valid_mem128_64 b i h =
  FStar.Pervasives.reveal_opaque (`%S.valid_addr64) S.valid_addr64;
  FStar.Pervasives.reveal_opaque (`%S.valid_addr128) S.valid_addr128;
  low_lemma_valid_mem128 b i h;
  let ptr = buffer_addr b h + 16 * i in
  assert (buffer_addr b h + 16 * i + 8 = ptr + 8)
#pop-options

open Vale.Def.Words.Two_s
open Vale.Def.Words.Four_s

let low_lemma_load_mem128_lo64 b i h =
  low_lemma_load_mem128 b i h;
  Vale.Def.Opaque_s.reveal_opaque lo64_def;
  Vale.Def.Opaque_s.reveal_opaque S.get_heap_val128_def;
  Vale.Def.Opaque_s.reveal_opaque S.get_heap_val64_def;
  Vale.Def.Opaque_s.reveal_opaque S.get_heap_val32_def

let low_lemma_load_mem128_hi64 b i h =
  low_lemma_load_mem128 b i h;
  Vale.Def.Opaque_s.reveal_opaque hi64_def;
  Vale.Def.Opaque_s.reveal_opaque S.get_heap_val128_def;
  Vale.Def.Opaque_s.reveal_opaque S.get_heap_val64_def;
  Vale.Def.Opaque_s.reveal_opaque S.get_heap_val32_def

//let same_domain_update128_64 b i v h =
//  low_lemma_valid_mem128_64 b i (_ih h);
//  Vale.Arch.MachineHeap.same_domain_update (buffer_addr b h + 16 * i) v (get_heap h);
//  Vale.Arch.MachineHeap.same_domain_update (buffer_addr b h + 16 * i + 8) v (get_heap h)

open Vale.Def.Types_s

let frame_get_heap32 (ptr:int) (mem1 mem2:S.machine_heap) : Lemma
  (requires (forall i. i >= ptr /\ i < ptr + 4 ==> mem1.[i] == mem2.[i]))
  (ensures S.get_heap_val32 ptr mem1 == S.get_heap_val32 ptr mem2) =
  Vale.Def.Opaque_s.reveal_opaque S.get_heap_val32_def

let update_heap128_lo (ptr:int) (v:quad32) (mem:S.machine_heap) : Lemma
  (requires
    S.valid_addr128 ptr mem /\
    v.hi2 == S.get_heap_val32 (ptr+8) mem /\
    v.hi3 == S.get_heap_val32 (ptr+12) mem
  )
  (ensures S.update_heap128 ptr v mem ==
    S.update_heap32 (ptr+4) v.lo1 (S.update_heap32 ptr v.lo0 mem)) =
  FStar.Pervasives.reveal_opaque (`%S.valid_addr128) S.valid_addr128;
  Vale.Def.Opaque_s.reveal_opaque S.update_heap128_def;
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

let low_lemma_store_mem128_lo64 b i v h =
  let ptr = buffer_addr b h + 16 * i in
  let v128 = buffer_read b i h in
  let v' = insert_nat64_opaque v128 v 0 in
  low_lemma_load_mem128 b i h;
  low_lemma_store_mem128 b i v' h;
  Vale.Def.Opaque_s.reveal_opaque S.get_heap_val128_def;
  update_heap128_lo ptr v' (get_heap h);
  Vale.Def.Opaque_s.reveal_opaque S.update_heap64_def;
  Vale.Def.Opaque_s.reveal_opaque S.update_heap32_def;
  Vale.Def.Opaque_s.reveal_opaque insert_nat64

let low_lemma_store_mem128_hi64 b i v h =
  FStar.Pervasives.reveal_opaque (`%S.valid_addr128) S.valid_addr128;
  let ptr = buffer_addr b h + 16 * i in
  let v128 = buffer_read b i h in
  let v' = insert_nat64_opaque v128 v 1 in
  low_lemma_load_mem128 b i h;
  low_lemma_store_mem128 b i v' h;
  assert (S.valid_addr128 ptr (get_heap h));
  Vale.Arch.MachineHeap.update_heap32_get_heap32 ptr (get_heap h);
  Vale.Arch.MachineHeap.update_heap32_get_heap32 (ptr+4) (get_heap h);
  Vale.Def.Opaque_s.reveal_opaque S.get_heap_val128_def;
  Vale.Def.Opaque_s.reveal_opaque S.update_heap128_def;
  Vale.Def.Opaque_s.reveal_opaque S.update_heap64_def;
  Vale.Def.Opaque_s.reveal_opaque S.update_heap32_def;
  Vale.Def.Opaque_s.reveal_opaque insert_nat64
