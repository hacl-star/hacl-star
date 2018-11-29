module X64.BufferViewStore

open Views
open Interop
module B = LowStar.Buffer
module BV = LowStar.BufferView
module HS = FStar.HyperStack
open BufferViewHelpers
open Types_s
open Words_s
open Words.Two_s
open Words.Two
open Words.Four_s
open Words.Seq_s
open Words.Seq
open Arch.Types

friend LowStar.BufferView

#reset-options "--z3rlimit 10 --max_fuel 0 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 1"

let math_aux (a b c:int) : Lemma (a + b + (c - b) == a + c) = ()

let map_aux (ptr1 ptr2:int) (v:int) (m:heap) : Lemma
  (requires ptr1 == ptr2 /\ m.[ptr1] == v)
  (ensures m.[ptr2] == v) = ()

let get64_aux (ptr:int) (heap:heap) (v:nat64) (k:nat{k < 8}) : Lemma
  (requires get_heap_val64 ptr heap == v)
  (ensures heap.[ptr + k] == UInt8.v (Seq.index (put64 (UInt64.uint_to_t v)) k)) =
  Opaque_s.reveal_opaque get_heap_val64_def;
  Opaque_s.reveal_opaque put64_def;
  Opaque_s.reveal_opaque le_nat64_to_bytes_def;
  four_to_nat_8_injective ();
  two_to_nat_32_injective ()

let get128_aux (ptr:int) (heap:heap) (v:quad32) (k:nat{k < 16}) : Lemma
  (requires get_heap_val128 ptr heap == v)
  (ensures heap.[ptr + k] == UInt8.v (Seq.index (put128 v) k)) =
  Opaque_s.reveal_opaque get_heap_val128_def;
  Opaque_s.reveal_opaque get_heap_val32_def;
  Opaque_s.reveal_opaque put128_def;
  Opaque_s.reveal_opaque le_quad32_to_bytes_def;
  four_to_nat_8_injective ()

#set-options "--z3refresh --max_fuel 1 --initial_fuel 1 --z3rlimit 200"

let bv_upd_update_heap64 b heap i v addrs ptrs h =
  admit();
  let bv = BV.mk_buffer_view b view64 in
  BV.as_buffer_mk_buffer_view b view64;
  BV.get_view_mk_buffer_view b view64;
  BV.length_eq bv;
  let h' = BV.upd h bv i (UInt64.uint_to_t v) in
  let ptr = addrs b + 8 `op_Multiply` i in
  let heap' = update_heap64 ptr v heap in
  let prefix, _, suffix = BV.split_at_i bv i h in
  let s1 = prefix `Seq.append` (BV.View?.put view64 (UInt64.uint_to_t v) `Seq.append` suffix) in
  let aux1 (j:nat{j < Seq.length s1}) : Lemma 
    (requires  j < 8 `op_Multiply` i \/ j >= 8 `op_Multiply` i + 8)
    (ensures heap'.[addrs b + j] == UInt8.v (Seq.index s1 j)) =
    X64.Bytes_Semantics.frame_update_heap (addrs b + 8 `op_Multiply` i) v heap;
    assert (Seq.index s1 j == Seq.index (B.as_seq h b) j);
    ()
  in 
  let aux2 (j:nat{j < Seq.length s1}) : Lemma
    (requires  j >= 8 `op_Multiply` i /\ j < 8 `op_Multiply` i + 8)
    (ensures heap'.[addrs b + j] == UInt8.v (Seq.index s1 j)) =
    Seq.lemma_index_app2 prefix (BV.View?.put view64 (UInt64.uint_to_t v) `Seq.append` suffix) j;
    Seq.lemma_index_app1 (BV.View?.put view64 (UInt64.uint_to_t v)) suffix (j - 8 `op_Multiply` i);
    get64_aux ptr heap' v (j - 8 `op_Multiply` i);
    math_aux (addrs b) (8 `op_Multiply` i) j;
    map_aux
      (addrs b + (8 `op_Multiply` i) + (j - 8 `op_Multiply` i)) 
      (addrs b + j) (UInt8.v (Seq.index s1 j)) heap'
  in
  Classical.forall_intro (Classical.move_requires aux1);
  Classical.forall_intro (Classical.move_requires aux2);
  assert (Seq.equal s1 (get_seq_heap heap' addrs b));
  ()
  
#set-options "--z3refresh --z3rlimit 200"

let bv_upd_update_heap128 b heap i v addrs ptrs h =
  admit();
  let bv = BV.mk_buffer_view b view128 in
  BV.as_buffer_mk_buffer_view b view128;
  BV.get_view_mk_buffer_view b view128;
  BV.length_eq bv;
  let h' = BV.upd h bv i v in
  let ptr = addrs b + 16 `op_Multiply` i in
  let heap' = update_heap128 ptr v heap in
  let prefix, _, suffix = BV.split_at_i bv i h in
  let s1 = prefix `Seq.append` (BV.View?.put view128 v `Seq.append` suffix) in
  let aux1 (j:nat{j < Seq.length s1}) : Lemma 
    (requires  j < 16 `op_Multiply` i \/ j >= 16 `op_Multiply` i + 16)
    (ensures heap'.[addrs b + j] == UInt8.v (Seq.index s1 j)) =
    X64.Bytes_Semantics.frame_update_heap128 (addrs b + 16 `op_Multiply` i) v heap;
    assert (Seq.index s1 j == Seq.index (B.as_seq h b) j);
    ()
  in 
  let aux2 (j:nat{j < Seq.length s1}) : Lemma
    (requires  j >= 16 `op_Multiply` i /\ j < 16 `op_Multiply` i + 16)
    (ensures heap'.[addrs b + j] == UInt8.v (Seq.index s1 j)) =
    Seq.lemma_index_app2 prefix (BV.View?.put view128 v `Seq.append` suffix) j;
    Seq.lemma_index_app1 (BV.View?.put view128 v) suffix (j - 16 `op_Multiply` i);
    get128_aux ptr heap' v (j - 16 `op_Multiply` i);
    math_aux (addrs b) (16 `op_Multiply` i) j;
    map_aux 
      (addrs b + (16 `op_Multiply` i) + (j - 16 `op_Multiply` i)) 
      (addrs b + j) (UInt8.v (Seq.index s1 j)) heap'
  in
  Classical.forall_intro (Classical.move_requires aux1);
  Classical.forall_intro (Classical.move_requires aux2);
  assert (Seq.equal s1 (get_seq_heap heap' addrs b));
  ()  
