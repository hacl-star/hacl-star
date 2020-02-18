module Vale.Arch.HeapImpl
open FStar.Mul
open Vale.Arch.HeapTypes_s
module Map16 = Vale.Lib.Map16

(**
Define abstract (or mostly abstract) types for use by Vale.X64.Decls.fsti.

Note: the untrusted memory definitions are split among 3 modules:
- Vale.Arch.HeapImpl
- Vale.Arch.Heap
- Vale.X64.Memory
This splitting is done to avoid circular module dependencies.
*)

let heaplet_id = n:nat{n < 16}

val buffer (t:base_typ) : Type0

type mutability = | Mutable | Immutable

// Buffer information for heaplets
noeq type buffer_info : Type0 = {
  bi_typ:base_typ;
  bi_buffer:buffer bi_typ;
  bi_heaplet:heaplet_id;
  bi_taint:taint;
  bi_mutable:mutability;
}

val vale_heap : Type u#1
val vale_heap_layout_inner : Type u#1

noeq type vale_heap_layout : Type u#1 = {
  vl_inner:vale_heap_layout_inner;
  vl_taint:memTaint_t;
}

let vale_heaplets = Map16.map16 vale_heap

noeq type vale_full_heap = {
  vf_layout:vale_heap_layout;
  vf_heap:vale_heap;
  vf_heaplets:vale_heaplets;
}

unfold let full_heap_taint (vfh:vale_full_heap) : memTaint_t =
  vfh.vf_layout.vl_taint

