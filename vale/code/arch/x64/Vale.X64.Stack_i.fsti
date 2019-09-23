module Vale.X64.Stack_i

open FStar.Mul
open Vale.X64.Machine_s
open Vale.X64.Memory
open Vale.Def.Prop_s

val vale_stack : Type u#0

val valid_src_stack64 (ptr:int) (h:vale_stack) : GTot bool
val load_stack64 (ptr:int) (h:vale_stack) : GTot nat64
val store_stack64 (ptr:int) (v:nat64) (h:vale_stack) : GTot vale_stack
val free_stack64 (start:int) (finish:int) (h:vale_stack) : GTot vale_stack

val valid_src_stack128 (ptr:int) (h:vale_stack) : GTot bool
val load_stack128 (ptr:int) (h:vale_stack) : GTot quad32
val store_stack128 (ptr:int) (v:quad32) (h:vale_stack) : GTot vale_stack

val init_rsp (h:vale_stack) : (n:nat64{n >= 4096})

let modifies_stack (lo_rsp hi_rsp:nat) (h h':vale_stack) : Vale.Def.Prop_s.prop0 =
  forall addr . {:pattern (load_stack64 addr h') \/ (valid_src_stack64 addr h') }
    valid_src_stack64 addr h /\ (addr + 8 <= lo_rsp || addr >= hi_rsp) ==>
      valid_src_stack64 addr h' /\
      load_stack64 addr h == load_stack64 addr h'

let valid_src_stack64s (base num_slots:nat) (h:vale_stack) : Vale.Def.Prop_s.prop0 =
  forall addr . {:pattern (valid_src_stack64 addr h)}
    (base <= addr) && (addr < base + num_slots * 8) && (addr - base) % 8 = 0 ==>
      valid_src_stack64 addr h

(* Validity preservation *)

val lemma_store_stack_same_valid64 (ptr:int) (v:nat64) (h:vale_stack) (i:int) : Lemma
  (requires valid_src_stack64 i h /\
    (i >= ptr + 8 \/ i + 8 <= ptr))
  (ensures valid_src_stack64 i (store_stack64 ptr v h))
  [SMTPat (valid_src_stack64 i (store_stack64 ptr v h))]

val lemma_free_stack_same_valid64 (start:int) (finish:int) (ptr:int) (h:vale_stack) : Lemma
  (requires valid_src_stack64 ptr h /\
    (ptr >= finish \/ ptr + 8 <= start))
  (ensures valid_src_stack64 ptr (free_stack64 start finish h))
  [SMTPat (valid_src_stack64 ptr (free_stack64 start finish h))]

(* Validity update *)

val lemma_store_new_valid64 (ptr:int) (v:nat64) (h:vale_stack) : Lemma
  (valid_src_stack64 ptr (store_stack64 ptr v h))
  [SMTPat (valid_src_stack64 ptr (store_stack64 ptr v h))]

(* Classic select/update lemmas *)
val lemma_correct_store_load_stack64 (ptr:int) (v:nat64) (h:vale_stack) : Lemma
  (load_stack64 ptr (store_stack64 ptr v h) == v)
  [SMTPat (load_stack64 ptr (store_stack64 ptr v h))]

val lemma_frame_store_load_stack64 (ptr:int) (v:nat64) (h:vale_stack) (i:int) : Lemma
  (requires valid_src_stack64 i h /\
    (i >= ptr + 8 \/ i + 8 <= ptr))
  (ensures (load_stack64 i (store_stack64 ptr v h) == load_stack64 i h))
  [SMTPat (load_stack64 i (store_stack64 ptr v h))]

val lemma_free_stack_same_load64 (start:int) (finish:int) (ptr:int) (h:vale_stack) : Lemma
  (requires valid_src_stack64 ptr h /\
    (ptr >= finish \/ ptr + 8 <= start))
  (ensures load_stack64 ptr h == load_stack64 ptr (free_stack64 start finish h))
  [SMTPat (load_stack64 ptr (free_stack64 start finish h))]

(* Free composition *)
val lemma_compose_free_stack64 (start:int) (inter:int) (finish:int) (h:vale_stack) : Lemma
  (requires start <= inter /\ inter <= finish)
  (ensures free_stack64 inter finish (free_stack64 start inter h) == free_stack64 start finish h)
  [SMTPat (free_stack64 inter finish (free_stack64 start inter h))]

(* Preservation of the initial stack pointer *)
val lemma_same_init_rsp_free_stack64 (start:int) (finish:int) (h:vale_stack) : Lemma
  (init_rsp (free_stack64 start finish h) == init_rsp h)
  [SMTPat (init_rsp (free_stack64 start finish h))]

val lemma_same_init_rsp_store_stack64 (ptr:int) (v:nat64) (h:vale_stack) : Lemma
  (init_rsp (store_stack64 ptr v h) == init_rsp h)
  [SMTPat (init_rsp (store_stack64 ptr v h))]

// Taint for the stack

val valid_taint_stack64 (ptr:int) (t:taint) (stackTaint:memtaint) : GTot prop0
val valid_taint_stack128 (ptr:int) (t:taint) (stackTaint:memtaint) : GTot prop0
val store_taint_stack64 (ptr:int) (t:taint) (stackTaint:memtaint) : GTot memtaint

val lemma_valid_taint_stack64 (ptr:int) (t:taint) (stackTaint:memtaint) : Lemma
  (requires valid_taint_stack64 ptr t stackTaint)
  (ensures forall i.{:pattern Map.sel stackTaint i} i >= ptr /\ i < ptr + 8 ==> Map.sel stackTaint i == t)

val lemma_valid_taint_stack128 (ptr:int) (t:taint) (stackTaint:memtaint) : Lemma
  (requires valid_taint_stack128 ptr t stackTaint)
  (ensures forall i.{:pattern Map.sel stackTaint i} i >= ptr /\ i < ptr + 16 ==> Map.sel stackTaint i == t)

val lemma_valid_taint_stack64_reveal (ptr:int) (t:taint) (stackTaint:memtaint) : Lemma
  (requires forall i.{:pattern Map.sel stackTaint i} i >= ptr /\ i < ptr + 8 ==> Map.sel stackTaint i == t)
  (ensures valid_taint_stack64 ptr t stackTaint)

val lemma_correct_store_load_taint_stack64 (ptr:int) (t:taint) (stackTaint:memtaint) : Lemma
  (valid_taint_stack64 ptr t (store_taint_stack64 ptr t stackTaint))
  [SMTPat (valid_taint_stack64 ptr t (store_taint_stack64 ptr t stackTaint))]

val lemma_frame_store_load_taint_stack64 (ptr:int) (t:taint) (stackTaint:memtaint) (i:int) (t':taint) : Lemma
  (requires i >= ptr + 8 \/ i + 8 <= ptr)
  (ensures valid_taint_stack64 i t' stackTaint == valid_taint_stack64 i t' (store_taint_stack64 ptr t stackTaint))
  [SMTPat (valid_taint_stack64 i t' (store_taint_stack64 ptr t stackTaint))]


let valid_stack_slot64 (ptr:int) (h:vale_stack) (t:taint) (stackTaint:memtaint) =
  valid_src_stack64 ptr h /\ valid_taint_stack64 ptr t stackTaint

let valid_stack_slot64s (base num_slots:nat) (h:vale_stack) (t:taint) (stackTaint:memtaint) : Vale.Def.Prop_s.prop0 =
  forall addr . {:pattern (valid_src_stack64 addr h) \/ (valid_taint_stack64 addr t stackTaint) \/
    (valid_stack_slot64 addr h t stackTaint)}
    (base <= addr) && (addr < base + num_slots * 8) && (addr - base) % 8 = 0 ==>
      valid_src_stack64 addr h /\ valid_taint_stack64 addr t stackTaint

let modifies_stacktaint (lo_rsp hi_rsp:nat) (h h':memtaint) : Vale.Def.Prop_s.prop0 =
  forall addr t. {:pattern (valid_taint_stack64 addr t h') }
    (addr + 8 <= lo_rsp || addr >= hi_rsp) ==>
      valid_taint_stack64 addr t h == valid_taint_stack64 addr t h'
