module X64.Bytes_Semantics

open X64.Bytes_Semantics_s
open X64.Machine_s
open Words_s

val same_mem_get_heap_val (ptr:int) (mem1 mem2:heap) : Lemma
  (requires get_heap_val64 ptr mem1 == get_heap_val64 ptr mem2)
  (ensures forall i. i >= ptr /\ i < ptr + 8 ==> mem1.[i] == mem2.[i])

val frame_update_heap (ptr:int) (v:nat64) (mem:heap) : Lemma (
  let new_mem = update_heap64 ptr v mem in
  forall j. j < ptr \/ j >= ptr + 8 ==>
    mem.[j] == new_mem.[j])

val correct_update_get (ptr:int) (v:nat64) (mem:heap) : Lemma (
  get_heap_val64 ptr (update_heap64 ptr v mem) == v)
  [SMTPat (get_heap_val64 ptr (update_heap64 ptr v mem))]

val same_domain_update (ptr:int) (v:nat64) (mem:heap) : Lemma
  (requires valid_addr64 ptr mem)
  (ensures Map.domain mem == Map.domain (update_heap64 ptr v mem))

val same_mem_get_heap_val32 (ptr:int) (mem1 mem2:heap) : Lemma
  (requires get_heap_val32 ptr mem1 == get_heap_val32 ptr mem2)
  (ensures forall i. i >= ptr /\ i < ptr + 4 ==> mem1.[i] == mem2.[i])

val frame_update_heap128 (ptr:int) (v:quad32) (s:state) : Lemma (
  let s' = update_mem128 ptr v s in
  forall j. j < ptr \/ j >= ptr + 16 ==>
    s.mem.[j] == s'.mem.[j])

val correct_update_get128 (ptr:int) (v:quad32) (s:state) : Lemma (
  eval_mem128 ptr (update_mem128 ptr v s) == v)
  [SMTPat (eval_mem128 ptr (update_mem128 ptr v s))]

val same_domain_update128 (ptr:int) (v:quad32) (mem:heap) : Lemma
  (requires valid_addr128 ptr mem)
  (ensures Map.domain mem == Map.domain (update_heap128 ptr v mem))
