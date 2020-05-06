module Vale.Arch.MachineHeap

open FStar.Mul
open Vale.Def.Words_s
open Vale.Def.Types_s
open Vale.Arch.MachineHeap_s

val same_mem_get_heap_val64 (ptr:int) (mem1 mem2:machine_heap) : Lemma
  (requires get_heap_val64 ptr mem1 == get_heap_val64 ptr mem2)
  (ensures forall i.{:pattern mem1.[i] \/ mem2.[i]} i >= ptr /\ i < ptr + 8 ==> mem1.[i] == mem2.[i])

val frame_update_heap64 (ptr:int) (v:nat64) (mem:machine_heap) : Lemma (
  let new_mem = update_heap64 ptr v mem in
  forall j.{:pattern mem.[j] \/ new_mem.[j]} j < ptr \/ j >= ptr + 8 ==>
    mem.[j] == new_mem.[j])

val correct_update_get64 (ptr:int) (v:nat64) (mem:machine_heap) : Lemma (
  get_heap_val64 ptr (update_heap64 ptr v mem) == v)
  [SMTPat (get_heap_val64 ptr (update_heap64 ptr v mem))]

val same_domain_update64 (ptr:int) (v:nat64) (mem:machine_heap) : Lemma
  (requires valid_addr64 ptr mem)
  (ensures Map.domain mem == Map.domain (update_heap64 ptr v mem))

val same_mem_get_heap_val32 (ptr:int) (mem1 mem2:machine_heap) : Lemma
  (requires get_heap_val32 ptr mem1 == get_heap_val32 ptr mem2)
  (ensures forall i.{:pattern mem1.[i] \/ mem2.[i]} i >= ptr /\ i < ptr + 4 ==> mem1.[i] == mem2.[i])

val frame_update_heap32 (ptr:int) (v:nat32) (mem:machine_heap) : Lemma
  (let mem' = update_heap32 ptr v mem in
    forall i.{:pattern mem.[i] \/ mem'.[i]} i < ptr \/ i >= ptr + 4 ==> mem.[i] == mem'.[i])

val same_domain_update32 (ptr:int) (v:nat32) (mem:machine_heap) : Lemma
  (requires
    Map.contains mem ptr /\
    Map.contains mem (ptr + 1) /\
    Map.contains mem (ptr + 2) /\
    Map.contains mem (ptr + 3))
  (ensures Map.domain mem == Map.domain (update_heap32 ptr v mem))

val update_heap32_get_heap32 (ptr:int) (mem:machine_heap) : Lemma
  (requires
    Map.contains mem ptr /\
    Map.contains mem (ptr + 1) /\
    Map.contains mem (ptr + 2) /\
    Map.contains mem (ptr + 3))
  (ensures (update_heap32 ptr (get_heap_val32 ptr mem) mem == mem))

val frame_update_heap128 (ptr:int) (v:quad32) (mem:machine_heap) : Lemma
  (let mem' = update_heap128 ptr v mem in
    forall j.{:pattern mem.[j] \/ mem'.[j]} j < ptr \/ j >= ptr + 16 ==> mem.[j] == mem'.[j])

val correct_update_get128 (ptr:int) (v:quad32) (mem:machine_heap) : Lemma (
  get_heap_val128 ptr (update_heap128 ptr v mem) == v)
  [SMTPat (get_heap_val128 ptr (update_heap128 ptr v mem))]

val same_domain_update128 (ptr:int) (v:quad32) (mem:machine_heap) : Lemma
  (requires valid_addr128 ptr mem)
  (ensures Map.domain mem == Map.domain (update_heap128 ptr v mem))

val same_mem_get_heap_val128 (ptr:int) (mem1 mem2:machine_heap) : Lemma
  (requires get_heap_val128 ptr mem1 == get_heap_val128 ptr mem2)
  (ensures forall i.{:pattern mem1.[i] \/ mem2.[i]} i >= ptr /\ i < ptr + 16 ==> mem1.[i] == mem2.[i])

