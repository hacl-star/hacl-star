module X64.Bytes_Semantics

module TS = X64.Taint_Semantics_s
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

val frame_update_heap32 (ptr:int) (v:nat32) (mem:heap) : Lemma
  (let mem' = update_heap32 ptr v mem in
  forall i. i < ptr \/ i >= ptr + 4 ==> mem.[i] == mem'.[i])

val same_domain_update32 (ptr:int) (v:nat32) (mem:heap) : Lemma
  (requires
    Map.contains mem ptr /\
    Map.contains mem (ptr+1) /\
    Map.contains mem (ptr+2) /\
    Map.contains mem (ptr+3))    
  (ensures Map.domain mem == Map.domain (update_heap32 ptr v mem))

val update_heap32_get_heap32 (ptr:int) (mem:heap) : Lemma
  (requires 
    Map.contains mem ptr /\
    Map.contains mem (ptr+1) /\
    Map.contains mem (ptr+2) /\
    Map.contains mem (ptr+3))    
  (ensures (update_heap32 ptr (get_heap_val32 ptr mem) mem == mem))

val frame_update_heap128 (ptr:int) (v:quad32) (mem:heap) : Lemma
  (let mem' = update_heap128 ptr v mem in
  forall j. j < ptr \/ j >= ptr + 16 ==> mem.[j] == mem'.[j])

val correct_update_get128 (ptr:int) (v:quad32) (mem:heap) : Lemma (
  get_heap_val128 ptr (update_heap128 ptr v mem) == v)
  [SMTPat (get_heap_val128 ptr (update_heap128 ptr v mem))]

val same_domain_update128 (ptr:int) (v:quad32) (mem:heap) : Lemma
  (requires valid_addr128 ptr mem)
  (ensures Map.domain mem == Map.domain (update_heap128 ptr v mem))

val same_mem_get_heap_val128 (ptr:int) (mem1 mem2:heap) : Lemma
  (requires get_heap_val128 ptr mem1 == get_heap_val128 ptr mem2)
  (ensures forall i. i >= ptr /\ i < ptr + 16 ==> mem1.[i] == mem2.[i])

val eval_ins_domains (ins:TS.tainted_ins) (s0:TS.traceState) : Lemma
  (let s1 = TS.taint_eval_ins ins s0 in
  Set.equal (Map.domain s0.TS.state.mem) (Map.domain s1.TS.state.mem))

val eval_ins_same_unspecified (ins:TS.tainted_ins) (s0:TS.traceState) : Lemma
  (let Some s1 = TS.taint_eval_code (Ins ins) 0 s0 in
   forall x. not (Map.contains s1.TS.state.mem x) ==> s1.TS.state.mem.[x] == s0.TS.state.mem.[x])
