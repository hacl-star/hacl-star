module Vale.X64.Bytes_Semantics

open FStar.Mul
open Vale.Def.Words_s
open Vale.Def.Types_s
open Vale.Arch.MachineHeap_s
open Vale.Arch.Heap
open Vale.X64.Machine_s
open Vale.X64.Machine_Semantics_s

//val eval_ins_domains (ins:ins) (s0:machine_state) : Lemma
//  ( let s1 = machine_eval_ins ins s0 in
//    Set.equal (Map.domain (heap_get s0.ms_heap)) (Map.domain (heap_get s1.ms_heap)))
//
//val eval_ins_same_unspecified (ins:ins) (s0:machine_state) : Lemma
//  ( let Some s1 = machine_eval_code (Ins ins) 0 s0 in
//    forall x. not (Map.contains (heap_get s1.ms_heap) x) ==> (heap_get s1.ms_heap).[x] == (heap_get s0.ms_heap).[x])
