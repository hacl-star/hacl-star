module X64.Vale.StateEqSemantics

open X64.Vale.StateLemmas
module TS = X64.Taint_Semantics_s

val eval_ins_eq_all (c:TS.tainted_ins) : Lemma
  (ensures (forall (s1 s2:TS.traceState).{:pattern (TS.taint_eval_ins c s1); (TS.taint_eval_ins c s2)}
    state_eq_S s1 s2 ==>
    state_eq_S (TS.taint_eval_ins c s1) (TS.taint_eval_ins c s2)
  ))
