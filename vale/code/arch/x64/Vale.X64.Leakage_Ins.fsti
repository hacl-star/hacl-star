module Vale.X64.Leakage_Ins

open FStar.Mul
open Vale.X64.Machine_s
open Vale.X64.Leakage_s
open Vale.X64.Leakage_Helpers

val check_if_ins_consumes_fixed_time (ins:Vale.X64.Machine_Semantics_s.ins) (ts:analysis_taints)
  : (res:(bool & analysis_taints){ins_consumes_fixed_time ins ts res})

val lemma_ins_leakage_free (ts:analysis_taints) (ins:Vale.X64.Machine_Semantics_s.ins) : Lemma
  (let (b, ts') = check_if_ins_consumes_fixed_time ins ts in
    (b2t b ==> isConstantTime (Ins ins) ts.lts /\ isLeakageFree (Ins ins) ts.lts ts'.lts))
