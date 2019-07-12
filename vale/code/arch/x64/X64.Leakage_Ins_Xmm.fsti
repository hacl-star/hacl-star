module X64.Leakage_Ins_Xmm

open X64.Machine_s
open X64.Taint_Semantics_s
open X64.Leakage_s
open X64.Leakage_Helpers

val check_if_xmm_ins_consumes_fixed_time: (ins:tainted_ins{is_xmm_ins ins}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})
