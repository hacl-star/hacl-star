module X64.Leakage_s

open X64.Machine_s
open X64.Memory_s
open X64.Semantics_s
open X64.Taint_Semantics_s
module S = X64.Bytes_Semantics_s

noeq type taintState =
  | TaintState: regTaint: (reg -> taint) -> flagsTaint: taint -> cfFlagsTaint: taint ->
  xmmTaint: (xmm -> taint) -> taintState

let publicFlagValuesAreSame (ts:taintState) (s1:traceState) (s2:traceState) =
  ts.flagsTaint = Public ==> (s1.state.X64.Memory_s.state.S.flags = s2.state.X64.Memory_s.state.S.flags)

let publicCfFlagValuesAreSame (ts:taintState) (s1:traceState) (s2:traceState) =
Public? ts.cfFlagsTaint ==> (cf s1.state.X64.Memory_s.state.S.flags = cf s2.state.X64.Memory_s.state.S.flags)

let publicRegisterValuesAreSame (ts:taintState) (s1:traceState) (s2:traceState) =
  forall r.
      ts.regTaint r = Public
    ==> (s1.state.X64.Memory_s.state.S.regs r = s2.state.X64.Memory_s.state.S.regs r)

let publicMemValuesAreSame (s1:traceState) (s2:traceState) =
  forall x. (Public? (s1.memTaint.[x]) || Public? (s2.memTaint.[x])) ==> (valid_mem64 x s1.state.mem /\ valid_mem64 x s2.state.mem) ==> (eval_mem x s1.state == eval_mem x s2.state)

let publicXmmValuesAreSame (ts:taintState) (s1:traceState) (s2:traceState) =
  forall r.
      ts.xmmTaint r = Public
    ==> (s1.state.X64.Memory_s.state.S.xmms r = s2.state.X64.Memory_s.state.S.xmms r)

let publicValuesAreSame (ts:taintState) (s1:traceState) (s2:traceState) =
   publicRegisterValuesAreSame ts s1 s2
  /\ publicFlagValuesAreSame ts s1 s2
  /\ publicCfFlagValuesAreSame ts s1 s2
  /\ publicMemValuesAreSame s1 s2
  /\ publicXmmValuesAreSame ts s1 s2

let constTimeInvariant (ts:taintState) (s:traceState) (s':traceState) =
    publicValuesAreSame ts s s'
  /\ s.trace = s'.trace


let isConstantTimeGivenStates (code:tainted_code) (fuel:nat) (ts:taintState) (s1:traceState) (s2:traceState) =
  let r1 = taint_eval_code code fuel s1 in
  let r2 = taint_eval_code code fuel s2 in
  ( (Some? r1) /\ (Some? r2)
   /\ s1.state.X64.Memory_s.state.S.ok /\ (Some?.v r1).state.X64.Memory_s.state.S.ok
   /\ s2.state.X64.Memory_s.state.S.ok /\ (Some?.v r2).state.X64.Memory_s.state.S.ok
   /\ constTimeInvariant ts s1 s2
  ) ==> (Some?.v r1).trace = (Some?.v r2).trace

let isConstantTime (code:tainted_code) (ts:taintState) =
  forall s1 s2 fuel.
      isConstantTimeGivenStates code fuel ts s1 s2

let isExplicitLeakageFreeGivenStates (code:tainted_code) (fuel:nat) (ts:taintState) (ts':taintState) (s1:traceState) (s2:traceState) =
  let r1 = taint_eval_code code fuel s1 in
  let r2 = taint_eval_code code fuel s2 in
 ( Some? r1 /\ Some? r2
  /\ s1.state.X64.Memory_s.state.S.ok /\ (Some?.v r1).state.X64.Memory_s.state.S.ok
  /\ s2.state.X64.Memory_s.state.S.ok /\ (Some?.v r2).state.X64.Memory_s.state.S.ok
  /\ constTimeInvariant ts s1 s2
 ) ==> publicValuesAreSame ts' (Some?.v r1) (Some?.v r2)

let isExplicitLeakageFree (code:tainted_code) (ts:taintState) (ts':taintState) =
  forall s1 s2 fuel.
    isExplicitLeakageFreeGivenStates code fuel ts ts' s1 s2

let isLeakageFree (code:tainted_code) (ts:taintState) (ts':taintState) =
    isConstantTime code ts
  /\ isExplicitLeakageFree code ts ts'
