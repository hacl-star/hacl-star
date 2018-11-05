module X64.Leakage_s

open X64.Machine_s
open X64.Taint_Semantics_s
open X64.Bytes_Semantics_s
module F = FStar.FunctionalExtensionality

type reg_taint = F.restricted_t reg (fun _ -> taint)
type xmms_taint = F.restricted_t xmm (fun _ -> taint)

noeq type taintState =
  | TaintState: regTaint: reg_taint -> flagsTaint: taint -> cfFlagsTaint: taint ->
  xmmTaint: xmms_taint -> taintState

let publicFlagValuesAreSame (ts:taintState) (s1:traceState) (s2:traceState) =
  ts.flagsTaint = Public ==> (s1.state.flags = s2.state.flags)

let publicCfFlagValuesAreSame (ts:taintState) (s1:traceState) (s2:traceState) =
Public? ts.cfFlagsTaint ==> (cf s1.state.flags = cf s2.state.flags)

let publicRegisterValuesAreSame (ts:taintState) (s1:traceState) (s2:traceState) =
  forall r.
      ts.regTaint r = Public
    ==> (s1.state.regs r = s2.state.regs r)

let publicMemValuesAreSame (s1:traceState) (s2:traceState) =
  forall x. (Public? (s1.memTaint.[x]) || Public? (s2.memTaint.[x])) ==> 
    (s1.state.mem.[x] == s2.state.mem.[x])

let publicXmmValuesAreSame (ts:taintState) (s1:traceState) (s2:traceState) =
  forall r.
      ts.xmmTaint r = Public
    ==> (s1.state.xmms r = s2.state.xmms r)

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
   /\ s1.state.ok /\ (Some?.v r1).state.ok
   /\ s2.state.ok /\ (Some?.v r2).state.ok
   /\ constTimeInvariant ts s1 s2
  ) ==> (Some?.v r1).trace = (Some?.v r2).trace

let isConstantTime (code:tainted_code) (ts:taintState) =
  forall s1 s2 fuel.
      isConstantTimeGivenStates code fuel ts s1 s2

let is_explicit_leakage_free_lhs (code:tainted_code) (fuel:nat)
                                 (ts:taintState) (ts':taintState) (s1:traceState) (s2:traceState)
  = s1.state.ok /\ s2.state.ok /\ constTimeInvariant ts s1 s2 /\
    (let r1 = taint_eval_code code fuel s1 in
     let r2 = taint_eval_code code fuel s2 in
     Some? r1 /\ Some? r2 /\ (Some?.v r1).state.ok /\ (Some?.v r2).state.ok)

let is_explicit_leakage_free_rhs (code:tainted_code) (fuel:nat)
                                 (ts:taintState) (ts':taintState) (s1:traceState) (s2:traceState)
  = let r1 = taint_eval_code code fuel s1 in
    let r2 = taint_eval_code code fuel s2 in
    Some? r1 /\ Some? r2 /\ publicValuesAreSame ts' (Some?.v r1) (Some?.v r2)

let isExplicitLeakageFreeGivenStates (code:tainted_code) (fuel:nat)
                                     (ts:taintState) (ts':taintState) (s1:traceState) (s2:traceState)
  = is_explicit_leakage_free_lhs code fuel ts ts' s1 s2 ==> is_explicit_leakage_free_rhs code fuel ts ts' s1 s2

let isExplicitLeakageFree (code:tainted_code) (ts:taintState) (ts':taintState) =
  forall s1 s2 fuel.
    isExplicitLeakageFreeGivenStates code fuel ts ts' s1 s2

let isLeakageFree (code:tainted_code) (ts:taintState) (ts':taintState) =
    isConstantTime code ts
  /\ isExplicitLeakageFree code ts ts'
