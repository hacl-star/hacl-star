module X64.Leakage
open X64.Machine_s
module S = X64.Bytes_Semantics_s
open X64.Taint_Semantics_s
open X64.Leakage_s
open X64.Leakage_Helpers
open X64.Leakage_Ins
open X64.Leakage_Ins_Xmm

#reset-options "--initial_ifuel 0 --max_ifuel 1 --initial_fuel 1 --max_fuel 1"
let combine_reg_taints (regs1 regs2:reg_taint) : reg_taint =
    FunctionalExtensionality.on reg (fun x -> merge_taint (regs1 x) (regs2 x))

let combine_reg_taints_monotone (regs1 regs2:reg_taint) : Lemma
  (forall r. Public? ((combine_reg_taints regs1 regs2) r) ==> Public? (regs1 r) /\ Public? (regs2 r))
= ()


let combine_xmm_taints (xmms1 xmms2:xmms_taint) : xmms_taint =
    FunctionalExtensionality.on xmm (fun x -> merge_taint (xmms1 x) (xmms2 x))

let combine_xmm_taints_monotone (xmms1 xmms2:xmms_taint) : Lemma
  (forall r. Public? ((combine_xmm_taints xmms1 xmms2) r) ==> Public? (xmms1 r) /\ Public? (xmms2 r))
= ()

let eq_registers (regs1 regs2:reg_taint) : (b:bool{b <==> regs1 == regs2}) =
  let b = regs1 Rax = regs2 Rax &&
  regs1 Rbx = regs2 Rbx &&
  regs1 Rcx = regs2 Rcx &&
  regs1 Rdx = regs2 Rdx &&
  regs1 Rsi = regs2 Rsi &&
  regs1 Rdi = regs2 Rdi &&
  regs1 Rbp = regs2 Rbp &&
  regs1 Rsp = regs2 Rsp &&
  regs1 R8 = regs2 R8 &&
  regs1 R9 = regs2 R9 &&
  regs1 R10 = regs2 R10 &&
  regs1 R11 = regs2 R11 &&
  regs1 R12 = regs2 R12 &&
  regs1 R13 = regs2 R13 &&
  regs1 R14 = regs2 R14 &&
  regs1 R15 = regs2 R15 in
  assert (FStar.FunctionalExtensionality.feq regs1 regs2 <==> b);
  b

let eq_xmms (xmms1 xmms2:xmms_taint) : (b:bool{b <==> (xmms1 == xmms2)})  =
  let b = xmms1 0 = xmms2 0 &&
    xmms1 1 = xmms2 1 &&
    xmms1 2 = xmms2 2 &&
    xmms1 3 = xmms2 3 &&
    xmms1 4 = xmms2 4 &&
    xmms1 5 = xmms2 5 &&
    xmms1 6 = xmms2 6 &&
    xmms1 7 = xmms2 7 &&
    xmms1 8 = xmms2 8 &&
    xmms1 9 = xmms2 9 &&
    xmms1 10 = xmms2 10 &&
    xmms1 11 = xmms2 11 &&
    xmms1 12 = xmms2 12 &&
    xmms1 13 = xmms2 13 &&
    xmms1 14 = xmms2 14 &&
    xmms1 15 = xmms2 15
  in
  assert (FStar.FunctionalExtensionality.feq xmms1 xmms2 <==> b);
  b

let eq_taintStates (ts1 ts2:taintState) : (b:bool{b <==> ts1 == ts2}) =
    eq_registers ts1.regTaint ts2.regTaint && ts1.flagsTaint = ts2.flagsTaint && ts1.cfFlagsTaint = ts2.cfFlagsTaint && eq_xmms ts1.xmmTaint ts2.xmmTaint

let taintstate_monotone (ts ts':taintState) = ( forall r. Public? (ts'.regTaint r) ==> Public? (ts.regTaint r)) /\ (Public? (ts'.flagsTaint) ==> Public? (ts.flagsTaint)) /\
  (Public? (ts'.cfFlagsTaint) ==> Public? (ts.cfFlagsTaint)) /\
  (forall x. Public? (ts'.xmmTaint x) ==> Public? (ts.xmmTaint x))

let taintstate_monotone_trans (ts1:taintState) (ts2:taintState) (ts3:taintState)
  :Lemma (taintstate_monotone ts1 ts2 /\ taintstate_monotone ts2 ts3 ==> taintstate_monotone ts1 ts3) = ()

let isConstant_monotone (ts1:taintState) (ts2:taintState) (code:tainted_code) (fuel:nat) (s1:traceState) (s2:traceState) 
  :Lemma (isConstantTimeGivenStates code fuel ts2 s1 s2 /\ taintstate_monotone ts1 ts2 ==> isConstantTimeGivenStates code fuel ts1 s1 s2)
  = ()

let isExplicit_monotone (ts:taintState) (ts1:taintState) (ts2:taintState) (code:tainted_code) 
  (fuel:nat) (s1:traceState) (s2:traceState) 
  :Lemma (isExplicitLeakageFreeGivenStates code fuel ts ts1 s1 s2 /\ taintstate_monotone ts1 ts2 ==> isExplicitLeakageFreeGivenStates code fuel ts ts2 s1 s2)
  = ()

let isExplicit_monotone2 (ts:taintState) (ts1:taintState) (ts2:taintState)
  (code:tainted_code) (fuel:nat) (s1:traceState) (s2:traceState) 
  :Lemma (isExplicitLeakageFreeGivenStates code fuel ts2 ts s1 s2 /\ taintstate_monotone ts1 ts2 ==> isExplicitLeakageFreeGivenStates code fuel ts1 ts s1 s2)
  = ()

let combine_taint_states (ts1:taintState) (ts2:taintState) : (ts:taintState{taintstate_monotone ts1 ts /\ taintstate_monotone ts2 ts}) =
  TaintState (combine_reg_taints ts1.regTaint ts2.regTaint)
    (merge_taint ts1.flagsTaint ts2.flagsTaint)
    (merge_taint ts1.cfFlagsTaint ts2.cfFlagsTaint)
    (combine_xmm_taints ts1.xmmTaint ts2.xmmTaint)

let count_public_register (regs:reg_taint) (r:reg) = if Public? (regs r) then 1 else 0

let count_public_registers (regs:reg_taint) : nat =
  count_public_register regs Rax +
  count_public_register regs Rbx +
  count_public_register regs Rcx +
  count_public_register regs Rdx +
  count_public_register regs Rsi +
  count_public_register regs Rdi +
  count_public_register regs Rbp +
  count_public_register regs Rsp +
  count_public_register regs R8 +
  count_public_register regs R9 +
  count_public_register regs R10 +
  count_public_register regs R11 +
  count_public_register regs R12 +
  count_public_register regs R13 +
  count_public_register regs R14 +
  count_public_register regs R15

let count_flagTaint (ts:taintState) : nat = if Public? ts.flagsTaint then 1 else 0

let count_cfFlagTaint (ts:taintState) : nat = if Public? ts.cfFlagsTaint then 1 else 0

let count_public_xmm (xmms:xmms_taint) (x:xmm) : nat = if Public? (xmms x) then 1 else 0

let count_public_xmms (xmms:xmms_taint) : nat =
  count_public_xmm xmms 0 +
  count_public_xmm xmms 1 +
  count_public_xmm xmms 2 +
  count_public_xmm xmms 3 +
  count_public_xmm xmms 4 +
  count_public_xmm xmms 5 +
  count_public_xmm xmms 6 +
  count_public_xmm xmms 7 +
  count_public_xmm xmms 8 +
  count_public_xmm xmms 9 +
  count_public_xmm xmms 10 +
  count_public_xmm xmms 11 +
  count_public_xmm xmms 12 +
  count_public_xmm xmms 13 +
  count_public_xmm xmms 14 +
  count_public_xmm xmms 15

let count_publics (ts:taintState) : nat =
  count_public_registers ts.regTaint +
  count_flagTaint ts +
  count_cfFlagTaint ts +
  count_public_xmms ts.xmmTaint

#set-options "--z3rlimit 50"

#push-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 1 --initial_ifuel 1"
let monotone_decreases_count (ts ts':taintState) : Lemma
  (requires taintstate_monotone ts ts' /\ not (eq_taintStates ts ts'))
  (ensures count_publics ts' < count_publics ts)  
  =
  assert (forall r. count_public_register ts'.regTaint r <= count_public_register ts.regTaint r);
  assert (forall r. count_public_xmm ts'.xmmTaint r <= count_public_xmm ts.xmmTaint r);
  assert (count_cfFlagTaint ts' <= count_cfFlagTaint ts);
  assert (count_flagTaint ts' <= count_flagTaint ts)
#pop-options

val check_if_block_consumes_fixed_time: (block:tainted_codes) -> (ts:taintState) -> Tot (bool * taintState)
(decreases %[block])
val check_if_code_consumes_fixed_time: (code:tainted_code) -> (ts:taintState) -> Tot (bool * taintState) (decreases %[code; count_publics ts; 1])
val check_if_loop_consumes_fixed_time: (code:tainted_code{While? code}) -> (ts:taintState) -> Tot (bool * taintState) (decreases %[code; count_publics ts; 0])

#set-options "--z3refresh --z3rlimit 600"
let rec check_if_block_consumes_fixed_time (block:tainted_codes) (ts:taintState) : bool * taintState =
  match block with
  | [] -> true, ts
  | hd::tl -> let fixedTime, ts_int = check_if_code_consumes_fixed_time hd ts in
    if (not fixedTime) then fixedTime, ts_int
    else check_if_block_consumes_fixed_time tl ts_int


and check_if_code_consumes_fixed_time (code:tainted_code) (ts:taintState) : bool * taintState =
  match code with
  | Ins ins -> if is_xmm_ins ins then check_if_xmm_ins_consumes_fixed_time ins ts
        else check_if_ins_consumes_fixed_time ins ts

  | Block block -> check_if_block_consumes_fixed_time block ts

  | IfElse ifCond ifTrue ifFalse ->
    let cond_taint = ifCond.ot in
    let o1 = operand_taint (get_fst_ocmp ifCond.o) ts Public in
    let o2 = operand_taint (get_snd_ocmp ifCond.o) ts Public in
    let predTaint = merge_taint (merge_taint o1 o2) cond_taint in
    if (Secret? predTaint) then (false, ts)
    else
      let o1Public = operand_does_not_use_secrets (get_fst_ocmp ifCond.o) ts in
      if (not o1Public) then (false, ts)
      else
      let o2Public = operand_does_not_use_secrets (get_snd_ocmp ifCond.o) ts in
      if (not o2Public) then (false, ts)
      else
      let validIfTrue, tsIfTrue = check_if_code_consumes_fixed_time ifTrue ts in
      if (not validIfTrue) then (false, ts)
      else
      let validIfFalse, tsIfFalse = check_if_code_consumes_fixed_time ifFalse ts in
      if (not validIfFalse) then (false, ts)
      else
      (true, combine_taint_states tsIfTrue tsIfFalse)

  | While cond body -> check_if_loop_consumes_fixed_time code ts

and check_if_loop_consumes_fixed_time c (ts:taintState) : (bool * taintState) =
  let While pred body = c in
  let cond_taint = pred.ot in
  let o1 = operand_taint (get_fst_ocmp pred.o) ts Public in
  let o2 = operand_taint (get_snd_ocmp pred.o) ts Public in
  let predTaint = merge_taint (merge_taint o1 o2) cond_taint in
  if (Secret? predTaint) then false, ts
  else
    let o1Public = operand_does_not_use_secrets (get_fst_ocmp pred.o) ts in
    if (not o1Public) then (false, ts)
    else
    let o2Public = operand_does_not_use_secrets (get_snd_ocmp pred.o) ts in
    if (not o2Public) then (false, ts)
    else
    let fixedTime, next_ts = check_if_code_consumes_fixed_time body ts in
    if (not fixedTime) then (false, ts)
    else
    let combined_ts = combine_taint_states ts next_ts in
    assert (taintstate_monotone ts combined_ts);
    if eq_taintStates combined_ts ts then
      true, combined_ts
    else (
      monotone_decreases_count ts combined_ts;
      check_if_loop_consumes_fixed_time c combined_ts
    )

val monotone_ok_eval: (code:tainted_code) -> (fuel:nat) -> (s:traceState) -> Lemma
 (requires True)
 (ensures (let s' = taint_eval_code code fuel s in
    Some? s' /\ (Some?.v s').state.S.ok ==> s.state.S.ok))
 (decreases %[code; 0])

val monotone_ok_eval_block: (codes:tainted_codes) -> (fuel:nat) -> (s:traceState) -> Lemma
 (requires True)
 (ensures (let s' = taint_eval_codes codes fuel s in
    Some? s' /\ (Some?.v s').state.S.ok ==> s.state.S.ok))
 (decreases %[codes;1])

#set-options "--z3rlimit 20 --initial_ifuel 0 --max_ifuel 1 --initial_fuel 2 --max_fuel 2"
let rec monotone_ok_eval code fuel s = match code with
  | Ins ins -> ()
  | Block block -> monotone_ok_eval_block block fuel s
  | IfElse ifCond ifTrue ifFalse ->
    let st, b = taint_eval_ocmp s ifCond in
    let st = {st with trace=BranchPredicate(b)::s.trace} in
    if b then monotone_ok_eval ifTrue fuel st else monotone_ok_eval ifFalse fuel st
  | While cond body ->
    if fuel = 0 then ()
    else
    let st, b = taint_eval_ocmp s cond in
    if not b then ()
    else
    let st = {st with trace=BranchPredicate(b)::s.trace} in
    monotone_ok_eval body (fuel-1) st;
    ()

and monotone_ok_eval_block block fuel s =
  match block with
  | [] -> ()
  | hd :: tl ->
    let s' = taint_eval_code hd fuel s in
    if None? s' then () else
    monotone_ok_eval_block tl fuel (Some?.v s');
    monotone_ok_eval hd fuel s

val monotone_ok_eval_while: (code:tainted_code{While? code}) -> (fuel:nat) -> (s:traceState) -> Lemma
  (requires True)
  (ensures (
      let While cond body = code in
      let (s1, b1) = taint_eval_ocmp s cond in
      let r1 = taint_eval_code code fuel s in
      Some? r1 /\ (Some?.v r1).state.S.ok ==> s1.state.S.ok))

let monotone_ok_eval_while code fuel s =
  let While cond body = code in
  let (s1, b) = taint_eval_ocmp s cond in
  let r1 = taint_eval_while code fuel s in
  if fuel = 0 then ()
  else if not b then ()
  else let s0 = {s1 with trace = BranchPredicate(true)::s1.trace} in
  let s_opt = taint_eval_code body (fuel - 1) s0 in
  match s_opt with
    | None -> ()
    | Some s -> if not s.state.S.ok then ()
      else monotone_ok_eval body (fuel -1) s0; monotone_ok_eval code (fuel - 1) s

val lemma_loop_taintstate_monotone: (ts:taintState) -> (code:tainted_code{While? code}) -> Lemma
(requires True)
(ensures (let _, ts' = check_if_loop_consumes_fixed_time code ts in
  taintstate_monotone ts ts'))
(decreases %[count_publics ts])

#reset-options "--initial_ifuel 1 --max_ifuel 1 --initial_fuel 2 --max_fuel 2 --z3rlimit 40"
let rec lemma_loop_taintstate_monotone ts code =
  let While pred body = code in
  let b, ts' = check_if_code_consumes_fixed_time body ts in
  let combined_ts = combine_taint_states ts ts' in
  if eq_taintStates combined_ts ts then ()
  else (
    monotone_decreases_count ts combined_ts;
    let b, ts_fin = check_if_loop_consumes_fixed_time code combined_ts in
    lemma_loop_taintstate_monotone combined_ts code;
    taintstate_monotone_trans ts combined_ts ts_fin
  )

#reset-options "--initial_ifuel 1 --max_ifuel 1 --initial_fuel 2 --max_fuel 2 --z3rlimit 60"
val lemma_code_explicit_leakage_free: (ts:taintState) -> (code:tainted_code) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
 (requires True)
 (ensures (let b, ts' = check_if_code_consumes_fixed_time code ts in
  (b2t b ==> isConstantTimeGivenStates code fuel ts s1 s2 /\ isExplicitLeakageFreeGivenStates code fuel ts ts' s1 s2)))
 (decreases %[fuel; code; 1])

val lemma_block_explicit_leakage_free: (ts:taintState) -> (codes:tainted_codes) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
 (requires True)
 (ensures (let b, ts' = check_if_block_consumes_fixed_time codes ts in
  (b2t b ==> isConstantTimeGivenStates (Block codes) fuel ts s1 s2 /\ isExplicitLeakageFreeGivenStates (Block codes) fuel ts ts' s1 s2)))
 (decreases %[fuel; codes; 2])

val lemma_loop_explicit_leakage_free: (ts:taintState) -> (code:tainted_code{While? code}) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
 (requires True)
 (ensures (let b, ts' = check_if_loop_consumes_fixed_time code ts in
  (b2t b ==> isConstantTimeGivenStates code fuel ts s1 s2 /\ isExplicitLeakageFreeGivenStates code fuel ts ts' s1 s2)))
 (decreases %[fuel; code; 0])

#reset-options "--initial_ifuel 2 --max_ifuel 2 --initial_fuel 1 --max_fuel 2 --z3rlimit 300"
 let rec lemma_code_explicit_leakage_free ts code s1 s2 fuel = match code with
  | Ins ins -> if is_xmm_ins ins then () else lemma_ins_leakage_free ts ins
  | Block block -> lemma_block_explicit_leakage_free ts block s1 s2 fuel
  | IfElse ifCond ifTrue ifFalse ->
    let b_fin, ts_fin = check_if_code_consumes_fixed_time code ts in
    let st1, b1 = taint_eval_ocmp s1 ifCond in
    let st1 = {st1 with trace=BranchPredicate(b1)::s1.trace} in
    let st2, b2 = taint_eval_ocmp s2 ifCond in
    let st2 = {st2 with trace=BranchPredicate(b2)::s2.trace} in
    assert (b2t b_fin ==> constTimeInvariant ts s1 s2 /\ st1.state.S.ok /\ st2.state.S.ok ==> constTimeInvariant ts st1 st2);
    monotone_ok_eval ifTrue fuel st1;
    monotone_ok_eval ifTrue fuel st2;
    lemma_code_explicit_leakage_free ts ifTrue st1 st2 fuel;
    monotone_ok_eval ifFalse fuel st1;
    monotone_ok_eval ifFalse fuel st2;
    lemma_code_explicit_leakage_free ts ifFalse st1 st2 fuel
  | While _ _ -> lemma_loop_explicit_leakage_free ts code s1 s2 fuel

and lemma_block_explicit_leakage_free ts block s1 s2 fuel = match block with
  | [] -> ()
  | hd :: tl ->
    let b, ts' = check_if_code_consumes_fixed_time hd ts in
    lemma_code_explicit_leakage_free ts hd s1 s2 fuel;
    let s'1 = taint_eval_code hd fuel s1 in
    let s'2 = taint_eval_code hd fuel s2 in
    if None? s'1 || None? s'2 then ()
    else
    let s'1 = Some?.v s'1 in
    let s'2 = Some?.v s'2 in
    lemma_block_explicit_leakage_free ts' tl s'1 s'2 fuel;
    monotone_ok_eval (Block tl) fuel s'1;
    monotone_ok_eval (Block tl) fuel s'2

and lemma_loop_explicit_leakage_free ts code s1 s2 fuel =
  if fuel = 0 then ()
  else
  let b_fin, ts_fin = check_if_code_consumes_fixed_time code ts in
  let r1 = taint_eval_code code fuel s1 in
  let r2 = taint_eval_code code fuel s2 in
  let While cond body = code in
  let (st1, b1) = taint_eval_ocmp s1 cond in
  let (st2, b2) = taint_eval_ocmp s2 cond in

  assert (b2t b_fin ==> constTimeInvariant ts s1 s2 /\ st1.state.S.ok /\ st2.state.S.ok ==> b1 = b2);
  assert (b2t b_fin ==> constTimeInvariant ts s1 s2 /\ st1.state.S.ok /\ st2.state.S.ok ==> constTimeInvariant ts st1 st2);
  if not b1 || not b2 then
  (
  assert (b2t b_fin ==> constTimeInvariant ts s1 s2 /\ st1.state.S.ok /\ st2.state.S.ok ==> not b1 /\ not b2);
  assert (not b1 ==> r1 == Some ({st1 with trace = BranchPredicate(false)::st1.trace}));
  assert (not b2 ==> r2 == Some ({st2 with trace = BranchPredicate(false)::st2.trace}));
  monotone_ok_eval_while code fuel s1;
  assert (Some? r1 /\ (Some?.v r1).state.S.ok ==> st1.state.S.ok);
  monotone_ok_eval_while code fuel s2;
  assert (Some? r2 /\ (Some?.v r2).state.S.ok ==> st2.state.S.ok);
  lemma_loop_taintstate_monotone ts code;
  isExplicit_monotone ts ts ts_fin code fuel s1 s2;
  ()
  )
  else
  let st'1 = ({st1 with trace = BranchPredicate(true)::st1.trace}) in
  let st'2 = ({st2 with trace = BranchPredicate(true)::st2.trace}) in
  assert (b2t b_fin ==> constTimeInvariant ts s1 s2 /\ st'1.state.S.ok /\ st'2.state.S.ok ==> constTimeInvariant ts st'1 st'2);
  let b', ts' = check_if_code_consumes_fixed_time body ts in
  lemma_code_explicit_leakage_free ts body st'1 st'2 (fuel-1);
  monotone_ok_eval body (fuel-1) st'1;
  monotone_ok_eval body (fuel-1) st'2;
  let st1 = taint_eval_code body (fuel - 1) st'1 in
  let st2 = taint_eval_code body (fuel - 1) st'2 in
  assert (None? st1 ==> r1 == st1);
  assert (None? st2 ==> r2 == st2);
  if (None? st1 || None? st2) then ()
  else
  let st1 = Some?.v st1 in
  let st2 = Some?.v st2 in
  if not st1.state.S.ok || not st2.state.S.ok then ()
  else
  let combined_ts = combine_taint_states ts ts' in
  let b_aux, ts_aux = check_if_loop_consumes_fixed_time code combined_ts in
  lemma_loop_explicit_leakage_free combined_ts code st1 st2 (fuel-1);
  isConstant_monotone ts combined_ts code (fuel-1) st1 st2;
  isExplicit_monotone2 ts_aux ts combined_ts code (fuel-1) st1 st2;
  assert (b2t b_fin ==> constTimeInvariant ts s1 s2 /\ st1.state.S.ok /\ st2.state.S.ok ==> constTimeInvariant ts' st1 st2)

val lemma_code_leakage_free: (ts:taintState) -> (code:tainted_code) -> Lemma
 (let b, ts' = check_if_code_consumes_fixed_time code ts in
  (b2t b ==> isConstantTime code ts /\ isLeakageFree code ts ts'))

let lemma_code_leakage_free ts code = FStar.Classical.forall_intro_3 (lemma_code_explicit_leakage_free ts code)

#set-options "--z3rlimit 20"
val check_if_code_is_leakage_free: (code:tainted_code) -> (ts:taintState) -> (tsExpected:taintState) -> (b:bool{b ==> isLeakageFree code ts tsExpected
         /\ b ==> isConstantTime code ts})

let check_if_code_is_leakage_free code ts tsExpected =
  let b, ts' = check_if_code_consumes_fixed_time code ts in
  if b then
    publicTaintsAreAsExpected ts' tsExpected
  else
    b
