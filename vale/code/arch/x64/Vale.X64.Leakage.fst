module Vale.X64.Leakage
open Vale.X64.Machine_s
module S = Vale.X64.Machine_Semantics_s
open Vale.X64.Leakage_s
open Vale.X64.Leakage_Helpers
open Vale.X64.Leakage_Ins

unfold let machine_eval_ocmp = S.machine_eval_ocmp
unfold let machine_eval_code = S.machine_eval_code
unfold let machine_eval_codes = S.machine_eval_codes
unfold let machine_eval_while = S.machine_eval_while

#reset-options "--initial_ifuel 0 --max_ifuel 1 --initial_fuel 1 --max_fuel 1"
let combine_reg_taints (regs1 regs2:reg_taint) : reg_taint =
  FunctionalExtensionality.on reg (fun x -> merge_taint (regs1 x) (regs2 x))

let rec eq_regs_file (regs1 regs2:reg_taint) (rf:reg_file_id) (k:nat{k <= n_regs rf}) : bool =
  if k = 0 then true
  else regs1 (Reg rf (k - 1)) = regs2 (Reg rf (k - 1)) && eq_regs_file regs1 regs2 rf (k - 1)

let rec eq_regs (regs1 regs2:reg_taint) (k:nat{k <= n_reg_files}) : bool =
  if k = 0 then true
  else eq_regs_file regs1 regs2 (k - 1) (n_regs (k - 1)) && eq_regs regs1 regs2 (k - 1)

let rec lemma_eq_regs_file (regs1 regs2:reg_taint) (rf:reg_file_id) (k:nat{k <= n_regs rf}) : Lemma
  (ensures eq_regs_file regs1 regs2 rf k <==>
    (forall (i:nat).{:pattern (Reg rf i)} i < k ==> regs1 (Reg rf i) == regs2 (Reg rf i)))
  =
  if k > 0 then lemma_eq_regs_file regs1 regs2 rf (k - 1)

let rec lemma_eq_regs (regs1 regs2:reg_taint) (k:nat{k <= n_reg_files}) : Lemma
  (ensures
    eq_regs regs1 regs2 k <==>
    (forall (i j:nat).{:pattern (Reg i j)} i < k /\ j < n_regs i ==>
      regs1 (Reg i j) == regs2 (Reg i j)))
  =
  if k > 0 then (
    lemma_eq_regs_file regs1 regs2 (k - 1) (n_regs (k - 1));
    lemma_eq_regs regs1 regs2 (k - 1)
  )

let eq_registers (regs1 regs2:reg_taint) : (b:bool{b <==> regs1 == regs2}) =
  lemma_eq_regs regs1 regs2 n_reg_files;
  let b = eq_regs regs1 regs2 n_reg_files in
  if b then (
    assert (FStar.FunctionalExtensionality.feq regs1 regs2)
  );
  b

let eq_taintStates (ts1 ts2:analysis_taints) : (b:bool{b <==> ts1 == ts2}) =
  eq_registers ts1.regTaint ts2.regTaint &&
  ts1.flagsTaint = ts2.flagsTaint &&
  ts1.cfFlagsTaint = ts2.cfFlagsTaint &&
  ts1.ofFlagsTaint = ts2.ofFlagsTaint

let taintstate_monotone_regs (ts ts':reg_taint) =
  (forall (r:reg).{:pattern (ts' r) \/ (ts r)}
    Public? (ts' r) ==> Public? (ts r))

let taintstate_monotone (ts ts':analysis_taints) =
  taintstate_monotone_regs ts.regTaint ts'.regTaint /\
  (Public? (ts'.flagsTaint) ==> Public? (ts.flagsTaint)) /\
  (Public? (ts'.cfFlagsTaint) ==> Public? (ts.cfFlagsTaint)) /\
  (Public? (ts'.ofFlagsTaint) ==> Public? (ts.ofFlagsTaint))

let taintstate_monotone_trans (ts1:analysis_taints) (ts2:analysis_taints) (ts3:analysis_taints)
  : Lemma (taintstate_monotone ts1 ts2 /\ taintstate_monotone ts2 ts3 ==> taintstate_monotone ts1 ts3) = ()

let isConstant_monotone (ts1:analysis_taints) (ts2:analysis_taints) (code:S.code) (fuel:nat) (s1:S.machine_state) (s2:S.machine_state)
  : Lemma (isConstantTimeGivenStates code fuel ts2 s1 s2 /\ taintstate_monotone ts1 ts2 ==> isConstantTimeGivenStates code fuel ts1 s1 s2)
  = ()

let isExplicit_monotone (ts:analysis_taints) (ts1:analysis_taints) (ts2:analysis_taints) (code:S.code)
  (fuel:nat) (s1:S.machine_state) (s2:S.machine_state)
  : Lemma (isExplicitLeakageFreeGivenStates code fuel ts ts1 s1 s2 /\ taintstate_monotone ts1 ts2 ==> isExplicitLeakageFreeGivenStates code fuel ts ts2 s1 s2)
  = ()

let isExplicit_monotone2 (ts:analysis_taints) (ts1:analysis_taints) (ts2:analysis_taints)
  (code:S.code) (fuel:nat) (s1:S.machine_state) (s2:S.machine_state)
  : Lemma (isExplicitLeakageFreeGivenStates code fuel ts2 ts s1 s2 /\ taintstate_monotone ts1 ts2 ==> isExplicitLeakageFreeGivenStates code fuel ts1 ts s1 s2)
  = ()

let combine_taint_states (ts1:analysis_taints) (ts2:analysis_taints) : (ts:analysis_taints{taintstate_monotone ts1 ts /\ taintstate_monotone ts2 ts}) =
  AnalysisTaints
    (combine_reg_taints ts1.regTaint ts2.regTaint)
    (merge_taint ts1.flagsTaint ts2.flagsTaint)
    (merge_taint ts1.cfFlagsTaint ts2.cfFlagsTaint)
    (merge_taint ts1.ofFlagsTaint ts2.ofFlagsTaint)

let count_public_register (regs:reg_taint) (r:reg) = if Public? (regs r) then 1 else 0

let rec count_public_registers_file (regs:reg_taint) (rf:reg_file_id) (k:nat{k <= n_regs rf}) : nat =
  if k = 0 then 0
  else count_public_register regs (Reg rf (k - 1)) + count_public_registers_file regs rf (k - 1)

let rec lemma_count_public_registers_file (regs1 regs2:reg_taint) (rf:reg_file_id) (k:nat{k <= n_regs rf}) : Lemma
  (requires
    taintstate_monotone_regs regs2 regs1 /\
    count_public_registers_file regs1 rf k >= count_public_registers_file regs2 rf k
  )
  (ensures
    count_public_registers_file regs1 rf k == count_public_registers_file regs2 rf k /\
    (forall (i:nat).{:pattern regs1 (Reg rf i) \/ regs2 (Reg rf i)} i < k ==> regs1 (Reg rf i) == regs2 (Reg rf i))
  )
  =
  if k > 0 then lemma_count_public_registers_file regs1 regs2 rf (k - 1)

let rec count_public_registers (regs:reg_taint) (k:nat{k <= n_reg_files}) : nat =
  if k = 0 then 0
  else count_public_registers_file regs (k - 1) (n_regs (k - 1)) + count_public_registers regs (k - 1)

let rec lemma_count_public_registers (regs1 regs2:reg_taint) (k:nat{k <= n_reg_files}) : Lemma
  (requires
    taintstate_monotone_regs regs2 regs1 /\
    count_public_registers regs1 k >= count_public_registers regs2 k
  )
  (ensures
    count_public_registers regs1 k == count_public_registers regs2 k /\
    (forall (r:reg).{:pattern regs1 r \/ regs2 r} Reg?.rf r < k ==> regs1 r == regs2 r)
  )
  =
  if k > 0 then (
    let n = n_regs (k - 1) in
    if count_public_registers_file regs1 (k - 1) n >= count_public_registers_file regs2 (k - 1) n then
      lemma_count_public_registers_file regs1 regs2 (k - 1) n;
    lemma_count_public_registers regs1 regs2 (k - 1)
  )

let count_flagTaint (ts:analysis_taints) : nat = if Public? ts.flagsTaint then 1 else 0

let count_cfFlagTaint (ts:analysis_taints) : nat = if Public? ts.cfFlagsTaint then 1 else 0

let count_ofFlagTaint (ts:analysis_taints) : nat = if Public? ts.ofFlagsTaint then 1 else 0

let count_publics (ts:analysis_taints) : nat =
  count_public_registers ts.regTaint n_reg_files +
  count_flagTaint ts +
  count_cfFlagTaint ts +
  count_ofFlagTaint ts

let monotone_decreases_count (ts ts':analysis_taints) : Lemma
  (requires taintstate_monotone ts ts' /\ not (eq_taintStates ts ts'))
  (ensures count_publics ts' < count_publics ts)
  =
  let regs1 = ts'.regTaint in
  let regs2 = ts.regTaint in
  if count_public_registers regs1 n_reg_files >= count_public_registers regs2 n_reg_files then (
    lemma_count_public_registers regs1 regs2 n_reg_files;
    assert (FStar.FunctionalExtensionality.feq regs1 regs2)
  )

val check_if_block_consumes_fixed_time (block:S.codes) (ts:analysis_taints) : Tot (bool & analysis_taints)
  (decreases %[block])
val check_if_code_consumes_fixed_time (code:S.code) (ts:analysis_taints) : Tot (bool & analysis_taints)
  (decreases %[code; count_publics ts; 1])
val check_if_loop_consumes_fixed_time (code:S.code{While? code}) (ts:analysis_taints) : Tot (bool & analysis_taints)
  (decreases %[code; count_publics ts; 0])

#set-options "--z3refresh --z3rlimit 600"
let rec check_if_block_consumes_fixed_time (block:S.codes) (ts:analysis_taints) : bool & analysis_taints =
  match block with
  | [] -> true, ts
  | hd::tl -> let fixedTime, ts_int = check_if_code_consumes_fixed_time hd ts in
    if (not fixedTime) then fixedTime, ts_int
    else check_if_block_consumes_fixed_time tl ts_int

and check_if_code_consumes_fixed_time (code:S.code) (ts:analysis_taints) : bool & analysis_taints =
  match code with
  | Ins ins ->  let b, ts = check_if_ins_consumes_fixed_time ins ts in b, ts

  | Block block -> check_if_block_consumes_fixed_time block ts

  | IfElse ifCond ifTrue ifFalse ->
    let o1 = operand_taint 0 (S.get_fst_ocmp ifCond) ts in
    let o2 = operand_taint 0 (S.get_snd_ocmp ifCond) ts in
    let predTaint = merge_taint o1 o2 in
    if (Secret? predTaint) then (false, ts)
    else
      let o1Public = operand_does_not_use_secrets (S.get_fst_ocmp ifCond) ts in
      if (not o1Public) then (false, ts)
      else
      let o2Public = operand_does_not_use_secrets (S.get_snd_ocmp ifCond) ts in
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

and check_if_loop_consumes_fixed_time c (ts:analysis_taints) : (bool & analysis_taints) =
  let While pred body = c in
  let o1 = operand_taint 0 (S.get_fst_ocmp pred) ts in
  let o2 = operand_taint 0 (S.get_snd_ocmp pred) ts in
  let predTaint = merge_taint o1 o2 in
  if (Secret? predTaint) then false, ts
  else
    let o1Public = operand_does_not_use_secrets (S.get_fst_ocmp pred) ts in
    if (not o1Public) then (false, ts)
    else
    let o2Public = operand_does_not_use_secrets (S.get_snd_ocmp pred) ts in
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

val monotone_ok_eval: (code:S.code) -> (fuel:nat) -> (s:S.machine_state) -> Lemma
 (requires True)
 (ensures (let s' = machine_eval_code code fuel s in
    Some? s' /\ (Some?.v s').S.ms_ok ==> s.S.ms_ok))
 (decreases %[code; 0])

val monotone_ok_eval_block: (codes:S.codes) -> (fuel:nat) -> (s:S.machine_state) -> Lemma
 (requires True)
 (ensures (let s' = machine_eval_codes codes fuel s in
    Some? s' /\ (Some?.v s').S.ms_ok ==> s.S.ms_ok))
 (decreases %[codes;1])

#set-options "--z3rlimit 20 --initial_ifuel 0 --max_ifuel 1 --initial_fuel 2 --max_fuel 2"
let rec monotone_ok_eval code fuel s =
  match code with
  | Ins ins -> ()
  | Block block -> monotone_ok_eval_block block fuel s
  | IfElse ifCond ifTrue ifFalse ->
    let st, b = machine_eval_ocmp s ifCond in
    let st = {st with S.ms_trace = BranchPredicate(b)::s.S.ms_trace} in
    if b then monotone_ok_eval ifTrue fuel st else monotone_ok_eval ifFalse fuel st
  | While cond body ->
    if fuel = 0 then ()
    else
    let st, b = machine_eval_ocmp s cond in
    if not b then ()
    else
    let st = {st with S.ms_trace = BranchPredicate(b)::s.S.ms_trace} in
    monotone_ok_eval body (fuel-1) st;
    ()

and monotone_ok_eval_block block fuel s =
  match block with
  | [] -> ()
  | hd :: tl ->
    let s' = machine_eval_code hd fuel s in
    if None? s' then () else
    monotone_ok_eval_block tl fuel (Some?.v s');
    monotone_ok_eval hd fuel s

val monotone_ok_eval_while: (code:S.code{While? code}) -> (fuel:nat) -> (s:S.machine_state) -> Lemma
  (requires True)
  (ensures (
    let While cond body = code in
    let (s1, b1) = machine_eval_ocmp s cond in
    let r1 = machine_eval_code code fuel s in
    Some? r1 /\ (Some?.v r1).S.ms_ok ==> s1.S.ms_ok))

let monotone_ok_eval_while code fuel s =
  let While cond body = code in
  let (s1, b) = machine_eval_ocmp s cond in
  let r1 = machine_eval_while code fuel s in
  if fuel = 0 then ()
  else if not b then ()
  else let s0 = {s1 with S.ms_trace = BranchPredicate(true)::s1.S.ms_trace} in
  let s_opt = machine_eval_code body (fuel - 1) s0 in
  match s_opt with
  | None -> ()
  | Some s -> if not s.S.ms_ok then ()
    else monotone_ok_eval body (fuel -1) s0; monotone_ok_eval code (fuel - 1) s

val lemma_loop_taintstate_monotone (ts:analysis_taints) (code:S.code{While? code}) : Lemma
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
val lemma_code_explicit_leakage_free: (ts:analysis_taints) -> (code:S.code) -> (s1:S.machine_state) -> (s2:S.machine_state) -> (fuel:nat) -> Lemma
  (requires True)
  (ensures (let b, ts' = check_if_code_consumes_fixed_time code ts in
    (b2t b ==> isConstantTimeGivenStates code fuel ts s1 s2 /\ isExplicitLeakageFreeGivenStates code fuel ts ts' s1 s2)))
  (decreases %[fuel; code; 1])

val lemma_block_explicit_leakage_free: (ts:analysis_taints) -> (codes:S.codes) -> (s1:S.machine_state) -> (s2:S.machine_state) -> (fuel:nat) -> Lemma
  (requires True)
  (ensures (let b, ts' = check_if_block_consumes_fixed_time codes ts in
    (b2t b ==> isConstantTimeGivenStates (Block codes) fuel ts s1 s2 /\ isExplicitLeakageFreeGivenStates (Block codes) fuel ts ts' s1 s2)))
  (decreases %[fuel; codes; 2])

val lemma_loop_explicit_leakage_free: (ts:analysis_taints) -> (code:S.code{While? code}) -> (s1:S.machine_state) -> (s2:S.machine_state) -> (fuel:nat) -> Lemma
  (requires True)
  (ensures (let b, ts' = check_if_loop_consumes_fixed_time code ts in
    (b2t b ==> isConstantTimeGivenStates code fuel ts s1 s2 /\ isExplicitLeakageFreeGivenStates code fuel ts ts' s1 s2)))
  (decreases %[fuel; code; 0])

#reset-options "--initial_ifuel 2 --max_ifuel 2 --initial_fuel 1 --max_fuel 2 --z3rlimit 300"
let rec lemma_code_explicit_leakage_free ts code s1 s2 fuel = match code with
  | Ins ins -> lemma_ins_leakage_free ts ins
  | Block block -> lemma_block_explicit_leakage_free ts block s1 s2 fuel
  | IfElse ifCond ifTrue ifFalse ->
    let b_fin, ts_fin = check_if_code_consumes_fixed_time code ts in
    let st1, b1 = machine_eval_ocmp s1 ifCond in
    let st1 = {st1 with S.ms_trace = BranchPredicate(b1)::s1.S.ms_trace} in
    let st2, b2 = machine_eval_ocmp s2 ifCond in
    let st2 = {st2 with S.ms_trace = BranchPredicate(b2)::s2.S.ms_trace} in
    assert (b2t b_fin ==> constTimeInvariant ts s1 s2 /\ st1.S.ms_ok /\ st2.S.ms_ok ==> constTimeInvariant ts st1 st2);
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
    let s'1 = machine_eval_code hd fuel s1 in
    let s'2 = machine_eval_code hd fuel s2 in
    if None? s'1 || None? s'2 then ()
    else
    let s'1 = Some?.v s'1 in
    let s'2 = Some?.v s'2 in
    lemma_block_explicit_leakage_free ts' tl s'1 s'2 fuel;
    monotone_ok_eval (Block tl) fuel s'1;
    monotone_ok_eval (Block tl) fuel s'2

and lemma_loop_explicit_leakage_free ts code s1 s2 fuel =
  if fuel = 0 then () else
  let b_fin, ts_fin = check_if_code_consumes_fixed_time code ts in
  let r1 = machine_eval_code code fuel s1 in
  let r2 = machine_eval_code code fuel s2 in
  let While cond body = code in
  let (st1, b1) = machine_eval_ocmp s1 cond in
  let (st2, b2) = machine_eval_ocmp s2 cond in

  assert (b2t b_fin ==> constTimeInvariant ts s1 s2 /\ st1.S.ms_ok /\ st2.S.ms_ok ==> b1 = b2);
  assert (b2t b_fin ==> constTimeInvariant ts s1 s2 /\ st1.S.ms_ok /\ st2.S.ms_ok ==> constTimeInvariant ts st1 st2);
  if not b1 || not b2 then
  (
    assert (b2t b_fin ==> constTimeInvariant ts s1 s2 /\ st1.S.ms_ok /\ st2.S.ms_ok ==> not b1 /\ not b2);
    assert (not b1 ==> r1 == Some ({st1 with S.ms_trace = BranchPredicate(false)::st1.S.ms_trace}));
    assert (not b2 ==> r2 == Some ({st2 with S.ms_trace = BranchPredicate(false)::st2.S.ms_trace}));
    monotone_ok_eval_while code fuel s1;
    assert (Some? r1 /\ (Some?.v r1).S.ms_ok ==> st1.S.ms_ok);
    monotone_ok_eval_while code fuel s2;
    assert (Some? r2 /\ (Some?.v r2).S.ms_ok ==> st2.S.ms_ok);
    lemma_loop_taintstate_monotone ts code;
    isExplicit_monotone ts ts ts_fin code fuel s1 s2;
    ()
  )
  else
    let st'1 = ({st1 with S.ms_trace = BranchPredicate(true)::st1.S.ms_trace}) in
    let st'2 = ({st2 with S.ms_trace = BranchPredicate(true)::st2.S.ms_trace}) in
    assert (b2t b_fin ==> constTimeInvariant ts s1 s2 /\ st'1.S.ms_ok /\ st'2.S.ms_ok ==> constTimeInvariant ts st'1 st'2);
  let b', ts' = check_if_code_consumes_fixed_time body ts in
  lemma_code_explicit_leakage_free ts body st'1 st'2 (fuel-1);
  monotone_ok_eval body (fuel-1) st'1;
  monotone_ok_eval body (fuel-1) st'2;
  let st1 = machine_eval_code body (fuel - 1) st'1 in
  let st2 = machine_eval_code body (fuel - 1) st'2 in
  assert (None? st1 ==> r1 == st1);
  assert (None? st2 ==> r2 == st2);
  if (None? st1 || None? st2) then () else
  let st1 = Some?.v st1 in
  let st2 = Some?.v st2 in
  if not st1.S.ms_ok || not st2.S.ms_ok then () else
  let combined_ts = combine_taint_states ts ts' in
  let b_aux, ts_aux = check_if_loop_consumes_fixed_time code combined_ts in
  lemma_loop_explicit_leakage_free combined_ts code st1 st2 (fuel-1);
  isConstant_monotone ts combined_ts code (fuel-1) st1 st2;
  isExplicit_monotone2 ts_aux ts combined_ts code (fuel-1) st1 st2;
  assert (b2t b_fin ==> constTimeInvariant ts s1 s2 /\ st1.S.ms_ok /\ st2.S.ms_ok ==> constTimeInvariant ts' st1 st2)

val lemma_code_leakage_free: (ts:analysis_taints) -> (code:S.code) -> Lemma
 (let b, ts' = check_if_code_consumes_fixed_time code ts in
  (b2t b ==> isConstantTime code ts /\ isLeakageFree code ts ts'))

let lemma_code_leakage_free ts code = FStar.Classical.forall_intro_3 (lemma_code_explicit_leakage_free ts code)

#set-options "--z3rlimit 20"
val check_if_code_is_leakage_free': (code:S.code) -> (ts:analysis_taints) -> (tsExpected:analysis_taints) -> (b:bool{b ==> isLeakageFree code ts tsExpected
         /\ b ==> isConstantTime code ts})

let check_if_code_is_leakage_free' code ts tsExpected =
  let b, ts' = check_if_code_consumes_fixed_time code ts in
  if b then
    publicTaintsAreAsExpected ts' tsExpected
  else
    b

let check_if_code_is_leakage_free code ts public_return =
  let b, ts' = check_if_code_consumes_fixed_time code ts in
  if public_return then
    b && Public? (ts'.regTaint reg_Rax)
  else b

// Only the args should be public
let mk_analysis_taints win nbr_args : analysis_taints =
  let regTaint r =
    if win then
      if r = reg_Rsp then Public else
      if r = reg_Rcx && nbr_args >= 1 then Public else
      if r = reg_Rdx && nbr_args >= 2 then Public else
      if r = reg_R8  && nbr_args >= 3 then Public else
      if r = reg_R9  && nbr_args >= 4 then Public else
      Secret
    else
      if r = reg_Rsp then Public else
      if r = reg_Rdi && nbr_args >= 1 then Public else
      if r = reg_Rsi && nbr_args >= 2 then Public else
      if r = reg_Rdx && nbr_args >= 3 then Public else
      if r = reg_Rcx && nbr_args >= 4 then Public else
      if r = reg_R8  && nbr_args >= 5 then Public else
      if r = reg_R9  && nbr_args >= 6 then Public else
      Secret
    in
  AnalysisTaints (FunctionalExtensionality.on reg regTaint) Secret Secret Secret
