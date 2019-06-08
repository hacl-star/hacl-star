module Vale.X64.Leakage_Helpers
open Vale.X64.Machine_Semantics_s
open Vale.X64.Machine_s
open Vale.X64.Leakage_s
open Vale.X64.Instruction_s

let merge_taint (t1:taint) (t2:taint) :taint =
  if Secret? t1 || Secret? t2 then Secret
  else Public

// Also pass the taint of the instruction
let operand_taint (rf:reg_file_id) (o:operand_rf rf) (ts:analysis_taints) : taint =
  match o with
  | OConst _ -> Public
  | OReg r -> ts.regTaint (Reg rf r)
  | OMem (_, t) | OStack (_, t) -> t

[@instr_attr]
let operand_taint_explicit
  (i:instr_operand_explicit)
  (o:instr_operand_t i)
  (ts:analysis_taints)
  : taint =
  match i with
  | IOp64 -> operand_taint 0 (o <: operand64) ts
  | IOpXmm -> operand_taint 1 (o <: operand128) ts

[@instr_attr]
let operand_taint_implicit
  (i:instr_operand_implicit)
  (ts:analysis_taints)
  : taint =
  match i with
  | IOp64One o -> operand_taint 0 o ts
  | IOpXmmOne o -> operand_taint 1 o ts
  | IOpFlagsCf -> ts.cfFlagsTaint
  | IOpFlagsOf -> ts.ofFlagsTaint

[@instr_attr]
let rec args_taint
  (args:list instr_operand)
  (oprs:instr_operands_t_args args)
  (ts:analysis_taints)
  : taint =
  match args with
  | [] -> Public
  | i::args ->
    match i with
    | IOpEx i ->
      let oprs = coerce oprs in merge_taint
      (operand_taint_explicit i (fst oprs) ts)
      (args_taint args (snd oprs) ts)
    | IOpIm i ->
      merge_taint
      (operand_taint_implicit i ts)
      (args_taint args (coerce oprs) ts)

[@instr_attr]
let rec inouts_taint
  (inouts:list instr_out)
  (args:list instr_operand)
  (oprs:instr_operands_t inouts args)
  (ts:analysis_taints)
  : taint =
  match inouts with
  | [] -> args_taint args oprs ts
  | (Out, i)::inouts ->
    let oprs =
      match i with
      | IOpEx i -> snd #(instr_operand_t i) (coerce oprs)
      | IOpIm i -> coerce oprs
    in inouts_taint inouts args oprs ts
  | (InOut, i)::inouts ->
    let (v, oprs) =
      match i with
      | IOpEx i ->
        let oprs = coerce oprs in
        ((operand_taint_explicit i (fst oprs) ts), snd oprs)
      | IOpIm i -> (operand_taint_implicit i ts, coerce oprs)
    in merge_taint v (inouts_taint inouts args oprs ts)

let maddr_does_not_use_secrets (addr:maddr) (ts:analysis_taints) : bool =
  match addr with
  | MConst _ -> true
  | MReg r _ -> Public? (ts.regTaint r)
  | MIndex base _ index _ ->
      let baseTaint = ts.regTaint base in
      let indexTaint = ts.regTaint index in
      (Public? baseTaint) && (Public? indexTaint)

let operand_does_not_use_secrets (#tc #tr:eqtype) (o:operand tc tr) (ts:analysis_taints) : bool =
  match o with
  | OConst _ | OReg _ -> true
  | OMem (m, _) | OStack (m, _) -> maddr_does_not_use_secrets m ts

let operand_taint_allowed (#tc #tr:eqtype) (o:operand tc tr) (t_data:taint) : bool =
  match o with
  | OConst _ | OReg _ -> true
  | OMem (_, t_operand) | OStack (_, t_operand) -> t_operand = Secret || t_data = Public

let set_taint (rf:reg_file_id) (dst:operand_rf rf) (ts:analysis_taints) (t:taint) : analysis_taints =
  match dst with
  | OConst _ -> ts  // Shouldn't actually happen
  | OReg r -> AnalysisTaints
      (FunctionalExtensionality.on reg (fun x -> if x = Reg rf r then t else ts.regTaint x))
      ts.flagsTaint ts.cfFlagsTaint ts.ofFlagsTaint
  | OMem _ | OStack _ -> ts // Ensured by taint semantics

let set_taint_cf_and_flags (ts:analysis_taints) (t:taint) : analysis_taints =
  let AnalysisTaints rs flags cf ovf = ts in
  AnalysisTaints rs (merge_taint t flags) t ovf

let set_taint_of_and_flags (ts:analysis_taints) (t:taint) : analysis_taints =
  let AnalysisTaints rs flags cf ovf = ts in
  AnalysisTaints rs (merge_taint t flags) cf t

let ins_consumes_fixed_time (ins:ins) (ts:analysis_taints) (res:bool & analysis_taints) =
  let (b, ts') = res in
  (b2t b ==> isConstantTime (Ins ins) ts)

#set-options "--z3rlimit 20"

let publicFlagValuesAreAsExpected (tsAnalysis:analysis_taints) (tsExpected:analysis_taints) : bool =
  (tsExpected.flagsTaint = Public && tsAnalysis.flagsTaint = Public) || (tsExpected.flagsTaint = Secret)

let publicCfFlagValuesAreAsExpected (tsAnalysis:analysis_taints) (tsExpected:analysis_taints) : bool =
  (tsExpected.cfFlagsTaint = Public && tsAnalysis.cfFlagsTaint = Public) || (tsExpected.cfFlagsTaint = Secret)

let publicOfFlagValuesAreAsExpected (tsAnalysis:analysis_taints) (tsExpected:analysis_taints) : bool =
  (tsExpected.ofFlagsTaint = Public && tsAnalysis.ofFlagsTaint = Public) || (tsExpected.ofFlagsTaint = Secret)

let registerAsExpected (r:reg) (tsAnalysis:analysis_taints) (tsExpected:analysis_taints) : bool =
  (tsExpected.regTaint r = Public && tsAnalysis.regTaint r = Public) || (tsExpected.regTaint r = Secret)

let rec publicRegisterValuesAreAsExpected_reg_file
    (tsAnalysis:analysis_taints) (tsExpected:analysis_taints) (rf:reg_file_id) (k:nat{k <= n_regs rf})
  : bool =
  if k = 0 then true
  else
    registerAsExpected (Reg rf (k - 1)) tsAnalysis tsExpected &&
    publicRegisterValuesAreAsExpected_reg_file tsAnalysis tsExpected rf (k - 1)

let rec publicRegisterValuesAreAsExpected_regs
    (tsAnalysis:analysis_taints) (tsExpected:analysis_taints) (k:nat{k <= n_reg_files})
  : bool =
  if k = 0 then true
  else
    publicRegisterValuesAreAsExpected_reg_file tsAnalysis tsExpected (k - 1) (n_regs (k - 1)) &&
    publicRegisterValuesAreAsExpected_regs tsAnalysis tsExpected (k - 1)

let publicRegisterValuesAreAsExpected (tsAnalysis:analysis_taints) (tsExpected:analysis_taints) : bool =
  publicRegisterValuesAreAsExpected_regs tsAnalysis tsExpected n_reg_files

// REVIEW: move to specs directory?
let publicTaintsAreAsExpected (tsAnalysis:analysis_taints) (tsExpected:analysis_taints) : bool =
  publicFlagValuesAreAsExpected tsAnalysis tsExpected &&
  publicCfFlagValuesAreAsExpected tsAnalysis tsExpected &&
  publicOfFlagValuesAreAsExpected tsAnalysis tsExpected &&
  publicRegisterValuesAreAsExpected tsAnalysis tsExpected
