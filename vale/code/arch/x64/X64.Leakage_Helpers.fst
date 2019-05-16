module X64.Leakage_Helpers
open X64.Bytes_Semantics_s
open X64.Machine_s
open X64.Leakage_s
open X64.Instruction_s

let merge_taint (t1:taint) (t2:taint) :taint =
  if Secret? t1 || Secret? t2 then Secret
  else Public

(* Also pass the taint of the instruction *)
let operand_taint (op:operand) (ts:analysis_taints) =
  match op with
  | OConst _ -> Public
  | OReg reg -> ts.regTaint reg
  | OMem (_, t) | OStack (_, t) -> t

let operand_taint128 (op:operand128) (ts:analysis_taints) : taint =
  match op with
  | OReg128 x -> ts.xmmTaint x
  | OMem128 (_, t) | OStack128 (_, t) -> t

[@instr_attr]
let operand_taint_explicit
  (i:instr_operand_explicit)
  (o:instr_operand_t i)
  (ts:analysis_taints)
  : taint =
  match i with
  | IOp64 -> operand_taint o ts
  | IOpXmm -> operand_taint128 o ts

[@instr_attr]
let operand_taint_implicit
  (i:instr_operand_implicit)
  (ts:analysis_taints)
  : taint =
  match i with
  | IOp64One o -> operand_taint o ts
  | IOpXmmOne o -> operand_taint128 o ts
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
  | MReg r _ -> Public? (operand_taint (OReg r) ts)
  | MIndex base _ index _ ->
      let baseTaint = operand_taint (OReg base) ts in
      let indexTaint = operand_taint (OReg index) ts in
      (Public? baseTaint) && (Public? indexTaint)

let operand_does_not_use_secrets (op:operand) (ts:analysis_taints) : bool =
  match op with
  | OConst _ | OReg _ -> true 
  | OMem (m, _) | OStack (m, _) -> maddr_does_not_use_secrets m ts

let operand128_does_not_use_secrets (op:operand128) (ts:analysis_taints) : bool =
  match op with
  | OReg128 _ -> true
  | OMem128 (m, _) | OStack128 (m, _) -> maddr_does_not_use_secrets m ts

let operand_taint_allowed (o:operand) (t_data:taint) : bool =
  match o with
  | OConst _ | OReg _ -> true
  | OMem (_, t_operand) | OStack (_, t_operand) -> t_operand = Secret || t_data = Public

let operand128_taint_allowed (o:operand128) (t_data:taint) : bool =
  match o with
  | OReg128 _ -> true
  | OMem128 (_, t_operand) | OStack128 (_, t_operand) -> t_operand = Secret || t_data = Public

let set_taint (dst:operand) (ts:analysis_taints) (t:taint) : analysis_taints =
  match dst with
  | OConst _ -> ts  // Shouldn't actually happen
  | OReg r -> AnalysisTaints (FunctionalExtensionality.on reg
      (fun x -> if x = r then t else ts.regTaint x)) ts.flagsTaint ts.cfFlagsTaint ts.ofFlagsTaint ts.xmmTaint
  | OMem _ | OStack _ -> ts (* Ensured by taint semantics *)

let set_taint128 (dst:operand128) (ts:analysis_taints) (t:taint) : analysis_taints =
  match dst with
  | OReg128 r -> AnalysisTaints ts.regTaint ts.flagsTaint ts.cfFlagsTaint ts.ofFlagsTaint
      (FunctionalExtensionality.on xmm (fun x -> if x = r then t else ts.xmmTaint x))
  | OMem128 _ | OStack128 _-> ts

let set_taint_cf_and_flags (ts:analysis_taints) (t:taint) : analysis_taints =
  let AnalysisTaints rs flags cf ovf xmms = ts in
  AnalysisTaints rs (merge_taint t flags) t ovf xmms

let set_taint_of_and_flags (ts:analysis_taints) (t:taint) : analysis_taints =
  let AnalysisTaints rs flags cf ovf xmms = ts in
  AnalysisTaints rs (merge_taint t flags) cf t xmms

let rec operands_do_not_use_secrets ops ts = match ops with
  | [] -> true
  | hd :: tl -> operand_does_not_use_secrets hd ts && (operands_do_not_use_secrets tl ts)

let ins_consumes_fixed_time (ins : ins) (ts:analysis_taints) (res:bool*analysis_taints) =
  let b, ts' = res in
  ((b2t b) ==> isConstantTime (Ins ins) ts)

#set-options "--z3rlimit 20"

val publicFlagValuesAreAsExpected: (tsAnalysis:analysis_taints) -> (tsExpected:analysis_taints) -> b:bool{b <==> (Public? tsExpected.flagsTaint ==> Public? tsAnalysis.flagsTaint)}

val publicCfFlagValuesAreAsExpected: (tsAnalysis:analysis_taints) -> (tsExpected:analysis_taints) -> b:bool{b <==> (Public? tsExpected.cfFlagsTaint ==> Public? tsAnalysis.cfFlagsTaint)}

val publicOfFlagValuesAreAsExpected: (tsAnalysis:analysis_taints) -> (tsExpected:analysis_taints) -> b:bool{b <==> (Public? tsExpected.ofFlagsTaint ==> Public? tsAnalysis.ofFlagsTaint)}

val publicRegisterValuesAreAsExpected: (tsAnalysis:analysis_taints) -> (tsExpected:analysis_taints) -> b:bool{b <==> (forall r. (Public? (tsExpected.regTaint r) ==> Public? (tsAnalysis.regTaint r)))}

val publicTaintsAreAsExpected: (tsAnalysis:analysis_taints) -> (tsExpected:analysis_taints) -> b:bool

let publicFlagValuesAreAsExpected (tsAnalysis:analysis_taints) (tsExpected:analysis_taints) =
  (tsExpected.flagsTaint = Public && tsAnalysis.flagsTaint = Public) || (tsExpected.flagsTaint = Secret)

let publicCfFlagValuesAreAsExpected (tsAnalysis:analysis_taints) (tsExpected:analysis_taints) =
  (tsExpected.cfFlagsTaint = Public && tsAnalysis.cfFlagsTaint = Public) || (tsExpected.cfFlagsTaint = Secret)

let publicOfFlagValuesAreAsExpected (tsAnalysis:analysis_taints) (tsExpected:analysis_taints) =
  (tsExpected.ofFlagsTaint = Public && tsAnalysis.ofFlagsTaint = Public) || (tsExpected.ofFlagsTaint = Secret)

let registerAsExpected (r:reg) (tsAnalysis:analysis_taints) (tsExpected:analysis_taints) =
  (tsExpected.regTaint r = Public && tsAnalysis.regTaint r = Public) || (tsExpected.regTaint r = Secret)

let publicRegisterValuesAreAsExpected (tsAnalysis:analysis_taints) (tsExpected:analysis_taints) =
  registerAsExpected rRax tsAnalysis tsExpected &&
  registerAsExpected rRbx tsAnalysis tsExpected &&
  registerAsExpected rRcx tsAnalysis tsExpected &&
  registerAsExpected rRdx tsAnalysis tsExpected &&
  registerAsExpected rRsi tsAnalysis tsExpected &&
  registerAsExpected rRdi tsAnalysis tsExpected &&
  registerAsExpected rRbp tsAnalysis tsExpected &&
  registerAsExpected rRsp tsAnalysis tsExpected &&
  registerAsExpected rR8 tsAnalysis tsExpected &&
  registerAsExpected rR9 tsAnalysis tsExpected &&
  registerAsExpected rR10 tsAnalysis tsExpected &&
  registerAsExpected rR11 tsAnalysis tsExpected &&
  registerAsExpected rR12 tsAnalysis tsExpected &&
  registerAsExpected rR13 tsAnalysis tsExpected &&
  registerAsExpected rR14 tsAnalysis tsExpected &&
  registerAsExpected rR15 tsAnalysis tsExpected

let publicTaintsAreAsExpected (tsAnalysis:analysis_taints) (tsExpected:analysis_taints) =
    publicFlagValuesAreAsExpected tsAnalysis tsExpected
  && publicCfFlagValuesAreAsExpected tsAnalysis tsExpected
  && publicOfFlagValuesAreAsExpected tsAnalysis tsExpected
&& publicRegisterValuesAreAsExpected tsAnalysis tsExpected
