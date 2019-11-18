module Vale.X64.Leakage_Helpers
open FStar.Mul
open Vale.X64.Machine_Semantics_s
open Vale.X64.Machine_s
open Vale.X64.Leakage_s
open Vale.X64.Instruction_s
open Vale.Lib.MapTree

let regmap = map reg taint

let reg_le (r1 r2:reg) : bool =
  let Reg f1 n1 = r1 in
  let Reg f2 n2 = r2 in
  f1 < f2 || (f1 = f2 && n1 <= n2)

let map_to_regs (m:regmap) : reg_taint =
  FunctionalExtensionality.on reg (sel m)

let is_map_of (m:regmap) (rs:reg_taint) =
  FStar.FunctionalExtensionality.feq (map_to_regs m) rs

let rec regs_to_map_rec (rs:reg_taint) (f n:nat) : Pure regmap
  (requires (f == n_reg_files /\ n == 0) \/ (f < n_reg_files /\ n <= n_regs f))
  (ensures (fun m -> forall (r:reg).{:pattern sel m r}
    r.rf < f \/ (r.rf == f /\ r.r < n) ==> sel m r == rs r))
  (decreases %[f; n])
  =
  if n = 0 then
    if f = 0 then const reg taint reg_le Secret
    else regs_to_map_rec rs (f - 1) (n_regs (f - 1))
  else
    let m = regs_to_map_rec rs f (n - 1) in
    let r = Reg f (n - 1) in
    upd m r (rs r)

let regs_to_map (rs:reg_taint) : (m:regmap{is_map_of m rs}) =
  regs_to_map_rec rs n_reg_files 0

noeq type analysis_taints =
  | AnalysisTaints: lts:leakage_taints -> rts:regmap{is_map_of rts lts.regTaint} -> analysis_taints

let merge_taint (t1:taint) (t2:taint) :taint =
  if Secret? t1 || Secret? t2 then Secret
  else Public

// Also pass the taint of the instruction
let operand_taint (rf:reg_file_id) (o:operand_rf rf) (ts:analysis_taints) : taint =
  match o with
  | OConst _ -> Public
  | OReg r -> sel ts.rts (Reg rf r)
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
  | IOpFlagsCf -> ts.lts.cfFlagsTaint
  | IOpFlagsOf -> ts.lts.ofFlagsTaint

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
  | MReg r _ -> Public? (sel ts.rts r)
  | MIndex base _ index _ ->
      let baseTaint = sel ts.rts base in
      let indexTaint = sel ts.rts index in
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
  | OReg r ->
      let AnalysisTaints (LeakageTaints rs f c o) rts = ts in
      let rts = upd rts (Reg rf r) t in
      AnalysisTaints (LeakageTaints (map_to_regs rts) f c o) rts
  | OMem _ | OStack _ -> ts // Ensured by taint semantics

let set_taint_cf_and_flags (ts:analysis_taints) (t:taint) : analysis_taints =
  let AnalysisTaints (LeakageTaints rs flags cf ovf) rts = ts in
  AnalysisTaints (LeakageTaints rs (merge_taint t flags) t ovf) rts

let set_taint_of_and_flags (ts:analysis_taints) (t:taint) : analysis_taints =
  let AnalysisTaints (LeakageTaints rs flags cf ovf) rts = ts in
  AnalysisTaints (LeakageTaints rs (merge_taint t flags) cf t) rts

let ins_consumes_fixed_time (ins:ins) (ts:analysis_taints) (res:bool & analysis_taints) =
  let (b, ts') = res in
  (b2t b ==> isConstantTime (Ins ins) ts.lts)

#set-options "--z3rlimit 20"

let publicFlagValuesAreAsExpected (tsAnalysis:analysis_taints) (tsExpected:analysis_taints) : bool =
  (tsExpected.lts.flagsTaint = Public && tsAnalysis.lts.flagsTaint = Public) || (tsExpected.lts.flagsTaint = Secret)

let publicCfFlagValuesAreAsExpected (tsAnalysis:analysis_taints) (tsExpected:analysis_taints) : bool =
  (tsExpected.lts.cfFlagsTaint = Public && tsAnalysis.lts.cfFlagsTaint = Public) || (tsExpected.lts.cfFlagsTaint = Secret)

let publicOfFlagValuesAreAsExpected (tsAnalysis:analysis_taints) (tsExpected:analysis_taints) : bool =
  (tsExpected.lts.ofFlagsTaint = Public && tsAnalysis.lts.ofFlagsTaint = Public) || (tsExpected.lts.ofFlagsTaint = Secret)

let registerAsExpected (r:reg) (tsAnalysis:analysis_taints) (tsExpected:analysis_taints) : bool =
  (sel tsExpected.rts r = Public && sel tsAnalysis.rts r = Public) || (sel tsExpected.rts r = Secret)

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
