module X64.Leakage_Helpers
open X64.Bytes_Semantics_s
open X64.Machine_s
open X64.Taint_Semantics_s
open X64.Leakage_s
open X64.Instruction_s

let merge_taint (t1:taint) (t2:taint) :taint =
  if Secret? t1 || Secret? t2 then Secret
  else Public

(* Also pass the taint of the instruction *)
let operand_taint (op:operand) ts taint =
  match op with
    | OConst _ -> Public
    | OReg reg -> ts.regTaint reg
    | OMem _ -> taint
    // TODO: This should be Public
    | OStack _ -> Secret

let operand_taint128 (op:mov128_op) (ts:taintState) (t:taint) : taint =
  match op with
  | Mov128Xmm x -> ts.xmmTaint x
  | Mov128Mem _ -> t
  // TODO: This should be Public
  | Mov128Stack _ -> Secret

[@instr_attr]
let operand_taint_explicit
  (i:instr_operand_explicit)
  (o:instr_operand_t i)
  (ts:taintState)
  (t:taint) : taint =
  match i with
  | IOp64 -> operand_taint o ts t
  | IOpXmm -> operand_taint128 o ts t

[@instr_attr]
let operand_taint_implicit
  (i:instr_operand_implicit)
  (ts:taintState)
  (t:taint) : taint =
  match i with
  | IOp64One o -> operand_taint o ts t
  | IOpXmmOne o -> operand_taint128 o ts t
  | IOpFlagsCf -> ts.cfFlagsTaint
  // TODO: Should be ts.ofFlagsTaint
  | IOpFlagsOf -> Secret

[@instr_attr]
let rec args_taint
  (args:list instr_operand)
  (oprs:instr_operands_t_args args)
  (ts:taintState)
  (t:taint) : taint =
  match args with
  | [] -> Public
  | i::args ->
    match i with
    | IOpEx i -> let oprs = coerce oprs in merge_taint
                (operand_taint_explicit i (fst oprs) ts t)
                (args_taint args (snd oprs) ts t)
    | IOpIm i -> merge_taint
            (operand_taint_implicit i ts t)
            (args_taint args (coerce oprs) ts t)

[@instr_attr]
let rec inouts_taint
  (inouts:list instr_out) 
  (args:list instr_operand)
  (oprs:instr_operands_t inouts args)
  (ts:taintState)
  (t:taint) : taint =
  match inouts with
  | [] -> args_taint args oprs ts t
  | (Out, i)::inouts ->
    let oprs =
      match i with
      | IOpEx i -> snd #(instr_operand_t i) (coerce oprs)
      | IOpIm i -> coerce oprs
    in inouts_taint inouts args oprs ts t
  | (InOut, i)::inouts -> 
    let (v, oprs) =
      match i with
      | IOpEx i -> let oprs = coerce oprs in
              (operand_taint_explicit i (fst oprs) ts t), snd oprs
      | IOpIm i -> operand_taint_implicit i ts t, coerce oprs
    in merge_taint v (inouts_taint inouts args oprs ts t)


let maddr_does_not_use_secrets addr ts =
  match addr with
    | MConst _ -> true
    | MReg r _ -> Public? (operand_taint (OReg r) ts Public)
    | MIndex base _ index _ ->
        let baseTaint = operand_taint (OReg base) ts Public in
        let indexTaint = operand_taint (OReg index) ts Public in
        (Public? baseTaint) && (Public? indexTaint)

let operand_does_not_use_secrets op ts =
  match op with
  | OConst _ | OReg _ -> true 
  | OMem m | OStack m -> maddr_does_not_use_secrets m ts

let operand128_does_not_use_secrets (op:mov128_op) (ts:taintState) : bool =
  match op with
  | Mov128Xmm _ -> true
  | Mov128Mem m | Mov128Stack m -> maddr_does_not_use_secrets m ts

let operand_taint_allowed (o:operand) (t_operand t_data:taint) : bool =
  match o with
  | OConst _ | OReg _ -> true
  | OMem _ | OStack _ -> t_operand = Secret || t_data = Public

let operand128_taint_allowed (o:mov128_op) (t_operand t_data:taint) : bool =
  match o with
  | Mov128Xmm _ -> true
  | Mov128Mem _ | Mov128Stack _ -> t_operand = Secret || t_data = Public

val lemma_operand_obs:  (ts:taintState) ->  (dst:operand) -> (s1 : traceState) -> (s2:traceState) -> Lemma ((operand_does_not_use_secrets dst ts) /\ publicValuesAreSame ts s1 s2 ==> (operand_obs s1 dst) = (operand_obs s2 dst))

#reset-options "--initial_ifuel 2 --max_ifuel 2 --initial_fuel 4 --max_fuel 4 --z3rlimit 20"
let lemma_operand_obs ts dst s1 s2 = match dst with
  | OConst _ | OReg _ -> ()
  | OMem m | OStack m  -> ()
#reset-options "--initial_ifuel 2 --max_ifuel 2 --initial_fuel 4 --max_fuel 4 --z3rlimit 5"

let set_taint (dst:operand) ts taint : Tot taintState =
  match dst with
  | OConst _ -> ts  (* Shouldn't actually happen *)
  | OReg r -> TaintState (FunctionalExtensionality.on reg (fun x -> if x = r then taint else ts.regTaint x)) ts.flagsTaint ts.cfFlagsTaint ts.xmmTaint
  | OMem m | OStack m -> ts (* Ensured by taint semantics *)

let set_taint128 (dst:mov128_op) (ts:taintState) (t:taint) : taintState =
  match dst with
  | Mov128Xmm r -> TaintState ts.regTaint ts.flagsTaint ts.cfFlagsTaint
      (FunctionalExtensionality.on xmm (fun x -> if x = r then t else ts.xmmTaint x))
  | Mov128Mem _ | Mov128Stack _-> ts

let set_taint_cf_and_flags (ts:taintState) (t:taint) : taintState =
  let TaintState rs flags cf xmms = ts in
  TaintState rs (merge_taint t flags) t xmms

let set_taint_of_and_flags (ts:taintState) (t:taint) : taintState =
  let TaintState rs flags cf xmms = ts in
  TaintState rs (merge_taint t flags) cf xmms

let rec operands_do_not_use_secrets ops ts = match ops with
  | [] -> true
  | hd :: tl -> operand_does_not_use_secrets hd ts && (operands_do_not_use_secrets tl ts)

val lemma_operands_imply_op: (ts:taintState) -> (ops:list operand{Cons? ops}) -> Lemma
(requires (operands_do_not_use_secrets ops ts))
(ensures (operand_does_not_use_secrets (List.Tot.Base.hd ops) ts))

let lemma_operands_imply_op ts ops = match ops with
| hd :: tl -> ()

let ins_consumes_fixed_time (ins : tainted_ins) (ts:taintState) (res:bool*taintState) =
  let b, ts' = res in
  ((b2t b) ==> isConstantTime (Ins ins) ts)


(*val lemma_operand_obs_list: (ts:taintState) -> (ops:list operand) -> (s1:traceState) -> (s2:traceState) -> Lemma  ((operands_do_not_use_secrets ops ts /\ publicValuesAreSame ts s1 s2) ==>
  (operand_obs_list s1 ops) == (operand_obs_list s2 ops))

let rec lemma_operand_obs_list ts ops s1 s2 = match ops with
  | [] -> ()
  | hd :: tl -> lemma_operand_obs_list ts tl s1 s2


let rec sources_taint srcs ts taint = match srcs with
  | [] -> taint
  | hd :: tl -> merge_taint (operand_taint hd ts taint) (sources_taint tl ts taint)

let rec set_taints dsts ts taint = match dsts with
  | [] -> ts
  | hd :: tl -> set_taints tl (set_taint hd ts taint) taint

val lemma_taint_sources: (ins:tainted_ins) -> (ts:taintState) -> Lemma
(let i = ins.i in
 let d, s = extract_operands i in
forall src. List.Tot.Base.mem src s /\ Public? (sources_taint s ts ins.t) ==> Public? (operand_taint src ts ins.t))

let lemma_taint_sources ins ts = ()
*)
#set-options "--z3rlimit 20"

val lemma_public_op_are_same:
  (ts:taintState) -> (op:operand) -> (s1:traceState) -> (s2:traceState)
   -> Lemma (requires (operand_does_not_use_secrets op ts   /\
                      Public? (operand_taint op ts Public) /\
		      publicValuesAreSame ts s1 s2         /\
		      taint_match op Public s1.memTaint s1.state /\
		      taint_match op Public s2.memTaint s2.state))
           (ensures eval_operand op s1.state == eval_operand op s2.state)
let lemma_public_op_are_same ts op s1 s2 =
  match op with
  | OConst _ -> ()
  | OReg _ -> ()
  | OMem m ->
    let a1 = eval_maddr m s1.state in
    let a2 = eval_maddr m s2.state in
    assert (a1 == a2);
//    assert (forall a. (a >= a1 /\ a < a1 + 8) ==> s1.state.mem.[a] == s2.state.mem.[a]);
    Opaque_s.reveal_opaque get_heap_val64_def
  | OStack m -> ()

val lemma_public_op_are_same2: 
  (ts:taintState) -> (op:operand) -> (s1:traceState) -> (s2:traceState) -> 
  Lemma (requires operand_does_not_use_secrets op ts /\ 
                  Public? (operand_taint op ts Secret) /\ 
                  publicValuesAreSame ts s1 s2 /\ 
                  taint_match op Public s1.memTaint s1.state /\ 
                  taint_match op Public s2.memTaint s2.state)
        (ensures eval_operand op s1.state == eval_operand op s2.state)

let lemma_public_op_are_same2 ts op s1 s2 = ()

val publicFlagValuesAreAsExpected: (tsAnalysis:taintState) -> (tsExpected:taintState) -> b:bool{b <==> (Public? tsExpected.flagsTaint ==> Public? tsAnalysis.flagsTaint)}

val publicCfFlagValuesAreAsExpected: (tsAnalysis:taintState) -> (tsExpected:taintState) -> b:bool{b <==> (Public? tsExpected.cfFlagsTaint ==> Public? tsAnalysis.cfFlagsTaint)}

val publicRegisterValuesAreAsExpected: (tsAnalysis:taintState) -> (tsExpected:taintState) -> b:bool{b <==> (forall r. (Public? (tsExpected.regTaint r) ==> Public? (tsAnalysis.regTaint r)))}

val publicTaintsAreAsExpected: (tsAnalysis:taintState) -> (tsExpected:taintState) -> b:bool

let publicFlagValuesAreAsExpected (tsAnalysis:taintState) (tsExpected:taintState) =
  (tsExpected.flagsTaint = Public && tsAnalysis.flagsTaint = Public) || (tsExpected.flagsTaint = Secret)

let publicCfFlagValuesAreAsExpected (tsAnalysis:taintState) (tsExpected:taintState) =
  (tsExpected.cfFlagsTaint = Public && tsAnalysis.cfFlagsTaint = Public) || (tsExpected.cfFlagsTaint = Secret)

let registerAsExpected (r:reg) (tsAnalysis:taintState) (tsExpected:taintState) =
  (tsExpected.regTaint r = Public && tsAnalysis.regTaint r = Public) || (tsExpected.regTaint r = Secret)

let publicRegisterValuesAreAsExpected (tsAnalysis:taintState) (tsExpected:taintState) =
  registerAsExpected Rax tsAnalysis tsExpected &&
  registerAsExpected Rbx tsAnalysis tsExpected &&
  registerAsExpected Rcx tsAnalysis tsExpected &&
  registerAsExpected Rdx tsAnalysis tsExpected &&
  registerAsExpected Rsi tsAnalysis tsExpected &&
  registerAsExpected Rdi tsAnalysis tsExpected &&
  registerAsExpected Rbp tsAnalysis tsExpected &&
  registerAsExpected Rsp tsAnalysis tsExpected &&
  registerAsExpected R8 tsAnalysis tsExpected &&
  registerAsExpected R9 tsAnalysis tsExpected &&
  registerAsExpected R10 tsAnalysis tsExpected &&
  registerAsExpected R11 tsAnalysis tsExpected &&
  registerAsExpected R12 tsAnalysis tsExpected &&
  registerAsExpected R13 tsAnalysis tsExpected &&
  registerAsExpected R14 tsAnalysis tsExpected &&
  registerAsExpected R15 tsAnalysis tsExpected

let publicTaintsAreAsExpected (tsAnalysis:taintState) (tsExpected:taintState) =
    publicFlagValuesAreAsExpected tsAnalysis tsExpected
  && publicCfFlagValuesAreAsExpected tsAnalysis tsExpected
&& publicRegisterValuesAreAsExpected tsAnalysis tsExpected
