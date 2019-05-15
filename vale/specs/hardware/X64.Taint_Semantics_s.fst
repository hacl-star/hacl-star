module X64.Taint_Semantics_s

open FStar.BaseTypes
open FStar.List.Tot.Base

open X64.Machine_s
open X64.Bytes_Semantics_s
module BC = X64.Bytes_Code_s
module S = X64.Bytes_Semantics_s
open X64.Instruction_s

// syntax for map accesses, m.[key] and m.[key] <- value
type map (key:eqtype) (value:Type) = Map.t key value
unfold let op_String_Access (#a:eqtype) (#b:Type) (x:Map.t a b) (y:a) : Tot b = Map.sel x y
unfold let op_String_Assignment = Map.upd

let operand_obs (s:machine_state) (o:operand) : list observation =
  match o with
  | OConst _ | OReg _ -> []
  | OMem (m, _) | OStack (m, _) ->
    match m with
    | MConst _ -> []
    | MReg reg _ -> [MemAccess (eval_reg reg s)]
    | MIndex base _ index _ -> [MemAccessOffset (eval_reg base s) (eval_reg index s)]

[@instr_attr]
let operand_obs128 (s:machine_state) (op:operand128) : list observation =
  match op with
  | OReg128 _ -> []
  | OStack128 (m, _) | OMem128 (m, _) -> 
    match m with
    | MConst _ -> []
    | MReg reg _ -> [MemAccess (eval_reg reg s)]
    | MIndex base _ index _ -> [MemAccessOffset (eval_reg base s) (eval_reg index s)]

[@instr_attr]
let obs_operand_explicit
  (i:instr_operand_explicit)
  (o:instr_operand_t i)
  (s:machine_state) : list observation =
  match i with
  | IOp64 -> operand_obs s o
  | IOpXmm -> operand_obs128 s o

[@instr_attr]
let obs_operand_implicit
  (i:instr_operand_implicit)
  (s:machine_state) : list observation =
  match i with
  | IOp64One o -> operand_obs s o
  | IOpXmmOne o -> operand_obs128 s o
  | IOpFlagsCf | IOpFlagsOf -> []

[@instr_attr]
let rec obs_args
  (args:list instr_operand)
  (oprs:instr_operands_t_args args)
  (s:machine_state) : list observation =
  match args with
  | [] -> []
  | i::args ->
    match i with
    | IOpEx i -> let oprs = coerce oprs in
                 obs_operand_explicit i (fst oprs) s @
                 obs_args args (snd oprs) s
    | IOpIm i -> obs_operand_implicit i s @
                 obs_args args (coerce oprs) s

[@instr_attr]
let rec obs_inouts 
  (inouts:list instr_out) 
  (args:list instr_operand)
  (oprs:instr_operands_t inouts args)
  (s:machine_state) : list observation =
  match inouts with
  | [] -> obs_args args oprs s
  | (_, i)::inouts -> 
    let (v, oprs) =
      match i with
      | IOpEx i -> let oprs = coerce oprs in
              (obs_operand_explicit i (fst oprs) s), snd oprs
      | IOpIm i -> obs_operand_implicit i s, coerce oprs
    in v @ obs_inouts inouts args oprs s

[@instr_attr]
let ins_obs (ins:ins) (s:machine_state) : list observation =
  match ins with
  | BC.Instr (InstrTypeRecord #outs #args _) oprs _ -> obs_inouts outs args oprs s
  | BC.Push src _ -> operand_obs s src
  | BC.Pop dst _ -> operand_obs s dst
  | BC.Alloc _ | BC.Dealloc _ -> []

[@"opaque_to_smt"]
let rec match_n (addr:int) (n:nat) (memTaint:memTaint_t) (t:taint)
  : Tot (b:bool{b <==> (forall i.{:pattern (memTaint `Map.sel` i)}
                           (i >= addr /\ i < addr + n) ==> memTaint.[i] == t)})
    (decreases n)
  = if n = 0 then true
    else if memTaint.[addr] <> t then false
    else match_n (addr + 1) (n - 1) memTaint t

[@"opaque_to_smt"]
let rec update_n (addr:int) (n:nat) (memTaint:memTaint_t) (t:taint)
  : Tot (m:memTaint_t{(forall i.{:pattern (m `Map.sel` i)}
                           ((i >= addr /\ i < addr + n) ==> m.[i] == t) /\
	                   ((i < addr \/ i >= addr + n) ==> m.[i] == memTaint.[i]))})
    (decreases n)
  = if n = 0 then memTaint
    else update_n (addr + 1) (n - 1) (memTaint.[addr] <- t) t


(*
Check if the taint annotation of a memory operand matches the taint in the memory map.
Evaluation will fail in case of a mismatch.
This allows the taint analysis to learn information about the memory map from the annotation,
assuming that the code has been verified not to fail.
(Note that this only relates to memory maps, so non-memory operands need no annotation.)
*)
[@instr_attr]
let taint_match (o:operand) (memTaint:memTaint_t) (stackTaint:memTaint_t) (s:machine_state) : bool =
  match o with
  | OConst _ | OReg _ -> true
  | OMem (m, t) -> match_n (eval_maddr m s) 8 memTaint t
  | OStack (m, t) -> match_n (eval_maddr m s) 8 stackTaint t 

[@instr_attr]
let taint_match128 (op:operand128) (memTaint:memTaint_t) (stackTaint:memTaint_t) (s:machine_state) : bool =
  match op with
  | OReg128 _ -> true
  | OMem128 (addr, t) -> match_n (eval_maddr addr s) 16 memTaint t
  | OStack128 (addr, t) -> match_n (eval_maddr addr s) 16 stackTaint t

[@instr_attr]
let taint_match_operand_explicit
  (i:instr_operand_explicit)
  (o:instr_operand_t i)
  (memTaint:memTaint_t)
  (stackTaint:memTaint_t)
  (s:machine_state) : bool =
  match i with
  | IOp64 -> taint_match o memTaint stackTaint s
  | IOpXmm -> taint_match128 o memTaint stackTaint s

[@instr_attr]
let taint_match_operand_implicit
  (i:instr_operand_implicit)
  (memTaint:memTaint_t)
  (stackTaint:memTaint_t)
  (s:machine_state) : bool =
  match i with
  | IOp64One o -> taint_match o memTaint stackTaint s
  | IOpXmmOne o -> taint_match128 o memTaint stackTaint s
  | IOpFlagsCf -> true
  | IOpFlagsOf -> true

[@instr_attr]
let rec taint_match_args
  (args:list instr_operand)
  (oprs:instr_operands_t_args args)
  (memTaint:memTaint_t)
  (stackTaint:memTaint_t)
  (s:machine_state)
  : bool =
  match args with
  | [] -> true
  | i::args ->
    match i with
    | IOpEx i ->
      let oprs = coerce oprs in
      taint_match_operand_explicit i (fst oprs) memTaint stackTaint s &&
      taint_match_args args (snd oprs) memTaint stackTaint s
    | IOpIm i ->
      taint_match_operand_implicit i memTaint stackTaint s &&
      taint_match_args args (coerce oprs) memTaint stackTaint s

[@instr_attr]
let rec taint_match_inouts 
  (inouts:list instr_out)
  (args:list instr_operand)
  (oprs:instr_operands_t inouts args)
  (memTaint:memTaint_t)
  (stackTaint:memTaint_t)
  (s:machine_state)
  : bool =
  match inouts with
  | [] -> taint_match_args args oprs memTaint stackTaint s
  | (Out, i)::inouts -> 
    let oprs =
      match i with
      | IOpEx i -> snd #(instr_operand_t i) (coerce oprs)
      | IOpIm i -> coerce oprs
    in taint_match_inouts inouts args oprs memTaint stackTaint s
  | (InOut, i)::inouts -> 
    let (v, oprs) =
      match i with
      | IOpEx i ->
        let oprs = coerce oprs in
        (taint_match_operand_explicit i (fst oprs) memTaint stackTaint s, snd oprs)
      | IOpIm i -> (taint_match_operand_implicit i memTaint stackTaint s, coerce oprs)
    in v && taint_match_inouts inouts args oprs memTaint stackTaint s

[@instr_attr]
let taint_match_ins (ins:ins) (memTaint:memTaint_t) (stackTaint:memTaint_t) (s:machine_state) : bool =
  match ins with
  | BC.Instr (InstrTypeRecord #outs #args _) oprs _ -> taint_match_inouts outs args oprs memTaint stackTaint s
  | BC.Push src _ -> taint_match src memTaint stackTaint s
  | BC.Pop _ t -> taint_match (OStack (MReg rRsp 0, t)) memTaint stackTaint s
  | BC.Alloc _ | BC.Dealloc _ -> true

[@instr_attr]
let update_taint (op:operand) (memTaint:memTaint_t) (stackTaint:memTaint_t) (s:machine_state)
  : memTaint_t & memTaint_t =
  match op with
  | OConst _ | OReg _ -> (memTaint, stackTaint)
  | OMem (m, t) -> (update_n (eval_maddr m s) 8 memTaint t, stackTaint)
  | OStack (m, t) -> (memTaint, update_n (eval_maddr m s) 8 stackTaint t)
    
[@instr_attr]
let update_taint128 (op:operand128) (memTaint:memTaint_t) (stackTaint:memTaint_t) (s:machine_state)
  : memTaint_t & memTaint_t =
  match op with
  | OReg128 _ -> (memTaint, stackTaint)
  | OMem128 (addr, t) -> (update_n (eval_maddr addr s) 16 memTaint t, stackTaint)
  | OStack128 (addr, t) -> (memTaint, update_n (eval_maddr addr s) 16 stackTaint t)

[@instr_attr]
let update_taint_operand_explicit
  (i:instr_operand_explicit)
  (o:instr_operand_t i)
  (memTaint:memTaint_t)
  (stackTaint:memTaint_t)
  (s:machine_state)
  : memTaint_t & memTaint_t =
  match i with
  | IOp64 -> update_taint o memTaint stackTaint s
  | IOpXmm -> update_taint128 o memTaint stackTaint s

[@instr_attr]
let update_taint_operand_implicit
  (i:instr_operand_implicit)
  (memTaint:memTaint_t)
  (stackTaint:memTaint_t)
  (s:machine_state)
  : memTaint_t & memTaint_t =
  match i with
  | IOp64One o -> update_taint o memTaint stackTaint s
  | IOpXmmOne o -> update_taint128 o memTaint stackTaint s
  | IOpFlagsCf -> (memTaint, stackTaint)
  | IOpFlagsOf -> (memTaint, stackTaint)

[@instr_attr]
let rec update_taint_outputs
  (outs:list instr_out) 
  (args:list instr_operand)
  (oprs:instr_operands_t outs args)
  (memTaint:memTaint_t)
  (stackTaint:memTaint_t)  
  (s:machine_state)
  : memTaint_t & memTaint_t =
  match outs with
  | [] -> (memTaint, stackTaint)
  | (_, i)::outs -> 
    let ((memTaint, stackTaint), oprs) =
      match i with
      | IOpEx i ->
        let oprs = coerce oprs in
        (update_taint_operand_explicit i (fst oprs) memTaint stackTaint s, snd oprs)
      | IOpIm i -> (update_taint_operand_implicit i memTaint stackTaint s, coerce oprs)
   in
   update_taint_outputs outs args oprs memTaint stackTaint s

[@instr_attr]
let update_taint_ins (ins:ins) (memTaint:memTaint_t) (stackTaint:memTaint_t) (s:machine_state) : memTaint_t * memTaint_t =
  match ins with
  | BC.Instr (InstrTypeRecord #outs #args _) oprs _ -> update_taint_outputs outs args oprs memTaint stackTaint s
  | BC.Alloc _ | BC.Dealloc _ -> (memTaint, stackTaint)
  | BC.Push _ t -> update_taint (OStack (MReg rRsp (-8), t)) memTaint stackTaint s
  | BC.Pop dst _ -> update_taint dst memTaint stackTaint s

[@instr_attr]
let taint_eval_ins (i:ins) (ts:machine_state) : GTot machine_state =
  let s = run (check (taint_match_ins i ts.ms_memTaint ts.ms_stackTaint)) ts in
  let (memTaint, stackTaint) = update_taint_ins i ts.ms_memTaint ts.ms_stackTaint s in
  let s = run (eval_ins i) s in
  {s with ms_memTaint = memTaint; ms_stackTaint = stackTaint}

let get_fst_ocmp (o:ocmp) = match o with
  | BC.OEq o1 _ | BC.ONe o1 _ | BC.OLe o1 _ | BC.OGe o1 _ | BC.OLt o1 _ | BC.OGt o1 _ -> o1

let get_snd_ocmp (o:ocmp) = match o with
  | BC.OEq _ o2 | BC.ONe _ o2 | BC.OLe _ o2 | BC.OGe _ o2 | BC.OLt _ o2 | BC.OGt _ o2 -> o2

let taint_eval_ocmp (ts:machine_state) (c:ocmp) : GTot (machine_state * bool) =
  let s =
    run (
      check (valid_ocmp c);;
      check (taint_match (get_fst_ocmp c) ts.ms_memTaint ts.ms_stackTaint);;
      check (taint_match (get_snd_ocmp c) ts.ms_memTaint ts.ms_stackTaint))
    ts
    in
  (s, eval_ocmp s c)

val taint_eval_code (c:S.code) (fuel:nat) (s:machine_state) : GTot (option machine_state)
  (decreases %[fuel; c; 1])
val taint_eval_codes (l:S.codes) (fuel:nat) (s:machine_state) : GTot (option machine_state)
  (decreases %[fuel; l])
val taint_eval_while (c:S.code{While? c}) (fuel:nat) (s:machine_state) : GTot (option machine_state)
  (decreases %[fuel; c; 0])

(* Adds the observations to the eval_code.
   Returns None if eval_code returns None *)
let rec taint_eval_code c fuel s =
  match c with
    | Ins ins -> let obs = ins_obs ins s in
      // REVIEW: drop trace, then restore trace, to make clear that taint_eval_ins shouldn't depend on trace
      Some ({taint_eval_ins ins ({s with ms_trace = []}) with ms_trace = obs @ s.ms_trace})

    | Block l -> taint_eval_codes l fuel s

    | IfElse ifCond ifTrue ifFalse ->
      let st, b = taint_eval_ocmp s ifCond in
      (* We add the BranchPredicate to the trace *)
      let s' = {st with ms_trace = BranchPredicate(b)::s.ms_trace} in
      (* We evaluate the branch with the new trace *)
      if b then taint_eval_code ifTrue fuel s' else taint_eval_code ifFalse fuel s'

    | While _ _ -> taint_eval_while c fuel s

and taint_eval_codes l fuel s =
match l with
      | [] -> Some s
      | c::tl ->
        let s_opt = taint_eval_code c fuel s in
        if None? s_opt then None
        (* Recursively evaluate on the tail *)
        else taint_eval_codes
          tl
          fuel
          (Some?.v s_opt)

and taint_eval_while c fuel s0 =
  if fuel = 0 then None else
  let While cond body = c in
  let (s0, b) = taint_eval_ocmp s0 cond in
  if not b then Some ({s0 with ms_trace = BranchPredicate(false)::s0.ms_trace})
  else
    let s0 = {s0 with ms_trace = BranchPredicate(true)::s0.ms_trace} in
    let s_opt = taint_eval_code body (fuel - 1) s0 in
    match s_opt with
    | None -> None
    | Some s1 -> if not s1.ms_ok then Some s1
      else taint_eval_while c (fuel - 1) s1
