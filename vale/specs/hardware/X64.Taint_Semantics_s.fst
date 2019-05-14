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

noeq
type tainted_ins =
  | TaintedIns: i:ins -> t:taint -> tainted_ins

let operand_obs (s:machine_state) (o:operand) : list observation =
  match o with
    | OConst _ | OReg _ -> []
    | OMem m | OStack m ->
      match m with
      | MConst _ -> []
      | MReg reg _ -> [MemAccess (eval_reg reg s)]
      | MIndex base _ index _ -> [MemAccessOffset (eval_reg base s) (eval_reg index s)]

[@instr_attr]
let operand_obs128 (s:machine_state) (op:mov128_op) : list observation =
  match op with
  | Mov128Xmm _ -> []
  | Mov128Stack m | Mov128Mem m -> 
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
  | BC.Push src -> operand_obs s src
  | BC.Pop dst -> operand_obs s dst
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


(* Checks if the taint of an operand matches the ins annotation *)
[@instr_attr]
let taint_match (o:operand) (t:taint) (memTaint:memTaint_t) (ms_stackTaint:memTaint_t) (s:machine_state) : bool =
  match o with
    | OConst _ | OReg _ -> true
    | OMem m -> match_n (eval_maddr m s) 8 memTaint t
    | OStack m -> match_n (eval_maddr m s) 8 ms_stackTaint t 

[@instr_attr]
let taint_match128 (op:mov128_op) (t:taint) (memTaint:memTaint_t) (ms_stackTaint:memTaint_t) (s:machine_state) : bool =
  match op with
  | Mov128Xmm _ -> true
  | Mov128Stack addr -> match_n (eval_maddr addr s) 16 ms_stackTaint t
  | Mov128Mem addr -> match_n (eval_maddr addr s) 16 memTaint t

[@instr_attr]
let taint_match_operand_explicit
  (i:instr_operand_explicit)
  (o:instr_operand_t i)
  (t:taint)
  (memTaint:memTaint_t)
  (ms_stackTaint:memTaint_t)
  (s:machine_state) : bool =
  match i with
  | IOp64 -> taint_match o t memTaint ms_stackTaint s
  | IOpXmm -> taint_match128 o t memTaint ms_stackTaint s

[@instr_attr]
let taint_match_operand_implicit
  (i:instr_operand_implicit)
  (t:taint)
  (memTaint:memTaint_t)
  (ms_stackTaint:memTaint_t)
  (s:machine_state) : bool =
  match i with
  | IOp64One o -> taint_match o t memTaint ms_stackTaint s
  | IOpXmmOne o -> taint_match128 o t memTaint ms_stackTaint s
  // We only check for memory operands in trusted semantics. Taint tracking for other operands will occur in the verified taint analysis
  | IOpFlagsCf -> true
  | IOpFlagsOf -> true

[@instr_attr]
let rec taint_match_args
  (args:list instr_operand)
  (oprs:instr_operands_t_args args)
  (t:taint)
  (memTaint:memTaint_t)
  (ms_stackTaint:memTaint_t)
  (s:machine_state) : bool =
  match args with
  | [] -> true
  | i::args ->
    match i with
    | IOpEx i -> let oprs = coerce oprs in
                taint_match_operand_explicit i (fst oprs) t memTaint ms_stackTaint s &&
                 taint_match_args args (snd oprs) t memTaint ms_stackTaint s
    | IOpIm i -> taint_match_operand_implicit i t memTaint ms_stackTaint s &&
                 taint_match_args args (coerce oprs) t memTaint ms_stackTaint s

[@instr_attr]
let rec taint_match_inouts 
  (inouts:list instr_out) 
  (args:list instr_operand)
  (oprs:instr_operands_t inouts args)
  (t:taint)
  (memTaint:memTaint_t)
  (ms_stackTaint:memTaint_t)
  (s:machine_state) : bool =
  match inouts with
  | [] -> taint_match_args args oprs t memTaint ms_stackTaint s
  | (Out, i)::inouts -> 
    let oprs =
      match i with
      | IOpEx i -> snd #(instr_operand_t i) (coerce oprs)
      | IOpIm i -> coerce oprs
    in taint_match_inouts inouts args oprs t memTaint ms_stackTaint s
  | (InOut, i)::inouts -> 
    let (v, oprs) =
      match i with
      | IOpEx i -> let oprs = coerce oprs in
              (taint_match_operand_explicit i (fst oprs) t memTaint ms_stackTaint s), snd oprs
      | IOpIm i -> taint_match_operand_implicit i t memTaint ms_stackTaint s, coerce oprs
    in v && taint_match_inouts inouts args oprs t memTaint ms_stackTaint s

[@instr_attr]
let taint_match_ins (ins:ins) (t:taint) (memTaint:memTaint_t) (ms_stackTaint:memTaint_t) (s:machine_state) : bool =
  match ins with
  | BC.Instr (InstrTypeRecord #outs #args _) oprs _ -> taint_match_inouts outs args oprs t memTaint ms_stackTaint s
  | BC.Push src -> taint_match src t memTaint ms_stackTaint s
  | BC.Pop _ -> taint_match (OStack (MReg rRsp 0)) t memTaint ms_stackTaint s
  | BC.Alloc _ | BC.Dealloc _ -> true

[@instr_attr]
let update_taint (memTaint:memTaint_t) (ms_stackTaint:memTaint_t) (dst:operand) (t:taint) (s:machine_state) : memTaint_t * memTaint_t =
  match dst with
    | OConst _ | OReg _ -> memTaint, ms_stackTaint
    | OMem m -> update_n (eval_maddr m s) 8 memTaint t, ms_stackTaint
    | OStack m -> memTaint, update_n (eval_maddr m s) 8 ms_stackTaint t
    
[@instr_attr]
let update_taint128 op t (memTaint:memTaint_t) (ms_stackTaint:memTaint_t) (s:machine_state) : memTaint_t * memTaint_t =
  match op with
  | Mov128Xmm _ -> memTaint, ms_stackTaint
  | Mov128Mem addr -> update_n (eval_maddr addr s) 16 memTaint t, ms_stackTaint
  | Mov128Stack addr -> memTaint, update_n (eval_maddr addr s) 16 ms_stackTaint t

[@instr_attr]
let update_taint_operand_explicit
  (i:instr_operand_explicit)
  (o:instr_operand_t i)
  (t:taint)
  (memTaint:memTaint_t)
  (ms_stackTaint:memTaint_t)
  (s:machine_state) : memTaint_t * memTaint_t =
  match i with
  | IOp64 -> update_taint memTaint ms_stackTaint o t s
  | IOpXmm -> update_taint128 o t memTaint ms_stackTaint s

[@instr_attr]
let update_taint_operand_implicit
  (i:instr_operand_implicit)
  (t:taint)
  (memTaint:memTaint_t)
  (ms_stackTaint:memTaint_t)
  (s:machine_state) : memTaint_t * memTaint_t =
  match i with
  | IOp64One o -> update_taint memTaint ms_stackTaint o t s
  | IOpXmmOne o -> update_taint128 o t memTaint ms_stackTaint s
  // We only check for memory operands in trusted semantics. Taint tracking for other operands will occur in the verified taint analysis
  | IOpFlagsCf -> memTaint, ms_stackTaint
  | IOpFlagsOf -> memTaint, ms_stackTaint

[@instr_attr]
let rec update_taint_outputs
  (outs:list instr_out) 
  (args:list instr_operand)
  (oprs:instr_operands_t outs args)
  (t:taint)
  (memTaint:memTaint_t)
  (ms_stackTaint:memTaint_t)  
  (s:machine_state) : memTaint_t * memTaint_t =
  match outs with
  | [] -> memTaint, ms_stackTaint
  | (_, i)::outs -> 
    let (memTaint, ms_stackTaint), oprs =
      match i with
      | IOpEx i -> let oprs = coerce oprs in
          update_taint_operand_explicit i (fst oprs) t memTaint ms_stackTaint s, snd oprs
      | IOpIm i -> update_taint_operand_implicit i t memTaint ms_stackTaint s, coerce oprs
   in
   update_taint_outputs outs args oprs t memTaint ms_stackTaint s

[@instr_attr]
let update_taint_ins (ins:ins) (t:taint) (memTaint:memTaint_t) (ms_stackTaint:memTaint_t) (s:machine_state) : memTaint_t * memTaint_t =
  match ins with
  | BC.Instr (InstrTypeRecord #outs #args _) oprs _ -> update_taint_outputs outs args oprs t memTaint ms_stackTaint s
  | BC.Alloc _ | BC.Dealloc _ -> memTaint, ms_stackTaint
  | BC.Push _ -> update_taint memTaint ms_stackTaint (OStack (MReg rRsp (-8))) t s
  | BC.Pop dst -> update_taint memTaint ms_stackTaint dst t s

[@instr_attr]
let taint_eval_ins (ins:tainted_ins) (ts: machine_state) : GTot machine_state =
  let t = ins.t in
  let i = ins.i in
  let s = run (check (taint_match_ins i t ts.ms_memTaint ts.ms_stackTaint)) ts in
  let (memTaint, ms_stackTaint) = update_taint_ins i t ts.ms_memTaint ts.ms_stackTaint s in
  let s = run (eval_ins i) s in
  {s with ms_memTaint = memTaint; ms_stackTaint = ms_stackTaint}

type tainted_ocmp : eqtype = | TaintedOCmp: o:ocmp -> ot:taint -> tainted_ocmp

let get_fst_ocmp (o:ocmp) = match o with
  | BC.OEq o1 _ | BC.ONe o1 _ | BC.OLe o1 _ | BC.OGe o1 _ | BC.OLt o1 _ | BC.OGt o1 _ -> o1

let get_snd_ocmp (o:ocmp) = match o with
  | BC.OEq _ o2 | BC.ONe _ o2 | BC.OLe _ o2 | BC.OGe _ o2 | BC.OLt _ o2 | BC.OGt _ o2 -> o2

let taint_eval_ocmp (ts:machine_state) (c:tainted_ocmp) : GTot (machine_state * bool) =
  let t = c.ot in
  let s =
    run (
      check (valid_ocmp c.o);; 
      check (taint_match (get_fst_ocmp c.o) t ts.ms_memTaint ts.ms_stackTaint);;
      check (taint_match (get_snd_ocmp c.o) t ts.ms_memTaint ts.ms_stackTaint))
    ts
    in
  (s, eval_ocmp s c.o)

type tainted_code = precode tainted_ins tainted_ocmp
type tainted_codes = list tainted_code

val taint_eval_code (c:tainted_code) (fuel:nat) (s:machine_state) : GTot (option machine_state)
  (decreases %[fuel; c; 1])
val taint_eval_codes (l:tainted_codes) (fuel:nat) (s:machine_state) : GTot (option machine_state)
  (decreases %[fuel; l])
val taint_eval_while (c:tainted_code{While? c}) (fuel:nat) (s:machine_state) : GTot (option machine_state)
  (decreases %[fuel; c; 0])

(* Adds the observations to the eval_code.
   Returns None if eval_code returns None *)
let rec taint_eval_code c fuel s =
  match c with
    | Ins ins -> let obs = ins_obs ins.i s in
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
