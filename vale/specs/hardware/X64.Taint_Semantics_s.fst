module X64.Taint_Semantics_s

open FStar.BaseTypes
open FStar.List.Tot.Base

open X64.Machine_s
open X64.Bytes_Semantics_s
module S = X64.Bytes_Semantics_s

// syntax for map accesses, m.[key] and m.[key] <- value
type map (key:eqtype) (value:Type) = Map.t key value
unfold let op_String_Access (#a:eqtype) (#b:Type) (x:Map.t a b) (y:a) : Tot b = Map.sel x y
unfold let op_String_Assignment = Map.upd

noeq type traceState = {
  state: state;
  trace: list observation;
  memTaint: memTaint_t;
}

// Extract a list of destinations written to and a list of sources read from
let extract_operands (i:ins) : (list operand * list operand) =
  match i with
  | S.Mov64 dst src -> [dst], [src]
  | S.MovBe64 dst src -> [dst], [src]
  | S.Cmovc64 dst src -> [dst], [src; dst]
  | S.Add64 dst src -> [dst], [dst; src]
  | S.AddLea64 dst src1 src2 -> [dst], [dst; src1; src2]
  | S.AddCarry64 dst src -> [dst], [dst; src]
  | S.Adcx64 dst src -> [dst], [dst; src]
  | S.Adox64 dst src -> [dst], [dst; src]
  | S.Sub64 dst src -> [dst], [dst; src]
  | S.Sbb64 dst src -> [dst], [dst; src]
  | S.Mul64 src -> [OReg Rax; OReg Rdx], [OReg Rax; src]
  | S.Mulx64 dst_hi dst_lo src -> [dst_hi; dst_lo], [OReg Rdx; src]
  | S.IMul64 dst src -> [dst], [dst; src]
  | S.Xor64 dst src -> [dst], [dst; src]
  | S.And64 dst src -> [dst], [dst; src]
  | S.Shr64 dst amt -> [dst], [dst; amt]
  | S.Shl64 dst amt -> [dst], [dst; amt]
  | S.Pinsrd _ src _ | S.Pinsrq _ src _ -> [], [src]
  | S.Pextrq dst _ _ -> [dst], []
  | S.Push src -> [], [src]
  | S.Pop dst -> [dst], [OStack (MReg Rsp 0)]
  | S.Alloc _ | S.Dealloc _ -> [OReg Rsp], [OReg Rsp]
  | _ -> [], []

(*
 * AR: do we need the two lists with ins? Can't we always call extract_operands where we need them?
 *)
type tainted_ins : eqtype = 
  | TaintedIns: i:ins -> t:taint -> tainted_ins

let operand_obs (s:traceState) (o:operand) : list observation =
  match o with
    | OConst _ | OReg _ -> []
    | OMem m | OStack m ->
      match m with
      | MConst _ -> []
      | MReg reg _ -> [MemAccess (eval_reg reg s.state)]
      | MIndex base _ index _ -> [MemAccessOffset (eval_reg base s.state) (eval_reg index s.state)]

let rec operand_obs_list (s:traceState) (o:list operand) : list observation =
  match o with
  | [] -> []
  | hd::tl -> operand_obs s hd @ (operand_obs_list s tl)

let ins_obs (ins:tainted_ins) (s:traceState) : (list observation) =
  let (dsts, srcs) = extract_operands ins.i in
  operand_obs_list s dsts @ operand_obs_list s srcs

[@"opaque_to_smt"]
private let rec match_n (addr:int) (n:nat) (memTaint:memTaint_t) (t:taint)
  : Tot (b:bool{b <==> (forall i.{:pattern (memTaint `Map.sel` i)}
                           (i >= addr /\ i < addr + n) ==> memTaint.[i] == t)})
    (decreases n)
  = if n = 0 then true
    else if memTaint.[addr] <> t then false
    else match_n (addr + 1) (n - 1) memTaint t

[@"opaque_to_smt"]
private let rec update_n (addr:int) (n:nat) (memTaint:memTaint_t) (t:taint)
  : Tot (m:memTaint_t{(forall i.{:pattern (m `Map.sel` i)}
                           ((i >= addr /\ i < addr + n) ==> m.[i] == t) /\
	                   ((i < addr \/ i >= addr + n) ==> m.[i] == memTaint.[i]))})
    (decreases n)
  = if n = 0 then memTaint
    else update_n (addr + 1) (n - 1) (memTaint.[addr] <- t) t


(* Checks if the taint of an operand matches the ins annotation *)
let taint_match (o:operand) (t:taint) (memTaint:memTaint_t) (s:state) : bool =
  match o with
    | OConst _ | OReg _ -> true
    | OMem m -> match_n (eval_maddr m s) 8 memTaint t
    | OStack m -> t = Public // everything on the stack should be public

let rec taint_match_list (o:list operand) (t:taint) (memTaint:memTaint_t) (s:state) : bool =
  match o with
  | [] -> true
  | hd::tl -> (taint_match hd t memTaint s) && taint_match_list tl t memTaint s

let update_taint (memTaint:memTaint_t) (dst:operand) (t:taint) (s:state) : memTaint_t =
  match dst with
    | OConst _ | OReg _ | OStack _ -> memTaint
    | OMem m -> update_n (eval_maddr m s) 8 memTaint t

let rec update_taint_list (memTaint:memTaint_t) (dst:list operand) (t:taint) (s:state)
  : Tot (memTaint_t) (decreases %[dst])
  = match dst with
    | [] -> memTaint
    | hd :: tl -> update_taint_list (update_taint memTaint hd t s) tl t s

let taint_match128 (op:mov128_op) (t:taint) (memTaint:memTaint_t) (s:state) : bool =
  match op with
  | Mov128Xmm _ -> true
  | Mov128Stack _ -> t = Public // Everything on the stack should be public
  | Mov128Mem addr -> match_n (eval_maddr addr s) 16 memTaint t

let update_taint128 op t (memTaint:memTaint_t) (s:state) : memTaint_t =
  match op with
  | Mov128Xmm _ | Mov128Stack _ -> memTaint
  | Mov128Mem addr -> update_n (eval_maddr addr s) 16 memTaint t

// Special treatment for movdqu
let taint_eval_movdqu (ins:tainted_ins{S.MOVDQU? ins.i}) (ts:traceState) : GTot traceState =
  let t = ins.t in
  let S.MOVDQU dst src = ins.i in
  let s = run (check (taint_match128 src t ts.memTaint)) ts.state in
  let memTaint = update_taint128 dst t ts.memTaint s in
  let s = run (eval_ins (S.MOVDQU dst src)) s in
  {state = s; trace = ts.trace; memTaint = memTaint}

let taint_eval_ins (ins:tainted_ins) (ts: traceState) : GTot traceState =
  let t = ins.t in
  let i = ins.i in
  let dsts, srcs = extract_operands i in
  
  if S.MOVDQU? i then taint_eval_movdqu ins ts
  else begin
    let s = run (check (taint_match_list srcs t ts.memTaint)) ts.state in
    let memTaint =
      if S.Mulx64? i then begin
        let S.Mulx64 dst_hi dst_lo src = i in
        let lo = FStar.UInt.mul_mod #64 (eval_reg Rdx s) (eval_operand src s) in
        let s' = update_operand_preserve_flags' dst_lo lo s in
        let memTaint = update_taint ts.memTaint dst_lo t s in
        update_taint memTaint dst_hi t s'
      end
      else update_taint_list ts.memTaint dsts t s
    in
    (* Execute the instruction *)
    let s = run (eval_ins i) s in
    {state = s; trace = ts.trace; memTaint = memTaint}
  end

type tainted_ocmp : eqtype = | TaintedOCmp: o:ocmp -> ot:taint -> tainted_ocmp

let get_fst_ocmp (o:ocmp) = match o with
  | S.OEq o1 _ | S.ONe o1 _ | S.OLe o1 _ | S.OGe o1 _ | S.OLt o1 _ | S.OGt o1 _ -> o1

let get_snd_ocmp (o:ocmp) = match o with
  | S.OEq _ o2 | S.ONe _ o2 | S.OLe _ o2 | S.OGe _ o2 | S.OLt _ o2 | S.OGt _ o2 -> o2

let taint_eval_ocmp (ts:traceState) (c:tainted_ocmp) : GTot (traceState * bool) =
  let t = c.ot in
  let s = run (check (valid_ocmp c.o);; check (taint_match (get_fst_ocmp c.o) t ts.memTaint);; check (taint_match (get_snd_ocmp c.o) t ts.memTaint)) ts.state in
    {ts with state = s}, eval_ocmp s c.o

type tainted_code:eqtype = precode tainted_ins tainted_ocmp
type tainted_codes:eqtype = list tainted_code

val taint_eval_code: c:tainted_code -> fuel:nat -> s:traceState -> GTot (option traceState)
(decreases %[fuel; c; 1])
val taint_eval_codes: l:tainted_codes -> fuel:nat -> s:traceState -> GTot (option traceState)
(decreases %[fuel; l])
val taint_eval_while: c:tainted_code{While? c} -> fuel:nat -> s:traceState -> GTot (option traceState)
(decreases %[fuel; c; 0])

(* Adds the observations to the eval_code.
   Returns None if eval_code returns None *)
let rec taint_eval_code c fuel s =
  match c with
    | Ins ins -> let obs = ins_obs ins s in
      Some ({taint_eval_ins ins s with trace = obs @ s.trace})

    | Block l -> taint_eval_codes l fuel s

    | IfElse ifCond ifTrue ifFalse ->
      let st, b = taint_eval_ocmp s ifCond in
      (* We add the BranchPredicate to the trace *)
      let s' = {st with trace=BranchPredicate(b)::s.trace} in
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
  if not b then Some ({s0 with trace = BranchPredicate(false)::s0.trace})
  else
    let s0 = {s0 with trace = BranchPredicate(true)::s0.trace} in
    let s_opt = taint_eval_code body (fuel - 1) s0 in
    match s_opt with
    | None -> None
    | Some s1 -> if not s1.state.ok then Some s1
      else taint_eval_while c (fuel - 1) s1

(* Used to split the analysis between instructions added for xmm, and other insns *)
let is_xmm_ins (ins:tainted_ins) =
  let i = ins.i in
  match i with
    | S.VPaddd _ _ _ | S.Paddd _ _ | S.Pxor _ _ | S.Pand _ _ | S.VPxor _ _ _ | S.Pslld _ _ | S.Psrld _ _ | S.Psrldq _ _ 
    | S.Palignr _ _ _ | S.VPalignr _ _ _ _ | S.Shufpd _ _ _ | S.VShufpd _ _ _ _ | S.Pshufb _ _ | S.VPshufb _ _ _
    | S.Pshufd _ _ _ | S.Pcmpeqd _ _ | S.Pextrq _ _ _ | S.Pinsrd _ _ _ | S.Pinsrq _ _ _
    | S.VPSLLDQ _ _ _ | S.Vpsrldq _ _ _ | S.MOVDQU _ _
    | S.Pclmulqdq _ _ _ | S.VPclmulqdq _ _ _ _ 
    | S.AESNI_enc _ _ | S.AESNI_enc_last _ _ | S.VAESNI_enc _ _ _ | S.VAESNI_enc_last _ _ _
    | S.AESNI_dec _ _ | S.AESNI_dec_last _ _ | S.AESNI_imc _ _
    | S.AESNI_keygen_assist _ _ _ 
    | S.SHA256_rnds2 _ _ | S.SHA256_msg1 _ _ | S.SHA256_msg2 _ _ -> true
    | _ -> false
