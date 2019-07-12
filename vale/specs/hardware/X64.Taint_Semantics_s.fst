module X64.Taint_Semantics_s

open FStar.BaseTypes
open FStar.List.Tot.Base

open X64.Machine_s
open X64.Memory_s
open X64.Semantics_s
module S = X64.Bytes_Semantics_s

// syntax for map accesses, m.[key] and m.[key] <- value
let map (key:eqtype) (value:Type) = Map.t key value
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
  | S.Add64 dst src -> [dst], [dst; src]
  | S.AddLea64 dst src1 src2 -> [dst], [dst; src1; src2]
  | S.AddCarry64 dst src -> [dst], [dst; src]
  | S.Adcx64 dst src -> [dst], [dst; src]
  | S.Adox64 dst src -> [dst], [dst; src]
  | S.Sub64 dst src -> [dst], [dst; src]
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
  | S.Pop dst -> [dst], [OMem (MReg Rsp 0)]
  | _ -> [], []

type tainted_ins = |TaintedIns: ops:(ins * list operand * list operand){let i, d, s = ops in (d,s) = extract_operands i}
                                -> t:taint -> tainted_ins

let operand_obs (s:traceState) (o:operand) : list observation =
  match o with
    | OConst _ | OReg _ -> []
    | OMem m -> match m with
      | MConst _ -> []
      | MReg reg _ -> [MemAccess (eval_reg reg s.state)]
      | MIndex base _ index _ -> [MemAccessOffset (eval_reg base s.state) (eval_reg index s.state)]

let rec operand_obs_list (s:traceState) (o:list operand) : list observation =
  match o with
  | [] -> []
  | hd :: tl -> operand_obs s hd @ (operand_obs_list s tl)

let ins_obs (ins:tainted_ins) (s:traceState) : (list observation) =
  let (i, dsts, srcs) = ins.ops in
  (operand_obs_list s dsts @ operand_obs_list s srcs)

(* Checks if the taint of an operand matches the ins annotation *)
let taint_match (o:operand) (t:taint) (memTaint:memTaint_t) (s:state) : bool =
  match o with
    | OConst _ | OReg _ -> true
    | OMem m ->
        let ptr = eval_maddr m s in
        memTaint.[ptr] = t

let rec taint_match_list o t memTaint s : bool = match o with
  | [] -> true
  | hd::tl -> (taint_match hd t memTaint s) && taint_match_list tl t memTaint s

let update_taint (memTaint:memTaint_t) (dst:operand) (t:taint) (s:state) : Tot memTaint_t =
  match dst with
    | OConst _ -> memTaint
    | OReg _ -> memTaint
    | OMem m -> let ptr = eval_maddr m s in
        let mt = memTaint.[ptr] <- t in
        assert (Set.equal (Map.domain mt) (Set.complement Set.empty));
        mt

val update_taint_list: (memTaint:memTaint_t) -> (dst:list operand) -> (t:taint) -> (s:state) -> Tot (memTaint_t) (decreases %[dst])
let rec update_taint_list (memTaint:memTaint_t) (dst:list operand) t s = match dst with
  | [] -> memTaint
  | hd :: tl -> update_taint_list (update_taint memTaint hd t s) tl t s

let taint_match128 op t (memTaint:memTaint_t) (s:state) : bool = match op with
  | Mov128Xmm _ -> true
  | Mov128Mem addr ->
    let ptr = eval_maddr addr s in
    memTaint.[ptr] = t && memTaint.[ptr+8] = t

let update_taint128 op t (memTaint:memTaint_t) (s:state) : Tot memTaint_t = match op with
  | Mov128Xmm _ -> memTaint
  | Mov128Mem addr ->
    let ptr = eval_maddr addr s in
    let mt = memTaint.[ptr] <- t in
    let mt = mt.[ptr+8] <- t in
    assert (Set.equal (Map.domain mt) (Set.complement Set.empty));
    mt

// Special treatment for movdqu
let taint_eval_movdqu
  (ins:tainted_ins{let i, _, _ = ins.ops in S.MOVDQU? i})
  (ts:traceState) : GTot traceState =
  let t = ins.t in
  let S.MOVDQU dst src, _, _ = ins.ops in
  let s = run (check (taint_match128 src t ts.memTaint)) ts.state in
  let memTaint = update_taint128 dst t ts.memTaint s in
  let s = run (eval_ins (S.MOVDQU dst src)) s in
  {state = s; trace = ts.trace; memTaint = memTaint}


let taint_eval_ins (ins:tainted_ins) (ts: traceState) : GTot traceState =
  let t = ins.t in
  let i, dsts, srcs = ins.ops in
  if S.MOVDQU? i then taint_eval_movdqu ins ts else
  begin
  let s = run (check (taint_match_list srcs t ts.memTaint)) ts.state in
  let memTaint =
    if S.Mulx64? i then
    begin
    let S.Mulx64 dst_hi dst_lo src = i in
    let lo = FStar.UInt.mul_mod #64 (eval_reg Rdx s) (eval_operand src s) in
    let s' = update_operand_preserve_flags' dst_lo lo s in
    let memTaint = update_taint ts.memTaint dst_lo t s in
    update_taint memTaint dst_hi t s'
    end
    else
    if S.Push? i then begin
      let S.Push src = i in
      let new_rsp = ((eval_reg Rsp s) - 8) % pow2_64 in
      let mt = ts.memTaint.[new_rsp] <- t in
      assert (Set.equal (Map.domain mt) (Set.complement Set.empty));
      mt
    end else update_taint_list ts.memTaint dsts t s in
  (* Execute the instruction *)
  let s = run (eval_ins i) s in
  {state = s; trace = ts.trace; memTaint = memTaint}
  end

type tainted_ocmp = |TaintedOCmp: o:ocmp -> ot:taint -> tainted_ocmp

let get_fst_ocmp (o:ocmp) = match o with
  | S.OEq o1 _ | S.ONe o1 _ | S.OLe o1 _ | S.OGe o1 _ | S.OLt o1 _ | S.OGt o1 _ -> o1

let get_snd_ocmp (o:ocmp) = match o with
  | S.OEq _ o2 | S.ONe _ o2 | S.OLe _ o2 | S.OGe _ o2 | S.OLt _ o2 | S.OGt _ o2 -> o2

let taint_eval_ocmp (ts:traceState) (c:tainted_ocmp) : GTot (traceState * bool) =
  let t = c.ot in
  let s = run (check (valid_ocmp c.o);; check (taint_match (get_fst_ocmp c.o) t ts.memTaint);; check (taint_match (get_snd_ocmp c.o) t ts.memTaint)) ts.state in
    {ts with state = s}, eval_ocmp s c.o

type tainted_code = precode tainted_ins tainted_ocmp
type tainted_codes = list tainted_code

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
    | Some s1 -> if not (s1.state).X64.Memory_s.state.S.ok then Some s1
      else taint_eval_while c (fuel - 1) s1

(* Used to split the analysis between instructions added for xmm, and other insns *)
let is_xmm_ins (ins:tainted_ins) =
  let i, _, _ = ins.ops in
  match i with
    | S.Paddd _ _ | S.Pxor _ _ | S.Pslld _ _ | S.Psrld _ _ | S.Psrldq _ _ | S.Shufpd _ _ _ | S.Pshufb _ _
    | S.Pshufd _ _ _ | S.Pcmpeqd _ _ | S.Pextrq _ _ _ | S.Pinsrd _ _ _ | S.Pinsrq _ _ _
    | S.VPSLLDQ _ _ _ | S.MOVDQU _ _
    | S.Pclmulqdq _ _ _ | S.AESNI_enc _ _ | S.AESNI_enc_last _ _
    | S.AESNI_dec _ _ | S.AESNI_dec_last _ _ | S.AESNI_imc _ _
    | S.AESNI_keygen_assist _ _ _ -> true
    | _ -> false

