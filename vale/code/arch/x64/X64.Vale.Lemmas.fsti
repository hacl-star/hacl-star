module X64.Vale.Lemmas
open X64.Machine_s
open X64.Vale.State
open X64.Vale.StateLemmas
module BS = X64.Bytes_Semantics_s
module TS = X64.Taint_Semantics_s

unfold let code = TS.tainted_code
unfold let codes = TS.tainted_codes
unfold let ocmp = TS.tainted_ocmp
unfold let fuel = nat

let cf (flags:int) : bool = BS.cf (int_to_nat64 flags)
let overflow (flags:int) : bool = BS.overflow (int_to_nat64 flags)
let update_cf (flags:int) (new_cf:bool) = BS.update_cf' (int_to_nat64 flags) new_cf
let update_of (flags:int) (new_of:bool) = BS.update_of' (int_to_nat64 flags) new_of

let state_eq_S (s1 s2:TS.traceState) =
  s1 == {s2 with TS.trace = s1.TS.trace}

let state_eq_opt (s1 s2:option TS.traceState) =
  match (s1, s2) with
  | (Some s1, Some s2) -> state_eq_S s1 s2
  | _ -> s1 == s2

let eval_code (c:code) (s0:state) (f0:fuel) (s1:state) : Type0 =
  state_eq_opt (TS.taint_eval_code c f0 (state_to_S s0)) (Some (state_to_S s1))

let eval_ins (c:code) (s0:state) : Ghost ((sM:state) * (f0:fuel))
  (requires Ins? c)
  (ensures fun (sM, f0) ->
    eval_code c s0 f0 sM
  ) =
  let f0 = 0 in
  let (Some sM) = TS.taint_eval_code c f0 (state_to_S s0) in
  same_domain_eval_ins c f0 (state_to_S s0) s0;
  lemma_to_of_eval_ins c s0;
  (state_of_S s0 sM, f0)

let eval_ocmp (s:state) (c:ocmp) : GTot bool = snd (TS.taint_eval_ocmp (state_to_S s) c)

let valid_ocmp (c:ocmp) (s:state) : GTot bool =
  BS.valid_ocmp c.TS.o (state_to_S s).TS.state

let ensure_valid_ocmp (c:ocmp) (s:state) : GTot state = 
  let ts:TS.traceState = fst (TS.taint_eval_ocmp (state_to_S s) c) in
  state_of_S s ts

val lemma_cmp_eq : s:state -> o1:operand{not (OMem? o1 || OStack? o1)} -> o2:operand{not (OMem? o2 || OStack? o2)} -> t:taint -> Lemma
  (ensures eval_ocmp s (TS.TaintedOCmp (BS.OEq o1 o2) t) <==> eval_operand o1 s == eval_operand o2 s)
  [SMTPat (eval_ocmp s (TS.TaintedOCmp (BS.OEq o1 o2) t))]

val lemma_cmp_ne : s:state -> o1:operand{not (OMem? o1 || OStack? o1)} -> o2:operand{not (OMem? o2 || OStack? o2)} -> t:taint
  -> Lemma
  (ensures eval_ocmp s (TS.TaintedOCmp (BS.ONe o1 o2) t) <==> eval_operand o1 s <> eval_operand o2 s)
  [SMTPat (eval_ocmp s (TS.TaintedOCmp (BS.ONe o1 o2) t))]

val lemma_cmp_le : s:state -> o1:operand{not (OMem? o1 || OStack? o1)} -> o2:operand{not (OMem? o2 || OStack? o2)} -> t:taint
  -> Lemma
  (ensures eval_ocmp s (TS.TaintedOCmp (BS.OLe o1 o2) t) <==> eval_operand o1 s <= eval_operand o2 s)
  [SMTPat (eval_ocmp s (TS.TaintedOCmp (BS.OLe o1 o2) t))]

val lemma_cmp_ge : s:state -> o1:operand{not (OMem? o1 || OStack? o1)} -> o2:operand{not (OMem? o2 || OStack? o2)} -> t:taint
  -> Lemma
  (ensures eval_ocmp s (TS.TaintedOCmp (BS.OGe o1 o2) t) <==> eval_operand o1 s >= eval_operand o2 s)
  [SMTPat (eval_ocmp s (TS.TaintedOCmp (BS.OGe o1 o2) t))]

val lemma_cmp_lt : s:state -> o1:operand{not (OMem? o1 || OStack? o1)} -> o2:operand{not (OMem? o2 || OStack? o2)} -> t:taint
  -> Lemma
  (ensures eval_ocmp s (TS.TaintedOCmp (BS.OLt o1 o2) t) <==> eval_operand o1 s < eval_operand o2 s)
  [SMTPat (eval_ocmp s (TS.TaintedOCmp (BS.OLt o1 o2) t))]

val lemma_cmp_gt : s:state -> o1:operand{not (OMem? o1 || OStack? o1)} -> o2:operand{not (OMem? o2 || OStack? o2)} -> t:taint
  -> Lemma
  (ensures eval_ocmp s (TS.TaintedOCmp (BS.OGt o1 o2) t) <==> eval_operand o1 s > eval_operand o2 s)
  [SMTPat (eval_ocmp s (TS.TaintedOCmp (BS.OGt o1 o2) t))]

val lemma_valid_cmp_eq : s:state -> o1:operand{not (OMem? o1 || OStack? o1)} -> o2:operand{not (OMem? o2 || OStack? o2)} -> t:taint -> Lemma
  (ensures valid_src_operand o1 s /\ valid_src_operand o2 s ==> valid_ocmp (TS.TaintedOCmp (BS.OEq o1 o2) t) s)
  [SMTPat (valid_ocmp (TS.TaintedOCmp (BS.OEq o1 o2) t) s)]

val lemma_valid_cmp_ne : s:state -> o1:operand{not (OMem? o1 || OStack? o1)} -> o2:operand{not (OMem? o2 || OStack? o2)} -> t:taint -> Lemma
  (ensures valid_src_operand o1 s /\ valid_src_operand o2 s ==> valid_ocmp (TS.TaintedOCmp (BS.ONe o1 o2) t) s)
  [SMTPat (valid_ocmp (TS.TaintedOCmp (BS.ONe o1 o2) t) s)]

val lemma_valid_cmp_le : s:state -> o1:operand{not (OMem? o1 || OStack? o1)} -> o2:operand{not (OMem? o2 || OStack? o2)} -> t:taint -> Lemma
  (ensures valid_src_operand o1 s /\ valid_src_operand o2 s ==> valid_ocmp (TS.TaintedOCmp (BS.OLe o1 o2) t) s)
  [SMTPat (valid_ocmp (TS.TaintedOCmp (BS.OLe o1 o2) t) s)]

val lemma_valid_cmp_ge : s:state -> o1:operand{not (OMem? o1 || OStack? o1)} -> o2:operand{not (OMem? o2 || OStack? o2)} -> t:taint -> Lemma
  (ensures valid_src_operand o1 s /\ valid_src_operand o2 s ==> valid_ocmp (TS.TaintedOCmp (BS.OGe o1 o2) t) s)
  [SMTPat (valid_ocmp (TS.TaintedOCmp (BS.OGe o1 o2) t) s)]

val lemma_valid_cmp_lt : s:state -> o1:operand{not (OMem? o1 || OStack? o1)} -> o2:operand{not (OMem? o2 || OStack? o2)} -> t:taint -> Lemma
  (ensures valid_src_operand o1 s /\ valid_src_operand o2 s ==> valid_ocmp (TS.TaintedOCmp (BS.OLt o1 o2) t) s)
  [SMTPat (valid_ocmp (TS.TaintedOCmp (BS.OLt o1 o2) t) s)]

val lemma_valid_cmp_gt : s:state -> o1:operand{not (OMem? o1 || OStack? o1)} -> o2:operand{not (OMem? o2 || OStack? o2)} -> t:taint -> Lemma
  (ensures valid_src_operand o1 s /\ valid_src_operand o2 s ==> valid_ocmp (TS.TaintedOCmp (BS.OGt o1 o2) t) s)
[SMTPat (valid_ocmp (TS.TaintedOCmp (BS.OGt o1 o2) t) s)]

val compute_merge_total (f0:fuel) (fM:fuel) : fuel

val lemma_merge_total (b0:codes) (s0:state) (f0:fuel) (sM:state) (fM:fuel) (sN:state) : Lemma
  (requires
    Cons? b0 /\
    eval_code (Cons?.hd b0) s0 f0 sM /\
    eval_code (Block (Cons?.tl b0)) sM fM sN
  )
  (ensures eval_code (Block b0) s0 (compute_merge_total f0 fM) sN)

val lemma_empty_total (s0:state) (bN:codes) : Ghost ((sM:state) * (fM:fuel))
  (requires True)
  (ensures (fun (sM, fM) ->
    s0 == sM /\
    eval_code (Block []) s0 fM sM
  ))

val lemma_ifElse_total (ifb:ocmp) (ct:code) (cf:code) (s0:state) : Ghost (bool * state * state * fuel)
  (requires True)
  (ensures  (fun (cond, sM, sN, f0) ->
    cond == eval_ocmp s0 ifb /\
    sM == s0
  ))

val lemma_ifElseTrue_total (ifb:ocmp) (ct:code) (cf:code) (s0:state) (f0:fuel) (sM:state) : Lemma
  (requires
    valid_ocmp ifb s0 /\
    eval_ocmp s0 ifb /\
    eval_code ct s0 f0 sM
  )
  (ensures
    eval_code (IfElse ifb ct cf) s0 f0 sM
  )

val lemma_ifElseFalse_total (ifb:ocmp) (ct:code) (cf:code) (s0:state) (f0:fuel) (sM:state) : Lemma
  (requires
    valid_ocmp ifb s0 /\
    not (eval_ocmp s0 ifb) /\
    eval_code cf s0 f0 sM
  )
  (ensures
    eval_code (IfElse ifb ct cf) s0 f0 sM
  )

val eval_while_inv (c:code) (s0:state) (fW:fuel) (sW:state) : Type0

val lemma_while_total (b:ocmp) (c:code) (s0:state) : Ghost ((s1:state) * (f1:fuel))
  (requires True)
  (ensures fun (s1, f1) ->
    s1 == s0 /\
    eval_while_inv (While b c) s1 f1 s1
  )

val lemma_whileTrue_total (b:ocmp) (c:code) (s0:state) (sW:state) (fW:fuel) : Ghost ((s1:state) * (f1:fuel))
  (requires eval_ocmp sW b)
  (ensures fun (s1, f1) -> s1 == sW /\ f1 == fW)

val lemma_whileFalse_total (b:ocmp) (c:code) (s0:state) (sW:state) (fW:fuel) : Ghost ((s1:state) * (f1:fuel))
  (requires
    valid_ocmp b sW /\
    not (eval_ocmp sW b) /\
    eval_while_inv (While b c) s0 fW sW
  )
  (ensures fun (s1, f1) ->
    s1 == sW /\
    eval_code (While b c) s0 f1 s1
  )

val lemma_whileMerge_total (c:code) (s0:state) (f0:fuel) (sM:state) (fM:fuel) (sN:state) : Ghost (fN:fuel)
  (requires
    While? c /\
    sN.ok /\
    valid_ocmp (While?.whileCond c) sM /\
    eval_ocmp sM (While?.whileCond c) /\
    eval_while_inv c s0 f0 sM /\
    eval_code (While?.whileBody c) sM fM sN
  )
  (ensures (fun fN ->
    eval_while_inv c s0 fN sN
  ))
