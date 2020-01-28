module Vale.X64.Lemmas
open FStar.Mul
open Vale.Arch.Heap
open Vale.Arch.HeapImpl
open Vale.Arch.HeapLemmas
open Vale.X64.Machine_s
open Vale.X64.State
open Vale.X64.StateLemmas
open Vale.X64.Bytes_Code_s
module BS = Vale.X64.Machine_Semantics_s
module Map16 = Vale.Lib.Map16
unfold let code = BS.code
unfold let codes = BS.codes
unfold let ocmp = BS.ocmp
unfold let fuel = nat

let cf (flags:Flags.t) : Flags.flag_val_t = Flags.sel fCarry flags
let overflow (flags:Flags.t) : Flags.flag_val_t = Flags.sel fOverflow flags
let update_cf (flags:Flags.t) (new_cf:bool) = Flags.upd fCarry (Some new_cf) flags
let update_of (flags:Flags.t) (new_of:bool) = Flags.upd fOverflow (Some new_of) flags

unfold let machine_state = BS.machine_state
unfold let machine_eval_code = BS.machine_eval_code

let rec code_modifies_ghost (c:code) : bool =
  match c with
  | Ins (Instr _ _ (BS.AnnotateGhost _)) -> true
  | Ins _ -> false
  | Block cs -> codes_modifies_ghost cs
  | IfElse _ c1 c2 -> code_modifies_ghost c1 || code_modifies_ghost c2
  | While _ c -> code_modifies_ghost c
and codes_modifies_ghost (cs:codes) : bool =
  match cs with
  | [] -> false
  | c::cs -> code_modifies_ghost c || codes_modifies_ghost cs

let state_eq_S (ignore_ghost:bool) (s1 s2:machine_state) =
  let s1 = {s1 with
    BS.ms_trace = [];
    BS.ms_heap = if ignore_ghost then heap_ignore_ghost_machine s1.BS.ms_heap else s1.BS.ms_heap
  } in
  let s2 = {s2 with
    BS.ms_trace = [];
    BS.ms_heap = if ignore_ghost then heap_ignore_ghost_machine s2.BS.ms_heap else s2.BS.ms_heap;
  } in
  machine_state_eq s1 s2

let state_eq_opt (ignore_ghost:bool) (s1 s2:option BS.machine_state) =
  match (s1, s2) with
  | (Some s1, Some s2) -> state_eq_S ignore_ghost s1 s2
  | _ -> s1 == s2

let eval_code (c:code) (s0:vale_state) (f0:fuel) (s1:vale_state) : Type0 =
  state_eq_opt (code_modifies_ghost c) (machine_eval_code c f0 (state_to_S s0)) (Some (state_to_S s1))

let eval_ins (c:code) (s0:vale_state) : Ghost (vale_state & fuel)
  (requires Ins? c)
  (ensures fun (sM, f0) -> eval_code c s0 f0 sM)
  =
  let f0 = 0 in
  let (Some sM) = machine_eval_code c f0 (state_to_S s0) in
  lemma_to_of sM;
  (state_of_S sM, f0)

let eval_ocmp (s:vale_state) (c:ocmp) : GTot bool = snd (BS.machine_eval_ocmp (state_to_S s) c)

let valid_ocmp (c:ocmp) (s:vale_state) : GTot bool =
  BS.valid_ocmp c (state_to_S s)

let ensure_valid_ocmp (c:ocmp) (s:vale_state) : GTot vale_state =
  let ts:machine_state = fst (BS.machine_eval_ocmp (state_to_S s) c) in
  state_of_S ts

val lemma_cmp_eq (s:vale_state) (o1:operand64{not (OMem? o1 || OStack? o1)}) (o2:operand64{not (OMem? o2 || OStack? o2)}) : Lemma
  (ensures eval_ocmp s (OEq o1 o2) <==> eval_operand o1 s == eval_operand o2 s)
  [SMTPat (eval_ocmp s (OEq o1 o2))]

val lemma_cmp_ne (s:vale_state) (o1:operand64{not (OMem? o1 || OStack? o1)}) (o2:operand64{not (OMem? o2 || OStack? o2)}) : Lemma
  (ensures eval_ocmp s (ONe o1 o2) <==> eval_operand o1 s <> eval_operand o2 s)
  [SMTPat (eval_ocmp s (ONe o1 o2))]

val lemma_cmp_le (s:vale_state) (o1:operand64{not (OMem? o1 || OStack? o1)}) (o2:operand64{not (OMem? o2 || OStack? o2)}) : Lemma
  (ensures eval_ocmp s (OLe o1 o2) <==> eval_operand o1 s <= eval_operand o2 s)
  [SMTPat (eval_ocmp s (OLe o1 o2))]

val lemma_cmp_ge (s:vale_state) (o1:operand64{not (OMem? o1 || OStack? o1)}) (o2:operand64{not (OMem? o2 || OStack? o2)}) : Lemma
  (ensures eval_ocmp s (OGe o1 o2) <==> eval_operand o1 s >= eval_operand o2 s)
  [SMTPat (eval_ocmp s (OGe o1 o2))]

val lemma_cmp_lt (s:vale_state) (o1:operand64{not (OMem? o1 || OStack? o1)}) (o2:operand64{not (OMem? o2 || OStack? o2)}) : Lemma
  (ensures eval_ocmp s (OLt o1 o2) <==> eval_operand o1 s < eval_operand o2 s)
  [SMTPat (eval_ocmp s (OLt o1 o2))]

val lemma_cmp_gt (s:vale_state) (o1:operand64{not (OMem? o1 || OStack? o1)}) (o2:operand64{not (OMem? o2 || OStack? o2)}) : Lemma
  (ensures eval_ocmp s (OGt o1 o2) <==> eval_operand o1 s > eval_operand o2 s)
  [SMTPat (eval_ocmp s (OGt o1 o2))]

val lemma_valid_cmp_eq (s:vale_state) (o1:operand64{not (OMem? o1 || OStack? o1)}) (o2:operand64{not (OMem? o2 || OStack? o2)}) : Lemma
  (ensures valid_src_operand o1 s /\ valid_src_operand o2 s ==> valid_ocmp (OEq o1 o2) s)
  [SMTPat (valid_ocmp (OEq o1 o2) s)]

val lemma_valid_cmp_ne (s:vale_state) (o1:operand64{not (OMem? o1 || OStack? o1)}) (o2:operand64{not (OMem? o2 || OStack? o2)}) : Lemma
  (ensures valid_src_operand o1 s /\ valid_src_operand o2 s ==> valid_ocmp (ONe o1 o2) s)
  [SMTPat (valid_ocmp (ONe o1 o2) s)]

val lemma_valid_cmp_le (s:vale_state) (o1:operand64{not (OMem? o1 || OStack? o1)}) (o2:operand64{not (OMem? o2 || OStack? o2)}) : Lemma
  (ensures valid_src_operand o1 s /\ valid_src_operand o2 s ==> valid_ocmp (OLe o1 o2) s)
  [SMTPat (valid_ocmp (OLe o1 o2) s)]

val lemma_valid_cmp_ge (s:vale_state) (o1:operand64{not (OMem? o1 || OStack? o1)}) (o2:operand64{not (OMem? o2 || OStack? o2)}) : Lemma
  (ensures valid_src_operand o1 s /\ valid_src_operand o2 s ==> valid_ocmp (OGe o1 o2) s)
  [SMTPat (valid_ocmp (OGe o1 o2) s)]

val lemma_valid_cmp_lt (s:vale_state) (o1:operand64{not (OMem? o1 || OStack? o1)}) (o2:operand64{not (OMem? o2 || OStack? o2)}) : Lemma
  (ensures valid_src_operand o1 s /\ valid_src_operand o2 s ==> valid_ocmp (OLt o1 o2) s)
  [SMTPat (valid_ocmp (OLt o1 o2) s)]

val lemma_valid_cmp_gt (s:vale_state) (o1:operand64{not (OMem? o1 || OStack? o1)}) (o2:operand64{not (OMem? o2 || OStack? o2)}) : Lemma
  (ensures valid_src_operand o1 s /\ valid_src_operand o2 s ==> valid_ocmp (OGt o1 o2) s)
  [SMTPat (valid_ocmp (OGt o1 o2) s)]

val compute_merge_total (f0:fuel) (fM:fuel) : fuel

val lemma_merge_total (b0:codes) (s0:vale_state) (f0:fuel) (sM:vale_state) (fM:fuel) (sN:vale_state) : Lemma
  (requires
    Cons? b0 /\
    eval_code (Cons?.hd b0) s0 f0 sM /\
    eval_code (Block (Cons?.tl b0)) sM fM sN
  )
  (ensures eval_code (Block b0) s0 (compute_merge_total f0 fM) sN)

val lemma_empty_total (s0:vale_state) (bN:codes) : Ghost (vale_state & fuel)
  (requires True)
  (ensures (fun (sM, fM) ->
    s0 == sM /\
    eval_code (Block []) s0 fM sM
  ))

val lemma_ifElse_total (ifb:ocmp) (ct:code) (cf:code) (s0:vale_state) : Ghost (bool & vale_state & vale_state & fuel)
  (requires True)
  (ensures  (fun (cond, sM, sN, f0) ->
    cond == eval_ocmp s0 ifb /\
    sM == s0
  ))

val lemma_ifElseTrue_total (ifb:ocmp) (ct:code) (cf:code) (s0:vale_state) (f0:fuel) (sM:vale_state) : Lemma
  (requires
    valid_ocmp ifb s0 /\
    eval_ocmp s0 ifb /\
    eval_code ct s0 f0 sM
  )
  (ensures
    eval_code (IfElse ifb ct cf) s0 f0 sM
  )

val lemma_ifElseFalse_total (ifb:ocmp) (ct:code) (cf:code) (s0:vale_state) (f0:fuel) (sM:vale_state) : Lemma
  (requires
    valid_ocmp ifb s0 /\
    not (eval_ocmp s0 ifb) /\
    eval_code cf s0 f0 sM
  )
  (ensures
    eval_code (IfElse ifb ct cf) s0 f0 sM
  )

val eval_while_inv (c:code) (s0:vale_state) (fW:fuel) (sW:vale_state) : Type0

val lemma_while_total (b:ocmp) (c:code) (s0:vale_state) : Ghost (vale_state & fuel)
  (requires True)
  (ensures fun (s1, f1) ->
    s1 == s0 /\
    eval_while_inv (While b c) s1 f1 s1
  )

val lemma_whileTrue_total (b:ocmp) (c:code) (s0:vale_state) (sW:vale_state) (fW:fuel) : Ghost (vale_state & fuel)
  (requires eval_ocmp sW b)
  (ensures fun (s1, f1) -> s1 == sW /\ f1 == fW)

val lemma_whileFalse_total (b:ocmp) (c:code) (s0:vale_state) (sW:vale_state) (fW:fuel) : Ghost (vale_state & fuel)
  (requires
    valid_ocmp b sW /\
    not (eval_ocmp sW b) /\
    eval_while_inv (While b c) s0 fW sW
  )
  (ensures fun (s1, f1) ->
    s1 == sW /\
    eval_code (While b c) s0 f1 s1
  )

val lemma_whileMerge_total (c:code) (s0:vale_state) (f0:fuel) (sM:vale_state) (fM:fuel) (sN:vale_state) : Ghost (fN:fuel)
  (requires
    While? c /\
    sN.vs_ok /\
    valid_ocmp (While?.whileCond c) sM /\
    eval_ocmp sM (While?.whileCond c) /\
    eval_while_inv c s0 f0 sM /\
    eval_code (While?.whileBody c) sM fM sN
  )
  (ensures (fun fN ->
    eval_while_inv c s0 fN sN
  ))
