module Vale.PPC64LE.Lemmas
open Vale.Def.Prop_s
open Vale.PPC64LE.Machine_s
open Vale.PPC64LE.State
open Vale.PPC64LE.StateLemmas
module S = Vale.PPC64LE.Semantics_s
open Vale.Arch.Heap
open Vale.Arch.HeapImpl
open Vale.Arch.HeapLemmas

unfold let code = S.code
unfold let codes = S.codes
unfold let ocmp = S.ocmp
unfold let fuel = nat

let xer_ov (xer:xer_t) : bool = S.xer_ov xer
let xer_ca (xer:xer_t) : bool = S.xer_ca xer
let update_xer_ov (xer:xer_t) (new_xer_ov:bool) = S.update_xer_ov xer new_xer_ov
let update_xer_ca (xer:xer_t) (new_xer_ca:bool) = S.update_xer_ca xer new_xer_ca

let rec code_modifies_ghost (c:code) : bool =
  match c with
  | Ins (S.Ghost _) -> true
  | Ins _ -> false
  | Block cs -> codes_modifies_ghost cs
  | IfElse _ c1 c2 -> code_modifies_ghost c1 || code_modifies_ghost c2
  | While _ c -> code_modifies_ghost c
and codes_modifies_ghost (cs:codes) : bool =
  match cs with
  | [] -> false
  | c::cs -> code_modifies_ghost c || codes_modifies_ghost cs

let core_state (ignore_ghost:bool) (s:state) : state =
  {s with
    ms_heap = if ignore_ghost then heap_ignore_ghost_machine s.ms_heap else s.ms_heap;
  }

let state_eq_S (ignore_ghost:bool) (s1 s2:state) =
  machine_state_eq (core_state ignore_ghost s1) (core_state ignore_ghost s2)

let state_eq_opt (ignore_ghost:bool) (s1 s2:option state) =
  match (s1, s2) with
  | (Some s1, Some s2) -> state_eq_S ignore_ghost s1 s2
  | _ -> s1 == s2

let eval_code (c:code) (s0:state) (f0:fuel) (s1:state) : Type0 =
  state_eq_opt (code_modifies_ghost c) (S.eval_code c f0 s0) (Some s1)

let eval_code2 (c:code) (s0:state) (f0:fuel) (s1:state) : prop0 =
  Some s1 == S.eval_code c f0 s0

let eval_ins (c:code) (s0:state) : Pure (state & fuel)
  (requires Ins? c)
  (ensures fun (sM, f0) ->
    eval_code c s0 f0 sM
  ) =
  let f0 = 0 in
  let (Some sM) = S.eval_code c f0 s0 in
  (sM, f0)

let eval_ocmp (s:state) (c:ocmp) : bool = S.eval_ocmp s c
let eval_cmp_opr (o:cmp_opr) (s:state) : nat64 = S.eval_cmp_opr o s
let valid_ocmp (c:ocmp) (s:state) : bool = S.valid_ocmp c s

val lemma_cmp_eq : s:state -> o1:cmp_opr -> o2:cmp_opr -> Lemma
  (ensures eval_ocmp s (S.OEq o1 o2) <==> eval_cmp_opr o1 s == eval_cmp_opr o2 s)
  [SMTPat (eval_ocmp s (S.OEq o1 o2))]

val lemma_cmp_ne : s:state -> o1:cmp_opr-> o2:cmp_opr -> Lemma
  (ensures eval_ocmp s (S.ONe o1 o2) <==> eval_cmp_opr o1 s <> eval_cmp_opr o2 s)
  [SMTPat (eval_ocmp s (S.ONe o1 o2))]

val lemma_cmp_le : s:state -> o1:cmp_opr-> o2:cmp_opr -> Lemma
  (ensures eval_ocmp s (S.OLe o1 o2) <==> eval_cmp_opr o1 s <= eval_cmp_opr o2 s)
  [SMTPat (eval_ocmp s (S.OLe o1 o2))]

val lemma_cmp_ge : s:state -> o1:cmp_opr-> o2:cmp_opr -> Lemma
  (ensures eval_ocmp s (S.OGe o1 o2) <==> eval_cmp_opr o1 s >= eval_cmp_opr o2 s)
  [SMTPat (eval_ocmp s (S.OGe o1 o2))]

val lemma_cmp_lt : s:state -> o1:cmp_opr-> o2:cmp_opr -> Lemma
  (ensures eval_ocmp s (S.OLt o1 o2) <==> eval_cmp_opr o1 s < eval_cmp_opr o2 s)
  [SMTPat (eval_ocmp s (S.OLt o1 o2))]

val lemma_cmp_gt : s:state -> o1:cmp_opr-> o2:cmp_opr -> Lemma
  (ensures eval_ocmp s (S.OGt o1 o2) <==> eval_cmp_opr o1 s > eval_cmp_opr o2 s)
  [SMTPat (eval_ocmp s (S.OGt o1 o2))]

val lemma_valid_cmp_eq : s:state -> o1:cmp_opr -> o2:cmp_opr -> Lemma
  (ensures valid_first_cmp_opr o1 ==> valid_ocmp (S.OEq o1 o2) s)
  [SMTPat (valid_ocmp (S.OEq o1 o2) s)]

val lemma_valid_cmp_ne : s:state -> o1:cmp_opr -> o2:cmp_opr -> Lemma
  (ensures valid_first_cmp_opr o1 ==> valid_ocmp (S.ONe o1 o2) s)
  [SMTPat (valid_ocmp (S.ONe o1 o2) s)]

val lemma_valid_cmp_le : s:state -> o1:cmp_opr -> o2:cmp_opr -> Lemma
  (ensures valid_first_cmp_opr o1 ==> valid_ocmp (S.OLe o1 o2) s)
  [SMTPat (valid_ocmp (S.OLe o1 o2) s)]

val lemma_valid_cmp_ge : s:state -> o1:cmp_opr -> o2:cmp_opr -> Lemma
  (ensures valid_first_cmp_opr o1 ==> valid_ocmp (S.OGe o1 o2) s)
  [SMTPat (valid_ocmp (S.OGe o1 o2) s)]

val lemma_valid_cmp_lt : s:state -> o1:cmp_opr -> o2:cmp_opr -> Lemma
  (ensures valid_first_cmp_opr o1 ==> valid_ocmp (S.OLt o1 o2) s)
  [SMTPat (valid_ocmp (S.OLt o1 o2) s)]

val lemma_valid_cmp_gt : s:state -> o1:cmp_opr -> o2:cmp_opr -> Lemma
  (ensures valid_first_cmp_opr o1 ==> valid_ocmp (S.OGt o1 o2) s)
  [SMTPat (valid_ocmp (S.OGt o1 o2) s)]

val compute_merge_total (f0:fuel) (fM:fuel) : fuel

val lemma_merge_total (b0:codes) (s0:state) (f0:fuel) (sM:state) (fM:fuel) (sN:state) : Lemma
  (requires
    Cons? b0 /\
    eval_code (Cons?.hd b0) s0 f0 sM /\
    eval_code (Block (Cons?.tl b0)) sM fM sN
  )
  (ensures eval_code (Block b0) s0 (compute_merge_total f0 fM) sN)

val lemma_empty_total (s0:state) (bN:codes) : Pure (state & fuel)
  (requires True)
  (ensures (fun (sM, fM) ->
    s0 == sM /\
    eval_code (Block []) s0 fM sM
  ))

val lemma_ifElse_total (ifb:ocmp) (ct:code) (cf:code) (s0:state) : Pure (bool & state & state & fuel)
  (requires True)
  (ensures  (fun (cond, sM, sN, f0) ->
    cond == eval_ocmp s0 ifb /\
    sM == {s0 with cr0 = S.eval_cmp_cr0 s0 ifb}
  ))

val lemma_ifElseTrue_total (ifb:ocmp) (ct:code) (cf:code) (s0:state) (f0:fuel) (sM:state) : Lemma
  (requires
    valid_ocmp ifb s0 /\
    eval_ocmp s0 ifb /\
    eval_code ct ({s0 with cr0 = S.eval_cmp_cr0 s0 ifb}) f0 sM
  )
  (ensures
    eval_code (IfElse ifb ct cf) s0 f0 sM
  )

val lemma_ifElseFalse_total (ifb:ocmp) (ct:code) (cf:code) (s0:state) (f0:fuel) (sM:state) : Lemma
  (requires
    valid_ocmp ifb s0 /\
    not (eval_ocmp s0 ifb) /\
    eval_code cf ({s0 with cr0 = S.eval_cmp_cr0 s0 ifb}) f0 sM
  )
  (ensures
    eval_code (IfElse ifb ct cf) s0 f0 sM
  )

val eval_while_inv (c:code) (s0:state) (fW:fuel) (sW:state) : prop0

val lemma_while_total (b:ocmp) (c:code) (s0:state) : Pure (state & fuel)
  (requires True)
  (ensures fun (s1, f1) ->
    s1 == s0 /\
    eval_while_inv (While b c) s1 f1 s1
  )

val lemma_whileTrue_total (b:ocmp) (c:code) (s0:state) (sW:state) (fW:fuel) : Pure (state & fuel)
  (requires valid_ocmp b sW /\ eval_ocmp sW b)
  (ensures fun (s1, f1) -> s1 == {sW with cr0 = S.eval_cmp_cr0 sW b} /\ f1 == fW)

val lemma_whileFalse_total (b:ocmp) (c:code) (s0:state) (sW:state) (fW:fuel) : Pure (state & fuel)
  (requires
    valid_ocmp b sW /\
    not (eval_ocmp sW b) /\
    eval_while_inv (While b c) s0 fW sW
  )
  (ensures fun (s1, f1) ->
    s1 == {sW with cr0 = S.eval_cmp_cr0 sW b} /\
    eval_code (While b c) s0 f1 s1
  )

val lemma_whileMerge_total (c:code) (s0:state) (f0:fuel) (sM:state) (fM:fuel) (sN:state)
  : Pure fuel
  (requires While? c /\ (
    let cond = While?.whileCond c in
    sN.ok /\
    valid_ocmp cond sM /\
    eval_ocmp sM cond /\
    eval_while_inv c s0 f0 sM /\
    eval_code (While?.whileBody c) ({sM with cr0 = S.eval_cmp_cr0 sM cond}) fM sN
  ))
  (ensures (fun fN ->
    eval_while_inv c s0 fN sN
  ))
