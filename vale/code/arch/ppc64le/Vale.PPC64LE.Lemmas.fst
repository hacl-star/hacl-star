module Vale.PPC64LE.Lemmas
open Vale.PPC64LE.Machine_s
open Vale.PPC64LE.State
module S = Vale.PPC64LE.Semantics_s
open Vale.Arch.HeapLemmas

#reset-options "--initial_fuel 2 --max_fuel 2 --z3rlimit 400"

let eval_code_eq_ins (g:bool) (i:S.ins) (s:state) : Lemma
  (ensures (
    let s1 = S.run (S.eval_ins i) s in
    let s2 = S.run (S.eval_ins i) (core_state g s) in
    state_eq_S g s1 s2
  ))
  =
  lemma_heap_ignore_ghost_machine s.ms_heap (core_state g s).ms_heap;
  use_machine_state_equal ()

let eval_ocmp_eq_core (g:bool) (cond:ocmp) (s:state) : Lemma
  (ensures (
    let (s1, b1) = S.run_ocmp s cond in
    let (s2, b2) = S.run_ocmp (core_state g s) cond in
    state_eq_S g s1 s2 /\ b1 == b2
  ))
  =
  ()

#restart-solver
let rec eval_code_eq_core (g:bool) (c:code) (f:fuel) (s:state) : Lemma
  (ensures state_eq_opt g (S.eval_code c f s) (S.eval_code c f (core_state g s)))
  (decreases %[f; c])
  =
  match c with
  | Ins i -> eval_code_eq_ins g i s
  | Block cs -> eval_codes_eq_core g cs f s
  | IfElse cond ct cf ->
    eval_ocmp_eq_core g cond s;
    let (s', _) = S.run_ocmp s cond in
    let (t', _) = S.run_ocmp (core_state g s) cond in
    eval_code_eq_core g ct f s';
    eval_code_eq_core g ct f t';
    eval_code_eq_core g cf f s';
    eval_code_eq_core g cf f t';
    ()
  | While cond body -> eval_while_eq_core g cond body f s
and eval_codes_eq_core (g:bool) (cs:codes) (f:fuel) (s:state) : Lemma
  (ensures state_eq_opt g (S.eval_codes cs f s) (S.eval_codes cs f (core_state g s)))
  (decreases %[f; cs])
  =
  match cs with
  | [] -> ()
  | c'::cs' -> (
      eval_code_eq_core g c' f s;
      match (S.eval_code c' f s, S.eval_code c' f (core_state g s)) with
      | (None, None) -> ()
      | (Some s', Some t') -> eval_codes_eq_core g cs' f s'; eval_codes_eq_core g cs' f t'
    )
and eval_while_eq_core (g:bool) (cond:ocmp) (body:code) (f:fuel) (s:state) : Lemma
  (ensures state_eq_opt g (S.eval_while cond body f s) (S.eval_while cond body f (core_state g s)))
  (decreases %[f; body])
  =
  if f > 0 then (
    eval_ocmp_eq_core g cond s;
    let (s1, _) = S.run_ocmp s cond in
    let (t1, _) = S.run_ocmp (core_state g s) cond in
    eval_code_eq_core g body (f - 1) s1;
    eval_code_eq_core g body (f - 1) t1;
    match (S.eval_code body (f - 1) s1, S.eval_code body (f - 1) t1) with
    | (None, None) -> ()
    | (Some s2, Some t2) ->
      eval_while_eq_core g cond body (f - 1) s2;
      eval_while_eq_core g cond body (f - 1) t2;
      ()
  )

let eval_code_eq_f (c:code) (f:fuel) (s1 s2:state) : Lemma
  (requires state_eq_S false s1 s2)
  (ensures state_eq_opt false (S.eval_code c f s1) (S.eval_code c f s2))
  [SMTPat (S.eval_code c f s1); SMTPat (S.eval_code c f s2)]
  =
  eval_code_eq_core false c f s1; eval_code_eq_core false c f s2

let eval_codes_eq_f (cs:codes) (f:fuel) (s1 s2:state) : Lemma
  (requires state_eq_S false s1 s2)
  (ensures state_eq_opt false (S.eval_codes cs f s1) (S.eval_codes cs f s2))
  [SMTPat (S.eval_codes cs f s1); SMTPat (S.eval_codes cs f s2)]
  =
  eval_codes_eq_core false cs f s1; eval_codes_eq_core false cs f s2

let eval_while_eq_f (cond:ocmp) (body:code) (f:fuel) (s1 s2:state) : Lemma
  (requires state_eq_S false s1 s2)
  (ensures state_eq_opt false (S.eval_while cond body f s1) (S.eval_while cond body f s2))
  [SMTPat (S.eval_while cond body f s1); SMTPat (S.eval_while cond body f s2)]
  =
  eval_while_eq_core false cond body f s1; eval_while_eq_core false cond body f s2

let eval_code_eq_t (c:code) (f:fuel) (s1 s2:state) : Lemma
  (requires state_eq_S true s1 s2)
  (ensures state_eq_opt true (S.eval_code c f s1) (S.eval_code c f s2))
  [SMTPat (S.eval_code c f s1); SMTPat (S.eval_code c f s2)]
  =
  eval_code_eq_core true c f s1; eval_code_eq_core true c f s2

let eval_codes_eq_t (cs:codes) (f:fuel) (s1 s2:state) : Lemma
  (requires state_eq_S true s1 s2)
  (ensures state_eq_opt true (S.eval_codes cs f s1) (S.eval_codes cs f s2))
  [SMTPat (S.eval_codes cs f s1); SMTPat (S.eval_codes cs f s2)]
  =
  eval_codes_eq_core true cs f s1; eval_codes_eq_core true cs f s2

let eval_while_eq_t (cond:ocmp) (body:code) (f:fuel) (s1 s2:state) : Lemma
  (requires state_eq_S true s1 s2)
  (ensures state_eq_opt true (S.eval_while cond body f s1) (S.eval_while cond body f s2))
  [SMTPat (S.eval_while cond body f s1); SMTPat (S.eval_while cond body f s2)]
  =
  eval_while_eq_core true cond body f s1; eval_while_eq_core true cond body f s2

let eval_code_ts (g:bool) (c:code) (s0:state) (f0:fuel) (s1:state) : Type0 =
  state_eq_opt g (S.eval_code c f0 s0) (Some s1)

let rec increase_fuel (g:bool) (c:code) (s0:state) (f0:fuel) (sN:state) (fN:fuel) : Lemma
  (requires eval_code_ts g c s0 f0 sN /\ f0 <= fN)
  (ensures eval_code_ts g c s0 fN sN)
  (decreases %[f0; c])
  =
  match c with
  | Ins ins -> ()
  | Block l -> increase_fuels g l s0 f0 sN fN
  | IfElse cond t f ->
      let (s0, b) = S.run_ocmp s0 cond in
      if b then increase_fuel g t s0 f0 sN fN else increase_fuel g f s0 f0 sN fN
  | While cond c ->
      let (s0, b) = S.run_ocmp s0 cond in
      if not b then ()
      else
      (
        match S.eval_code c (f0 - 1) s0 with
        | None -> ()
        | Some s1 ->
            increase_fuel g c s0 (f0 - 1) s1 (fN - 1);
            if s1.ok then increase_fuel g (While cond c) s1 (f0 - 1) sN (fN - 1)
            else ()
      )
and increase_fuels (g:bool) (c:codes) (s0:state) (f0:fuel) (sN:state) (fN:fuel) : Lemma
  (requires eval_code_ts g (Block c) s0 f0 sN /\ f0 <= fN)
  (ensures eval_code_ts g (Block c) s0 fN sN)
  (decreases %[f0; c])
  =
  match c with
  | [] -> ()
  | h::t ->
    (
      let Some s1 = S.eval_code h f0 s0 in
      increase_fuel g h s0 f0 s1 fN;
      increase_fuels g t s1 f0 sN fN
    )

let lemma_cmp_eq s o1 o2 = ()
let lemma_cmp_ne s o1 o2 = ()
let lemma_cmp_le s o1 o2 = ()
let lemma_cmp_ge s o1 o2 = ()
let lemma_cmp_lt s o1 o2 = ()
let lemma_cmp_gt s o1 o2 = ()

let lemma_valid_cmp_eq s o1 o2 = ()
let lemma_valid_cmp_ne s o1 o2 = ()
let lemma_valid_cmp_le s o1 o2 = ()
let lemma_valid_cmp_ge s o1 o2 = ()
let lemma_valid_cmp_lt s o1 o2 = ()
let lemma_valid_cmp_gt s o1 o2 = ()

let compute_merge_total (f0:fuel) (fM:fuel) =
  if f0 > fM then f0 else fM

let lemma_merge_total (b0:codes) (s0:state) (f0:fuel) (sM:state) (fM:fuel) (sN:state) =
  let f = if f0 > fM then f0 else fM in
  increase_fuel (codes_modifies_ghost b0) (Cons?.hd b0) s0 f0 sM f;
  increase_fuel (codes_modifies_ghost b0) (Block (Cons?.tl b0)) sM fM sN f

let lemma_empty_total (s0:state) (bN:codes) =
  (s0, 0)

let lemma_ifElse_total (ifb:ocmp) (ct:code) (cf:code) (s0:state) =
  (eval_ocmp s0 ifb, ({s0 with cr0 = S.eval_cmp_cr0 s0 ifb}), s0, 0)

let lemma_ifElseTrue_total (ifb:ocmp) (ct:code) (cf:code) (s0:state) (f0:fuel) (sM:state) =
  ()

let lemma_ifElseFalse_total (ifb:ocmp) (ct:code) (cf:code) (s0:state) (f0:fuel) (sM:state) =
  ()

let eval_while_inv_temp (c:code) (s0:state) (fW:fuel) (sW:state) : Type0 =
  forall (f:nat).{:pattern S.eval_code c f sW}
    Some? (S.eval_code c f sW) ==>
    state_eq_opt (code_modifies_ghost c)
      (S.eval_code c (f + fW) s0)
      (S.eval_code c f sW)

let eval_while_inv (c:code) (s0:state) (fW:fuel) (sW:state) : Type0 =
  eval_while_inv_temp c s0 fW sW

let lemma_while_total (b:ocmp) (c:code) (s0:state) =
  (s0, 0)

let lemma_whileTrue_total (b:ocmp) (c:code) (s0:state) (sW:state) (fW:fuel) =
  ({sW with cr0 = S.eval_cmp_cr0 sW b}, fW)

let lemma_whileFalse_total (b:ocmp) (c:code) (s0:state) (sW:state) (fW:fuel) =
  let f1 = fW + 1 in
  let (s1, _) = S.run_ocmp sW b in
  //assert (S.eval_code (While b c) f1 s0 == S.eval_code (While b c) 1 sW);
  assert (state_eq_opt (code_modifies_ghost c) (S.eval_code (While b c) f1 s0) (S.eval_code (While b c) 1 sW));
  assert (eval_code (While b c) s0 f1 s1);
  (s1, f1)

#reset-options "--initial_fuel 2 --max_fuel 2 --z3rlimit 30"
let lemma_whileMerge_total (c:code) (s0:state) (f0:fuel) (sM:state) (fM:fuel) (sN:state) =
  let cond = While?.whileCond c in
  let fN:nat = f0 + fM + 1 in
  let g = code_modifies_ghost c in
  let fForall (f:nat) : Lemma
    (requires Some? (S.eval_code c f sN))
    (ensures state_eq_opt g (S.eval_code c (f + fN) s0) (S.eval_code c f sN)) =
    let Some sZ = S.eval_code c f sN in
    let fZ = if f > fM then f else fM in
    let sM' = {sM with cr0 = S.eval_cmp_cr0 sM cond} in
    increase_fuel (code_modifies_ghost c) (While?.whileBody c) sM' fM sN fZ;
    increase_fuel (code_modifies_ghost c) c sN f sZ fZ;
    assert (state_eq_opt g (S.eval_code c (fZ + 1) sM) (Some sZ));
    //assert (S.eval_code c (fZ + 1) sM == Some sZ);
    assert (state_eq_opt g (S.eval_code c (fZ + 1) sM) (S.eval_code c (fZ + 1 + f0) s0));
    //assert (S.eval_code c (fZ + 1) sM == S.eval_code c (fZ + 1 + f0) s0);
    assert (state_eq_opt g (S.eval_code c (fZ + 1 + f0) s0) (Some sZ));
    //assert (S.eval_code c (fZ + 1 + f0) s0 == Some sZ);
    increase_fuel (code_modifies_ghost c) c s0 (fZ + 1 + f0) sZ (f + fN);
    assert (state_eq_opt g (S.eval_code c (f + fN) s0) (Some sZ));
    //assert (S.eval_code c (f + fN) s0 == Some sZ);
    ()
    in
  Classical.ghost_lemma fForall;
  fN
