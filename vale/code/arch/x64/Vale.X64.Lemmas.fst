module Vale.X64.Lemmas
open FStar.Mul
open Vale.X64.Machine_s
open Vale.X64.State
open Vale.X64.StateLemmas
open Vale.X64.Instruction_s
open Vale.X64.Bytes_Code_s
module BS = Vale.X64.Machine_Semantics_s
module ME = Vale.X64.Memory

val eval_code_eq_all (g:bool) (c:code) (f:fuel) : Lemma
  (ensures (forall (s1 s2:machine_state).{:pattern (BS.machine_eval_code c f s1); (BS.machine_eval_code c f s2)}
    state_eq_S g s1 s2 ==>
    state_eq_opt g (BS.machine_eval_code c f s1) (BS.machine_eval_code c f s2)
  ))
  (decreases %[f; c; 1])

val eval_codes_eq_all (g:bool) (cs:codes) (f:fuel) : Lemma
  (ensures (forall (s1 s2:machine_state).{:pattern (BS.machine_eval_codes cs f s1); (BS.machine_eval_codes cs f s2)}
    state_eq_S g s1 s2 ==>
    state_eq_opt g (BS.machine_eval_codes cs f s1) (BS.machine_eval_codes cs f s2)
  ))
  (decreases %[f; cs])

val eval_while_eq_all (g:bool) (c:code) (f:fuel) : Lemma
  (ensures (forall (s1 s2:machine_state).{:pattern (BS.machine_eval_while c f s1); (BS.machine_eval_while c f s2)}
    While? c /\ state_eq_S g s1 s2 ==>
    state_eq_opt g (BS.machine_eval_while c f s1) (BS.machine_eval_while c f s2)
  ))
  (decreases %[f; c; 0])

#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"

#restart-solver
let rec lemma_eq_instr_apply_eval_args
    (outs:list instr_out) (args:list instr_operand)
    (f:instr_args_t outs args) (oprs:instr_operands_t_args args) (s1 s2:machine_state)
  : Lemma
  (requires state_eq_S true s1 s2)
  (ensures
    BS.instr_apply_eval_args outs args f oprs s1 == 
    BS.instr_apply_eval_args outs args f oprs s2)
  =
  let open BS in
  lemma_heap_ignore_ghost_machine s1.BS.ms_heap s2.BS.ms_heap;
  match args with
  | [] -> ()
  | i::args ->
    (
      let (v, oprs) : option (instr_val_t i) & instr_operands_t_args args =
        match i with
        | IOpEx i -> let oprs = coerce oprs in (instr_eval_operand_explicit i (fst oprs) s1, snd oprs)
        | IOpIm i -> (instr_eval_operand_implicit i s1, coerce oprs)
        in
      let f:arrow (instr_val_t i) (instr_args_t outs args) = coerce f in
      match v with
        | None -> ()
        | Some v -> lemma_eq_instr_apply_eval_args outs args (f v) oprs s1 s2
    )

#restart-solver
let rec lemma_eq_instr_apply_eval_inouts
    (outs inouts:list instr_out) (args:list instr_operand)
    (f:instr_inouts_t outs inouts args) (oprs:instr_operands_t inouts args) (s1 s2:machine_state)
  : Lemma
  (requires state_eq_S true s1 s2)
  (ensures
    BS.instr_apply_eval_inouts outs inouts args f oprs s1 == 
    BS.instr_apply_eval_inouts outs inouts args f oprs s2)
  =
  let open BS in
  lemma_heap_ignore_ghost_machine s1.BS.ms_heap s2.BS.ms_heap;
  match inouts with
  | [] -> lemma_eq_instr_apply_eval_args outs args f oprs s1 s2
  | (Out, i)::inouts ->
    let oprs =
      match i with
      | IOpEx i -> snd #(instr_operand_t i) (coerce oprs)
      | IOpIm i -> coerce oprs
      in
    lemma_eq_instr_apply_eval_inouts outs inouts args (coerce f) oprs s1 s2
  | (InOut, i)::inouts ->
    (
      let (v, oprs) : option (instr_val_t i) & instr_operands_t inouts args =
        match i with
        | IOpEx i -> let oprs = coerce oprs in (instr_eval_operand_explicit i (fst oprs) s1, snd oprs)
        | IOpIm i -> (instr_eval_operand_implicit i s1, coerce oprs)
        in
      let f:arrow (instr_val_t i) (instr_inouts_t outs inouts args) = coerce f in
      match v with
      | None -> ()
      | Some v -> lemma_eq_instr_apply_eval_inouts outs inouts args (f v) oprs s1 s2
    )

#restart-solver
let rec lemma_eq_instr_write_outputs
    (outs:list instr_out) (args:list instr_operand)
    (vs:instr_ret_t outs) (oprs:instr_operands_t outs args) (s1_orig s1 s2_orig s2:machine_state)
  : Lemma
  (requires state_eq_S true s1_orig s2_orig /\ state_eq_S true s1 s2)
  (ensures
    state_eq_S true
      (BS.instr_write_outputs outs args vs oprs s1_orig s1)
      (BS.instr_write_outputs outs args vs oprs s2_orig s2))
  =
  let open BS in
  use_machine_state_equal ();
  lemma_heap_ignore_ghost_machine s1.BS.ms_heap s2.BS.ms_heap;
  lemma_heap_ignore_ghost_machine s1_orig.BS.ms_heap s2_orig.BS.ms_heap;
  allow_inversion tmaddr;
  match outs with
  | [] -> ()
  | (_, i)::outs ->
    (
      let ((v:instr_val_t i), (vs:instr_ret_t outs)) =
        match outs with
        | [] -> (vs, ())
        | _::_ -> let vs = coerce vs in (fst vs, snd vs)
        in
      match i with
      | IOpEx i ->
        let oprs = coerce oprs in
        let s1 = instr_write_output_explicit i v (fst oprs) s1_orig s1 in
        let s2 = instr_write_output_explicit i v (fst oprs) s2_orig s2 in
        lemma_eq_instr_write_outputs outs args vs (snd oprs) s1_orig s1 s2_orig s2
      | IOpIm i ->
        let s1 = instr_write_output_implicit i v s1_orig s1 in
        let s2 = instr_write_output_implicit i v s2_orig s2 in
        allow_inversion operand64;
        allow_inversion operand128;
        lemma_eq_instr_write_outputs outs args vs (coerce oprs) s1_orig s1 s2_orig s2
    )

#restart-solver
let eval_ins_eq_instr (inst:BS.ins) (s1 s2:machine_state) : Lemma
  (requires Instr? inst /\ state_eq_S true s1 s2)
  (ensures state_eq_S true (BS.machine_eval_ins inst s1) (BS.machine_eval_ins inst s2))
  =
  let open BS in
  let Instr it oprs ann = inst in
  let InstrTypeRecord #outs #args #havoc_flags' i = it in
  lemma_eq_instr_apply_eval_inouts outs outs args (instr_eval i) oprs s1 s2;
  let vs = instr_apply_eval outs args (instr_eval i) oprs s1 in
  let hav s =
    match havoc_flags' with
    | HavocFlags -> {s with ms_flags = havoc_flags}
    | PreserveFlags -> s
    in
  let s1' = hav s1 in
  let s2' = hav s2 in
  match vs with
    | None -> ()
    | Some vs -> lemma_eq_instr_write_outputs outs args vs oprs s1 s1' s2 s2'

let eval_code_eq_instr (inst:BS.ins) (f:fuel) (s1 s2:machine_state) : Lemma
  (requires Instr? inst /\ state_eq_S true s1 s2)
  (ensures state_eq_opt true (BS.machine_eval_code (Ins inst) f s1) (BS.machine_eval_code (Ins inst) f s2))
  =
  eval_ins_eq_instr inst ({s1 with BS.ms_trace = []}) ({s2 with BS.ms_trace = []})

#restart-solver
let eval_code_eq_ins (i:BS.ins) (f:fuel) (s1 s2:machine_state) : Lemma
  (requires state_eq_S true s1 s2)
  (ensures state_eq_opt true (BS.machine_eval_code (Ins i) f s1) (BS.machine_eval_code (Ins i) f s2))
  =
  if Instr? i then eval_code_eq_instr i f s1 s2 else
  assert (Dealloc? i \/ Alloc? i \/ Push? i \/ Pop? i);
  use_machine_state_equal ();
  lemma_heap_ignore_ghost_machine s1.BS.ms_heap s2.BS.ms_heap;
  allow_inversion tmaddr;
  ()

#reset-options "--initial_fuel 2 --max_fuel 2 --z3rlimit 30"

#restart-solver
let rec eval_code_eq_all g c f =
  match c with
  | Ins i ->
      let lem (s1 s2:machine_state) : Lemma
        (requires state_eq_S g s1 s2)
        (ensures state_eq_opt g (BS.machine_eval_code c f s1) (BS.machine_eval_code c f s2))
        [SMTPat (BS.machine_eval_code c f s1); SMTPat (BS.machine_eval_code c f s2)]
        =
        if g then eval_code_eq_ins i f s1 s2
        in
      ()
  | Block cs -> eval_codes_eq_all g cs f
  | IfElse _ ct cf -> eval_code_eq_all g ct f; eval_code_eq_all g cf f
  | While _ _ -> eval_while_eq_all g c f
and eval_codes_eq_all g cs f =
  match cs with
  | [] -> ()
  | c::cs -> eval_code_eq_all g c f; eval_codes_eq_all g cs f
and eval_while_eq_all g c f =
  if f = 0 then () else
  match c with
  | While _ c_body -> eval_code_eq_all g c_body (f - 1); eval_while_eq_all g c (f - 1)
  | _ -> ()

let eval_code_eq_f (c:code) (f:fuel) (s1 s2:machine_state) : Lemma
  (requires state_eq_S false s1 s2)
  (ensures state_eq_opt false (BS.machine_eval_code c f s1) (BS.machine_eval_code c f s2))
  [SMTPat (BS.machine_eval_code c f s1); SMTPat (BS.machine_eval_code c f s2)]
  =
  eval_code_eq_all false c f

let eval_codes_eq_f (cs:codes) (f:fuel) (s1 s2:machine_state) : Lemma
  (requires state_eq_S false s1 s2)
  (ensures state_eq_opt false (BS.machine_eval_codes cs f s1) (BS.machine_eval_codes cs f s2))
  [SMTPat (BS.machine_eval_codes cs f s1); SMTPat (BS.machine_eval_codes cs f s2)]
  =
  eval_codes_eq_all false cs f

let eval_while_eq_f (c:code) (f:fuel) (s1 s2:machine_state) : Lemma
  (requires While? c /\ state_eq_S false s1 s2)
  (ensures state_eq_opt false (BS.machine_eval_while c f s1) (BS.machine_eval_while c f s2))
  [SMTPat (BS.machine_eval_while c f s1); SMTPat (BS.machine_eval_while c f s2)]
  =
  eval_while_eq_all false c f

let eval_code_eq_t (c:code) (f:fuel) (s1 s2:machine_state) : Lemma
  (requires state_eq_S true s1 s2)
  (ensures state_eq_opt true (BS.machine_eval_code c f s1) (BS.machine_eval_code c f s2))
  [SMTPat (BS.machine_eval_code c f s1); SMTPat (BS.machine_eval_code c f s2)]
  =
  eval_code_eq_all true c f

let eval_codes_eq_t (cs:codes) (f:fuel) (s1 s2:machine_state) : Lemma
  (requires state_eq_S true s1 s2)
  (ensures state_eq_opt true (BS.machine_eval_codes cs f s1) (BS.machine_eval_codes cs f s2))
  [SMTPat (BS.machine_eval_codes cs f s1); SMTPat (BS.machine_eval_codes cs f s2)]
  =
  eval_codes_eq_all true cs f

let eval_while_eq_t (c:code) (f:fuel) (s1 s2:machine_state) : Lemma
  (requires While? c /\ state_eq_S true s1 s2)
  (ensures state_eq_opt true (BS.machine_eval_while c f s1) (BS.machine_eval_while c f s2))
  [SMTPat (BS.machine_eval_while c f s1); SMTPat (BS.machine_eval_while c f s2)]
  =
  eval_while_eq_all true c f

let eval_code_ts (g:bool) (c:code) (s0:machine_state) (f0:fuel) (s1:machine_state) : Type0 =
  state_eq_opt g (BS.machine_eval_code c f0 s0) (Some s1)

val increase_fuel (g:bool) (c:code) (s0:machine_state) (f0:fuel) (sN:machine_state) (fN:fuel) : Lemma
  (requires eval_code_ts g c s0 f0 sN /\ f0 <= fN)
  (ensures eval_code_ts g c s0 fN sN)
  (decreases %[f0; c])

val increase_fuels (g:bool) (c:codes) (s0:machine_state) (f0:fuel) (sN:machine_state) (fN:fuel) : Lemma
  (requires eval_code_ts g (Block c) s0 f0 sN /\ f0 <= fN)
  (ensures eval_code_ts g (Block c) s0 fN sN)
  (decreases %[f0; c])

let eval_code_ts_b (b:bool) (c:code) (s0:machine_state) (f0:fuel) (s1:machine_state) : Type0 =
state_eq_opt b (BS.machine_eval_code c f0 s0) (Some s1)

let rec increase_fuel g c s0 f0 sN fN =
  match c with
  | Ins ins -> ()
  | Block l -> increase_fuels g l s0 f0 sN fN
  | IfElse b t f ->
      let (_, b0) = BS.machine_eval_ocmp s0 b in
      if b0 then increase_fuel g t s0 f0 sN fN else increase_fuel g f s0 f0 sN fN
  | While b c ->
      let (s1, b0) = BS.machine_eval_ocmp s0 b in
      if not b0 then ()
      else
      (
        let s1 = {s1 with BS.ms_trace = (BranchPredicate true)::s1.BS.ms_trace} in
        match BS.machine_eval_code c (f0 - 1) s1 with
        | None -> ()
        | Some s2 ->
            increase_fuel g c s1 (f0 - 1) s2 (fN - 1);
            if s2.BS.ms_ok then increase_fuel g (While b c) s2 (f0 - 1) sN (fN - 1)
            else ()
      )

and increase_fuels g c s0 f0 sN fN =
  match c with
  | [] -> ()
  | h::t ->
    (
      let Some s1 = BS.machine_eval_code h f0 s0 in
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

let lemma_merge_total (b0:codes) (s0:vale_state) (f0:fuel) (sM:vale_state) (fM:fuel) (sN:vale_state) =
  let f = if f0 > fM then f0 else fM in
  increase_fuel (codes_modifies_ghost b0) (Cons?.hd b0) (state_to_S s0) f0 (state_to_S sM) f;
  increase_fuel (codes_modifies_ghost b0) (Block (Cons?.tl b0)) (state_to_S sM) fM (state_to_S sN) f

let lemma_empty_total (s0:vale_state) (bN:codes) =
  (s0, 0)

let lemma_ifElse_total (ifb:ocmp) (ct:code) (cf:code) (s0:vale_state) =
  (eval_ocmp s0 ifb, s0, s0, 0)

let lemma_ifElseTrue_total (ifb:ocmp) (ct:code) (cf:code) (s0:vale_state) (f0:fuel) (sM:vale_state) =
  ()

let lemma_ifElseFalse_total (ifb:ocmp) (ct:code) (cf:code) (s0:vale_state) (f0:fuel) (sM:vale_state) =
  ()

let eval_while_inv_temp (c:code) (s0:vale_state) (fW:fuel) (sW:vale_state) : Type0 =
  forall (f:nat).{:pattern BS.machine_eval_code c f (state_to_S sW)}
    Some? (BS.machine_eval_code c f (state_to_S sW)) ==>
    state_eq_opt (code_modifies_ghost c)
      (BS.machine_eval_code c (f + fW) (state_to_S s0))
      (BS.machine_eval_code c f (state_to_S sW))

let eval_while_inv (c:code) (s0:vale_state) (fW:fuel) (sW:vale_state) : Type0 =
  eval_while_inv_temp c s0 fW sW

let lemma_while_total (b:ocmp) (c:code) (s0:vale_state) =
  (s0, 0)

let lemma_whileTrue_total (b:ocmp) (c:code) (s0:vale_state) (sW:vale_state) (fW:fuel) =
  (sW, fW)

let lemma_whileFalse_total (b:ocmp) (c:code) (s0:vale_state) (sW:vale_state) (fW:fuel) =
  let f1 = fW + 1 in
  assert (state_eq_opt (code_modifies_ghost c) (BS.machine_eval_code (While b c) f1 (state_to_S s0)) (BS.machine_eval_code (While b c) 1 (state_to_S sW)));
  assert (eval_code (While b c) s0 f1 sW);
  (sW, f1)

#restart-solver
let lemma_whileMerge_total (c:code) (s0:vale_state) (f0:fuel) (sM:vale_state) (fM:fuel) (sN:vale_state) =
  let fN:nat = f0 + fM + 1 in
  let g = code_modifies_ghost c in
  let fForall (f:nat) : Lemma
    (requires Some? (BS.machine_eval_code c f (state_to_S sN)))
    (ensures state_eq_opt g (BS.machine_eval_code c (f + fN) (state_to_S s0)) (BS.machine_eval_code c f (state_to_S sN)))
    [SMTPat (BS.machine_eval_code c f (state_to_S sN))]
    =
    let Some sZ = BS.machine_eval_code c f (state_to_S sN) in
    let fZ = if f > fM then f else fM in
    increase_fuel (code_modifies_ghost c) (While?.whileBody c) (state_to_S sM) fM (state_to_S sN) fZ;

    increase_fuel (code_modifies_ghost c) c (state_to_S sN) f sZ fZ;

    assert (state_eq_opt g (BS.machine_eval_code c (fZ + 1) (state_to_S sM)) (Some sZ)); // via eval_code for While
    assert (state_eq_opt g (BS.machine_eval_code c (fZ + 1) (state_to_S sM)) (BS.machine_eval_code c (fZ + 1 + f0) (state_to_S s0))); // via eval_while_inv, choosing f = fZ + 1

    // Two assertions above prove (BS.machine_eval_code c (fZ + 1 + f0) (state_to_S s0)) equals (Some sZ)
    // increase_fuel (code_modifies_ghost c) c s0 (fZ + 1 + f0) (state_of_S s0 sZ) (f + fN);
    increase_fuel (code_modifies_ghost c) c (state_to_S s0) (fZ + 1 + f0) sZ (f + fN);
    assert (state_eq_opt g (BS.machine_eval_code c (f + fN) (state_to_S s0)) (Some sZ));
    ()
    in
  fN
