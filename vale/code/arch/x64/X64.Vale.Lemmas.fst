module X64.Vale.Lemmas
open X64.Machine_s
open X64.Vale.State
open X64.Vale.StateLemmas
module BS = X64.Bytes_Semantics_s
module TS = X64.Taint_Semantics_s
module ME = X64.Memory

friend X64.Vale.StateLemmas

#reset-options "--initial_fuel 2 --max_fuel 2 --z3rlimit 20"

val eval_code_eq_all (c:code) (f:fuel) : Lemma
  (ensures (forall (s1 s2:TS.traceState).{:pattern (TS.taint_eval_code c f s1); (TS.taint_eval_code c f s2)}
    state_eq_S s1 s2 ==>
    state_eq_opt (TS.taint_eval_code c f s1) (TS.taint_eval_code c f s2)
  ))
  (decreases %[f; c; 1])

val eval_codes_eq_all (cs:codes) (f:fuel) : Lemma
  (ensures (forall (s1 s2:TS.traceState).{:pattern (TS.taint_eval_codes cs f s1); (TS.taint_eval_codes cs f s2)}
    state_eq_S s1 s2 ==>
    state_eq_opt (TS.taint_eval_codes cs f s1) (TS.taint_eval_codes cs f s2)
  ))
  (decreases %[f; cs])

val eval_while_eq_all (c:code) (f:fuel) : Lemma
  (ensures (forall (s1 s2:TS.traceState).{:pattern (TS.taint_eval_while c f s1); (TS.taint_eval_while c f s2)}
    While? c /\ state_eq_S s1 s2 ==>
    state_eq_opt (TS.taint_eval_while c f s1) (TS.taint_eval_while c f s2)
  ))
  (decreases %[f; c; 0])

let rec eval_code_eq_all c f =
  match c with
  | Ins ins -> ()
  | Block cs -> eval_codes_eq_all cs f
  | IfElse _ ct cf -> eval_code_eq_all ct f; eval_code_eq_all cf f
  | While _ _ -> eval_while_eq_all c f
and eval_codes_eq_all cs f =
  match cs with
  | [] -> ()
  | c::cs -> eval_code_eq_all c f; eval_codes_eq_all cs f
and eval_while_eq_all c f =
  if f = 0 then () else
  match c with
  | While _ c_body -> eval_code_eq_all c_body (f - 1); eval_while_eq_all c (f - 1)
  | _ -> ()

let eval_code_eq (c:code) (f:fuel) (s1 s2:TS.traceState) : Lemma
  (requires state_eq_S s1 s2)
  (ensures state_eq_opt (TS.taint_eval_code c f s1) (TS.taint_eval_code c f s2))
  [SMTPat (TS.taint_eval_code c f s1); SMTPat (TS.taint_eval_code c f s2)]
  =
  eval_code_eq_all c f

let eval_codes_eq (cs:codes) (f:fuel) (s1 s2:TS.traceState) : Lemma
  (requires state_eq_S s1 s2)
  (ensures state_eq_opt (TS.taint_eval_codes cs f s1) (TS.taint_eval_codes cs f s2))
  [SMTPat (TS.taint_eval_codes cs f s1); SMTPat (TS.taint_eval_codes cs f s2)]
  =
  eval_codes_eq_all cs f

let eval_while_eq (c:code) (f:fuel) (s1 s2:TS.traceState) : Lemma
  (requires While? c /\ state_eq_S s1 s2)
  (ensures state_eq_opt (TS.taint_eval_while c f s1) (TS.taint_eval_while c f s2))
  [SMTPat (TS.taint_eval_while c f s1); SMTPat (TS.taint_eval_while c f s2)]
  =
  eval_while_eq_all c f

let eval_code_ts (c:code) (s0:TS.traceState) (f0:fuel) (s1:TS.traceState) : Type0 =
  state_eq_opt (TS.taint_eval_code c f0 s0) (Some s1)

val increase_fuel (c:code) (s0:TS.traceState) (f0:fuel) (sN:TS.traceState) (fN:fuel) : Lemma
  (requires eval_code_ts c s0 f0 sN /\ f0 <= fN)
  (ensures eval_code_ts c s0 fN sN)
  (decreases %[f0; c])

val increase_fuels (c:codes) (s0:TS.traceState) (f0:fuel) (sN:TS.traceState) (fN:fuel) : Lemma
  (requires eval_code_ts (Block c) s0 f0 sN /\ f0 <= fN)
  (ensures eval_code_ts (Block c) s0 fN sN)
  (decreases %[f0; c])

let rec increase_fuel c s0 f0 sN fN =
  match c with
  | Ins ins -> ()
  | Block l -> increase_fuels l s0 f0 sN fN
  | IfElse b t f ->
      let _, b0 = TS.taint_eval_ocmp s0 b in
      if b0 then increase_fuel t s0 f0 sN fN else increase_fuel f s0 f0 sN fN
  | While b c ->
      let s1, b0 = TS.taint_eval_ocmp s0 b in
      if not b0 then ()
      else
      (
        let s1 = {s1 with TS.trace=BranchPredicate(true)::s1.TS.trace} in
        match TS.taint_eval_code c (f0 - 1) s1 with
        | None -> ()
        | Some s2 ->
            increase_fuel c s1 (f0 - 1) s2 (fN - 1);
            if s2.TS.state.BS.ok then increase_fuel (While b c) s2 (f0 - 1) sN (fN - 1)
            else ()
      )

and increase_fuels c s0 f0 sN fN =
  match c with
  | [] -> ()
  | h::t ->
    (
      let Some s1 = TS.taint_eval_code h f0 s0 in
      increase_fuel h s0 f0 s1 fN;
      increase_fuels t s1 f0 sN fN
    )

let lemma_cmp_eq s o1 o2 t = ()
let lemma_cmp_ne s o1 o2 t = ()
let lemma_cmp_le s o1 o2 t = ()
let lemma_cmp_ge s o1 o2 t = ()
let lemma_cmp_lt s o1 o2 t = ()
let lemma_cmp_gt s o1 o2 t = ()

let lemma_valid_cmp_eq s o1 o2 t = ()
let lemma_valid_cmp_ne s o1 o2 t = ()
let lemma_valid_cmp_le s o1 o2 t = ()
let lemma_valid_cmp_ge s o1 o2 t = ()
let lemma_valid_cmp_lt s o1 o2 t = ()
let lemma_valid_cmp_gt s o1 o2 t = ()

let compute_merge_total (f0:fuel) (fM:fuel) =
  if f0 > fM then f0 else fM

let lemma_merge_total (b0:codes) (s0:state) (f0:fuel) (sM:state) (fM:fuel) (sN:state) =
  let f = if f0 > fM then f0 else fM in
  increase_fuel (Cons?.hd b0) (state_to_S s0) f0 (state_to_S sM) f;
  increase_fuel (Block (Cons?.tl b0)) (state_to_S sM) fM (state_to_S sN) f

let lemma_empty_total (s0:state) (bN:codes) =
  (s0, 0)

let lemma_ifElse_total (ifb:ocmp) (ct:code) (cf:code) (s0:state) =
  (eval_ocmp s0 ifb, s0, s0, 0)

let lemma_ifElseTrue_total (ifb:ocmp) (ct:code) (cf:code) (s0:state) (f0:fuel) (sM:state) =
  ()

let lemma_ifElseFalse_total (ifb:ocmp) (ct:code) (cf:code) (s0:state) (f0:fuel) (sM:state) =
  ()

let eval_while_inv_temp (c:code) (s0:state) (fW:fuel) (sW:state) : Type0 =
  forall (f:nat).{:pattern TS.taint_eval_code c f (state_to_S sW)}
    Some? (TS.taint_eval_code c f (state_to_S sW)) ==>
    state_eq_opt (TS.taint_eval_code c (f + fW) (state_to_S s0)) (TS.taint_eval_code c f (state_to_S sW))

let eval_while_inv (c:code) (s0:state) (fW:fuel) (sW:state) : Type0 =
  eval_while_inv_temp c s0 fW sW

let lemma_while_total (b:ocmp) (c:code) (s0:state) =
  (s0, 0)

let lemma_whileTrue_total (b:ocmp) (c:code) (s0:state) (sW:state) (fW:fuel) =
  (sW, fW)

let lemma_whileFalse_total (b:ocmp) (c:code) (s0:state) (sW:state) (fW:fuel) =
  let f1 = fW + 1 in
  assert (state_eq_opt (TS.taint_eval_code (While b c) f1 (state_to_S s0)) (TS.taint_eval_code (While b c) 1 (state_to_S sW)));
  assert (eval_code (While b c) s0 f1 sW);
  (sW, f1)

#reset-options "--initial_fuel 2 --max_fuel 2 --z3rlimit 30"
let lemma_whileMerge_total (c:code) (s0:state) (f0:fuel) (sM:state) (fM:fuel) (sN:state) =
  let fN:nat = f0 + fM + 1 in
  let lForall () : Lemma
    (forall (f:nat).{:pattern (TS.taint_eval_code c f (state_to_S sN))}
      Some? (TS.taint_eval_code c f (state_to_S sN)) ==>
      state_eq_opt (TS.taint_eval_code c (f + fN) (state_to_S s0)) (TS.taint_eval_code c f (state_to_S sN))
    ) =
    let fForall (f:nat) : Lemma
      (requires Some? (TS.taint_eval_code c f (state_to_S sN)))
      (ensures state_eq_opt (TS.taint_eval_code c (f + fN) (state_to_S s0)) (TS.taint_eval_code c f (state_to_S sN))) =
      let Some sZ = TS.taint_eval_code c f (state_to_S sN) in
      let fZ = if f > fM then f else fM in
      increase_fuel (While?.whileBody c) (state_to_S sM) fM (state_to_S sN) fZ;
      
      increase_fuel c (state_to_S sN) f sZ fZ;
      
      assert (state_eq_opt (TS.taint_eval_code c (fZ + 1) (state_to_S sM)) (Some sZ)); // via eval_code for While
      assert (state_eq_opt (TS.taint_eval_code c (fZ + 1) (state_to_S sM)) (TS.taint_eval_code c (fZ + 1 + f0) (state_to_S s0))); // via eval_while_inv, choosing f = fZ + 1

      // Two assertions above prove (TS.taint_eval_code c (fZ + 1 + f0) (state_to_S s0)) equals (Some sZ)
      // increase_fuel c s0 (fZ + 1 + f0) (state_of_S s0 sZ) (f + fN);
      increase_fuel c (state_to_S s0) (fZ + 1 + f0) sZ (f + fN);
      assert (state_eq_opt (TS.taint_eval_code c (f + fN) (state_to_S s0)) (Some sZ));
      ()
      in
    Classical.ghost_lemma fForall
    in
  lForall ();
  fN
