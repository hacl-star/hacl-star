module Vale.Transformers.Transform

module BS = Vale.X64.Machine_Semantics_s

open Vale.X64.Machine_Semantics_s
open Vale.X64.Machine_s
open Vale.Def.PossiblyMonad
open Vale.X64.Decls

open Vale.Def.PossiblyMonad

open Vale.X64.State

open Vale.X64.Lemmas
open Vale.X64.StateLemmas

friend Vale.X64.Decls
friend Vale.X64.StateLemmas

module IR = Vale.Transformers.InstructionReorder

unfold
let transformation_result_of_possibly_codes (c:possibly codes) (if_fail:code) =
  match c with
  | Ok c -> {
      success = ttrue;
      result = Block c;
    }
  | Err reason -> {
      success = ffalse reason;
      result = if_fail;
    }

let prints_to_same_code (c1 c2:code) : pbool =
  let open Vale.X64.Print_s in
  ((print_code c1 0 gcc) = (print_code c2 0 gcc)) /-
  ("Not matching codes: \n" ^
   "\tCode:\n" ^
   fst (print_code c1 0 gcc) ^
   "\tExpected code:\n" ^
   fst (print_code c2 0 gcc) ^
   "\n")

/// Reordering transformation

(* See fsti *)
let reorder orig hint =
  transformation_result_of_possibly_codes (
    if code_modifies_ghost orig then Err "code directly modifies ghost state (via ins_Ghost instruction)" else
    let orig' = IR.purge_empty_codes [orig] in
    ts <-- IR.find_transformation_hints orig' [hint];
    transformed <-- IR.perform_reordering_with_hints ts orig';
    prints_to_same_code (Block transformed) hint;;
    return transformed
  ) orig

#push-options "--max_fuel 2 --max_ifuel 1"
let lemma_code_codes (c:code) (fuel:nat) (s:machine_state) :
  Lemma
    (ensures (machine_eval_code c fuel s == machine_eval_codes [c] fuel s)) = ()

let lemma_codes_code (c:codes) (fuel:nat) (s:machine_state) :
  Lemma
    (ensures (machine_eval_codes c fuel s == machine_eval_code (Block c) fuel s)) = ()
#pop-options

let lemma_IR_equiv_states_to_equiv_states (s1 s2:machine_state) :
  Lemma
    (requires (
        (IR.equiv_states s1 s2)))
    (ensures (
        (equiv_states (state_of_S s1) (state_of_S s2)))) = ()

(* See fsti *)
let lemma_reorder orig hint transformed va_s0 va_sM va_fM =
  if code_modifies_ghost orig then (va_sM, va_fM) else
  let orig' = IR.purge_empty_codes [orig] in
  match IR.find_transformation_hints orig' [hint] with
  | Err _ -> va_sM, va_fM
  | Ok ts ->
    match IR.perform_reordering_with_hints ts orig' with
    | Err _ -> va_sM, va_fM
    | Ok tr ->
      lemma_code_codes orig va_fM (state_to_S va_s0);
      IR.lemma_purge_empty_codes [orig] va_fM (state_to_S va_s0);
      IR.lemma_perform_reordering_with_hints ts orig' va_fM (state_to_S va_s0);
      lemma_codes_code tr va_fM (state_to_S va_s0);
      let Some s = machine_eval_code orig va_fM (state_to_S va_s0) in
      let Some s' = machine_eval_code transformed va_fM (state_to_S va_s0) in
      lemma_IR_equiv_states_to_equiv_states s s';
      assert (eval_code orig va_s0 va_fM va_sM);
      assert ({s with ms_trace = []} == (state_to_S va_sM));
      let va_sM' = state_of_S s' in
      lemma_to_of s';
      assert (state_to_S va_sM' == {s' with ms_trace = []});
      assert (state_to_S va_sM == {s with ms_trace = []});
      assert (IR.equiv_states ({s with ms_trace = []}) ({s' with ms_trace = []}));
      assert (equiv_states va_sM va_sM');
      assert (va_ensure_total transformed va_s0 va_sM' va_fM);
      va_sM', va_fM

/// Check-if-same-printed-code "transformation"

(* See fsti *)
let check_if_same_printed_code orig hint =
  {
    success = prints_to_same_code orig hint;
    result = orig;
  }

(* See fsti *)
let lemma_check_if_same_printed_code orig hint transformed va_s0 va_sM va_fM =
  va_sM, va_fM
