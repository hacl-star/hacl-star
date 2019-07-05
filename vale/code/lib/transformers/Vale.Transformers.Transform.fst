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

(* See fsti *)
let reorder orig hint =
  match Vale.Transformers.InstructionReorder.reordering_allowed [orig] [hint] with
  | Ok () -> {
      success = ttrue;
      result = Block (Vale.Transformers.InstructionReorder.perform_reordering [orig] [hint])
    }
  | Err reason -> {
      success = ffalse reason;
      result = orig;
    }

#push-options "--max_fuel 2 --max_ifuel 1"
let lemma_code_codes (c:code) (fuel:nat) (s:machine_state) :
  Lemma
    (ensures (machine_eval_code c fuel s == machine_eval_codes [c] fuel s)) = ()

let lemma_codes_code (c:codes) (fuel:nat) (s:machine_state) :
  Lemma
    (ensures (machine_eval_codes c fuel s == machine_eval_code (Block c) fuel s)) = ()
#pop-options

(* See fsti *)
let lemma_reorder orig hint transformed va_s0 va_sM va_fM =
  match Vale.Transformers.InstructionReorder.reordering_allowed [orig] [hint] with
  | Ok () -> (
      lemma_code_codes orig va_fM (state_to_S va_s0);
      Vale.Transformers.InstructionReorder.lemma_reordering [orig] [hint] va_fM (state_to_S va_s0);
      lemma_codes_code (Vale.Transformers.InstructionReorder.perform_reordering [orig] [hint]) va_fM (state_to_S va_s0);
      let Some s' = machine_eval_code transformed va_fM (state_to_S va_s0) in
      assume (same_domain va_sM s');
      let va_sM' = state_of_S va_sM s' in
      assume (equiv_states va_sM va_sM');
      assume (va_ensure_total transformed va_s0 va_sM' va_fM);
      va_sM', va_fM
    )
  | Err reason -> va_sM, va_fM
