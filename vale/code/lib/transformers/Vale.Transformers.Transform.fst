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

(* See fsti *)
let lemma_reorder orig hint transformed va_s0 va_sM va_fM =
  match Vale.Transformers.InstructionReorder.reordering_allowed [orig] [hint] with
  | Ok () -> (
      admit ()
    )
  | Err reason -> va_sM, va_fM
