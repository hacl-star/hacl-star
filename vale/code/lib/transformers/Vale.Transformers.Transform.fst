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

let lemma_aux_reorder orig hint s_init s_final1 s_final2 fuel :
  Lemma
    (requires (
        (eval_code orig s_init fuel s_final1) /\
        (eval_code (reorder orig hint).result s_init fuel s_final2)))
    (ensures (
        (equiv_states s_final1 s_final2))) =
  let res = reorder orig hint in
  let success, result = res.success, res.result in
  match success with
  | Ok () -> (
      admit ()
    )
  | Err _ -> (
      assert (state_eq_opt (BS.machine_eval_code orig fuel (state_to_S s_init)) (Some (state_to_S s_final1)));
      assert (state_eq_opt (BS.machine_eval_code orig fuel (state_to_S s_init)) (Some (state_to_S s_final2)));
      assert (state_eq_S (state_to_S s_final1) (state_to_S s_final2));
      assert ((state_to_S s_final1) == (state_to_S s_final2));
      //
      assert (s_final1.vs_ok = s_final2.vs_ok);
      assert (Vale.X64.Regs.equal s_final1.vs_regs s_final2.vs_regs);
      assert (Vale.X64.Flags.sel fCarry s_final1.vs_flags == Vale.X64.Flags.sel fCarry s_final2.vs_flags);
      assert (Vale.X64.Flags.sel fOverflow s_final1.vs_flags == Vale.X64.Flags.sel fOverflow s_final2.vs_flags);
      assume (s_final1.vs_heap == s_final2.vs_heap); (* Why?! *)
      assume (s_final1.vs_stack == s_final2.vs_stack); (* Why?! *)
      assert (s_final1.vs_memTaint == s_final2.vs_memTaint);
      assert (s_final1.vs_stackTaint == s_final2.vs_stackTaint);
      assert (equiv_states s_final1 s_final2)
    )

(* See fsti *)
let lemma_reorder orig hint =
  let aux s_init s_final1 s_final2 = FStar.Classical.move_requires (lemma_aux_reorder orig hint s_init s_final1 s_final2) in
  FStar.Classical.forall_intro_4 aux
