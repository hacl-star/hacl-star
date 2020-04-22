(**

   This module defines a control flow lowering transform, which
   eliminates all cases of [IfElse] and [While], making them
   [Unstructured] instead.

   This is generally expected the be the last transformer to be used.

*)
module Vale.Transformers.ControlFlowLowering

open Vale.X64.Machine_Semantics_s
open Vale.Transformers.InstructionReorder // open so that we don't
                                          // need to redefine
                                          // erroring_option_state
                                          // etc.

val lower_code: code -> code

val lemma_lower_code:
  c:code ->
  fuel:nat ->
  s:machine_state ->
  Lemma
    (requires (
        ~(erroring_option_state (machine_eval_code c fuel s))))
    (ensures (
        machine_eval_code c fuel s ==
        machine_eval_code (lower_code c) fuel s))
    (decreases %[fuel; c])
