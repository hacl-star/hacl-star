(**

   This module defines a framework for peephole transformers. It needs
   to be instantiated with an actual pattern to generate a verified
   peephole transform. In particular, it needs to be provided a
   [peephole], and an [input_hint] to obtain a new transformer.

   A [peephole] is a function that converts a list of instructions
   into (optionally) another list of instructions. It must be proven
   correct wrt preservation of semantics. The [input_hint] is just a
   hint to say how many instructions it takes as input.

   Usage:

     let test = peephole_transform test_ih test_ph
     let lemma_test = lemma_peephole_transform test_ih test_ph

*)
module Vale.Transformers.PeepHole

open Vale.Transformers.Common


open Vale.X64.Decls
open Vale.X64.Lemmas
open Vale.X64.StateLemmas
open Vale.Transformers.Common

open Vale.X64.Bytes_Code_s
open Vale.X64.Instruction_s
open Vale.X64.Instructions_s
open Vale.X64.Machine_Semantics_s
open Vale.X64.Machine_s
open Vale.X64.Print_s

module L = FStar.List.Tot

open Vale.Transformers.InstructionReorder // open so that we don't
                                          // need to redefine things
                                          // equivalence etc.

open Vale.X64.InsLemmas

/// Define what a peephole means, and what it means to be correct.

type pre_peephole = list ins -> Tot (option (list ins))

let rec eval_inss (is:list ins) (s:machine_state) : GTot machine_state =
  match is with
  | [] -> s
  | i :: is' -> eval_inss is' (machine_eval_ins i s)

let peephole_correct (p:pre_peephole) (is:list ins) (s:machine_state) : GTot Type0 =
  match p is with
  | None -> True
  | Some is' ->
    equiv_states_or_both_not_ok
      (eval_inss is s)
      (eval_inss is' s)

type peephole = (p:pre_peephole{forall is s. {:pattern (peephole_correct p is s)}
                                  peephole_correct p is s})

/// Now, for the pièce de résistance, functions that give you
/// something you can directly use as transformers!

val peephole_transform :
  input_hint:pos -> p:peephole ->
  orig:va_code ->
  va_transformation_result

val lemma_peephole_transform :
  input_hint:pos -> p:peephole ->
  orig:va_code ->
  transformed:va_code ->
  va_s0:va_state -> va_sM:va_state -> va_fM:va_fuel ->
  Ghost (va_state & va_fuel)
    (requires (
        (va_require_total transformed (peephole_transform input_hint p orig).result va_s0) /\
        (va_get_ok va_s0) /\
        (va_ensure_total orig va_s0 va_sM va_fM) /\
        (va_get_ok va_sM)))
    (ensures (fun (va_sM', va_fM') ->
         (va_fM' == va_fM) /\
         (Vale.Transformers.Common.equiv_states va_sM va_sM') /\
         (va_ensure_total transformed va_s0 va_sM' va_fM') /\
         (va_get_ok va_sM')))


/// Common useful lemmas/definitions

let coerce_to_normal (#a:Type0) (x:a) : y:(normal a){x == y} = x
