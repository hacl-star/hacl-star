(**

   This module defines a framework for peephole transformers. It needs
   to be instantiated with an actual pattern to generate a verified
   peephole transform. In particular, it needs to be provided a
   [peephole], and an [input_hint] to obtain a new transformer.

   A [peephole] is a function that converts a list of instructions
   into (optionally) another list of instructions.

   Usage:
     let foo = peephole_transform foo_ph
     let lemma_foo = lemma_peephole_transform foo_ph

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

noeq
type pre_peephole = {
  ph: list ins -> Tot (option (list ins)); // The actual peephole transformer
  input_hint: pos; // The number of instructions it takes as input to transform
}

let rec eval_inss (is:list ins) (s:machine_state) : GTot machine_state =
  match is with
  | [] -> s
  | i :: is' -> eval_inss is' (machine_eval_ins i s)

let peephole_correct (p:pre_peephole) (is:list ins) (s:machine_state) : GTot Type0 =
  match p.ph is with
  | None -> True
  | Some is' ->
    let s1 = eval_inss is s in
    let s2 = eval_inss is' s in
    s1.ms_ok ==> equiv_states s1 s2

type peephole = (p:pre_peephole{forall is s. {:pattern (peephole_correct p is s)}
                                  peephole_correct p is s})

/// Now, for the pièce de résistance, functions that give you
/// something you can directly use as transformers!

val peephole_transform :
  p:peephole ->
  orig:va_code ->
  va_transformation_result

val lemma_peephole_transform :
  p:peephole ->
  orig:va_code ->
  transformed:va_code ->
  va_s0:va_state -> va_sM:va_state -> va_fM:va_fuel ->
  Ghost (va_state & va_fuel)
    (requires (
        (va_require_total transformed (peephole_transform p orig).result va_s0) /\
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

#push-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0 --initial_ifuel 2 --max_ifuel 2 --z3cliopt smt.arith.nl=true"
let lemma_update_to_valid_destination_keeps_it_as_valid_src (o:operand64) (s:machine_state) (v:nat64) :
  Lemma
    (requires (valid_dst_operand64 o s))
    (ensures (
        let s' = update_operand64_preserve_flags'' o v s s in
        valid_src_operand64_and_taint o s' /\
        eval_operand o s' == v)) =
  reveal_opaque (`%valid_addr64) valid_addr64;
  update_heap64_reveal ();
  get_heap_val64_reveal ()
#pop-options

let lemma_double_update_reg (dst:operand64) (s0 s1 s2 s3:machine_state) (v v_fin:nat64) :
  Lemma
    (requires (
        (OReg? dst) /\
        (valid_dst_operand64 dst s0) /\
        (s1 == update_operand64_preserve_flags'' dst v s0 s0) /\
        (s2 == update_operand64_preserve_flags'' dst v_fin s1 s1) /\
        (s3 == update_operand64_preserve_flags'' dst v_fin s0 s0)))
    (ensures (
        equiv_states s2 s3)) =
  match dst with
  | OReg r -> assert (equiv_states_ext s2 s3) (* OBSERVE *)
