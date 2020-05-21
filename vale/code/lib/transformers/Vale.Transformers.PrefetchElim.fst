module Vale.Transformers.PrefetchElim

open Vale.X64.Bytes_Code_s
open Vale.X64.Instruction_s
open Vale.X64.Instructions_s
open Vale.X64.Machine_Semantics_s
open Vale.X64.Machine_s
open Vale.X64.Print_s
open Vale.Transformers.InstructionReorder
open Vale.X64.InsLemmas

open Vale.Transformers.PeepHole

let prefetch_elim_ph = {
  ph = (function
      | [Instr i oprs (AnnotatePrefetchnta ())] ->
        Some []
      | _ -> None);
  input_hint = 1;
}

#push-options "--fuel 2 --ifuel 3"
let prefetch_elim_correct (is:list ins) (s:machine_state) :
  Lemma (peephole_correct prefetch_elim_ph is s)
    [SMTPat (peephole_correct prefetch_elim_ph is s)] =
  match is with
  | [Instr i oprs (AnnotatePrefetchnta ())] -> ()
  | _ -> ()
#pop-options
