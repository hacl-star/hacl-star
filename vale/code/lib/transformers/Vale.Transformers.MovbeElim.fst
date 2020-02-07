module Vale.Transformers.MovbeElim

open Vale.X64.Bytes_Code_s
open Vale.X64.Instruction_s
open Vale.X64.Instructions_s
open Vale.X64.Machine_Semantics_s
open Vale.X64.Machine_s
open Vale.X64.Print_s
open Vale.Transformers.InstructionReorder
open Vale.X64.InsLemmas

open Vale.Transformers.PeepHole

let movbe_elim_ph (is:list ins) : Tot (option (list ins)) =
  None (* Safe, but currently behaves as a no-op due to this *)

let movbe_elim_correct (is:list ins) (s:machine_state) :
  Lemma (peephole_correct movbe_elim_ph is s)
    [SMTPat (peephole_correct movbe_elim_ph is s)] =
  ()

let movbe_elim_input_hint : pos = 1
