module Vale.X64.Taint_Semantics

open FStar.Mul
open Vale.X64.Decls
open Vale.X64.Machine_s
open Vale.X64.Instruction_s
module S = Vale.X64.Machine_Semantics_s
module L = FStar.List.Tot

let normal_term_spec (#a:Type) (x:a) : Lemma (normal x == x) =
  ()

let mk_ins (i:S.ins) : Pure S.code
  (requires True)
  (ensures fun c ->
    c == Ins i /\
    i == normal i /\
    S.machine_eval_ins_st i == normal (S.machine_eval_ins_st i)
  )
  =
  normal_term_spec (S.machine_eval_ins_st i);
  Ins i

