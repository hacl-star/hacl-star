module X64.Vale.InsLemmas

open X64.Vale.StateLemmas
open X64.Taint_Semantics

friend X64.Vale.StateLemmas
friend X64.Vale.Decls

let lemma_valid_taint64_operand m t s =
  let open X64.Taint_Semantics_s in
  let tainted_mem:X64.Memory.memtaint = (state_to_S s).memTaint in
  let real_mem:X64.Memory.mem = s.mem in
  Util.Meta.exists_elim2
    (Map.sel tainted_mem (eval_maddr m s) == t)
    ()
    (fun (b:X64.Memory.buffer64) (index:nat{valid_maddr (eval_maddr m s) real_mem tainted_mem b index t}) ->
      lemma_valid_taint64 b tainted_mem real_mem index t)

let instr_norm_lemma (#a:Type) (x:a) : Lemma
  (x == norm [zeta; iota; delta_attr [`%instr_attr]] x)
  =
  ()

(*
let make_instr #outs #args #havoc_flags i oprs =
  let ins = S.Instr outs args havoc_flags i oprs in
  instr_norm_lemma (S.eval_ins ins);
  ins
*)
