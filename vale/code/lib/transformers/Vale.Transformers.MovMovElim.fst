module Vale.Transformers.MovMovElim

open Vale.X64.Bytes_Code_s
open Vale.X64.Instruction_s
open Vale.X64.Instructions_s
open Vale.X64.Machine_Semantics_s
open Vale.X64.Machine_s
open Vale.X64.Print_s
open Vale.Def.PossiblyMonad
open Vale.Transformers.InstructionReorder
open Vale.X64.InsLemmas

open Vale.Transformers.PeepHole

let safe_mov_mov_elim (is:list ins) : Tot bool =
  match is with
  | [Instr i1 oprs1 (AnnotateMov64 ()); Instr i2 oprs2 (AnnotateMov64 ())] ->
    let oprs1:normal (instr_operands_t [out op64] [op64]) =
      coerce_to_normal #(instr_operands_t [out op64] [op64]) oprs1 in
    let oprs2:normal (instr_operands_t [out op64] [op64]) =
      coerce_to_normal #(instr_operands_t [out op64] [op64]) oprs2 in
    let (dst1, (src1, ())) = oprs1 in
    let (dst2, (src2, ())) = oprs2 in
    dst1 = dst2 && OReg? dst1 && (
      let OReg rd = dst1 in
      match src2 with
      | OConst _ -> true
      | OReg rs2 -> not (rs2 = rd)
      | OStack (m, _) | OMem (m, _, _) ->
        match m with
        | MConst _ -> true
        | _ -> false // TODO: Can we relax this restriction?
    )
  | _ -> false

let mov_mov_elim_ph = {
  ph = (fun is ->
      if safe_mov_mov_elim is then (
        let [i1; i2] = is in
        Some [i2]
      ) else None);
  input_hint = 2;
}

module T = Vale.Def.Types_s
module H = Vale.Arch.Heap

#push-options "--initial_fuel 2 --max_fuel 8 --initial_ifuel 1 --max_ifuel 2 --query_stats"
let lemma_mov_mov_is_mov (i1 i2:ins) (s:machine_state) :
  Lemma
    (requires (safe_mov_mov_elim [i1; i2]))
    (ensures (
        let s1 = machine_eval_ins i2 (machine_eval_ins i1 s) in
        let s2 = machine_eval_ins i2 s in
        s1.ms_ok ==> equiv_states s1 s2)) =
  let Instr ii1 oprs1 (AnnotateMov64 ()) = i1 in
  let Instr ii2 oprs2 (AnnotateMov64 ()) = i2 in
  let oprs1:normal (instr_operands_t [out op64] [op64]) =
    coerce_to_normal #(instr_operands_t [out op64] [op64]) oprs1 in
  let oprs2:normal (instr_operands_t [out op64] [op64]) =
    coerce_to_normal #(instr_operands_t [out op64] [op64]) oprs2 in
  let (dst1, (src1, ())) = oprs1 in
  let (dst2, (src2, ())) = oprs2 in
  let dst = assert (dst1 == dst2); dst1 in
  let pre_s1 = machine_eval_ins i1 s in
  let s1 = machine_eval_ins i2 pre_s1 in
  let s2 = machine_eval_ins i2 s in
  if s1.ms_ok then (
    assert (pre_s1.ms_ok);
    let v1 = eval_operand src1 s in
    let v2' = eval_operand src2 s in
    let v2 = eval_operand src2 pre_s1 in
    assert (v2 == v2');
    lemma_double_update_reg dst s pre_s1 s1 s2 v1 v2
  ) else ()

#pop-options

#push-options "--initial_fuel 3 --max_fuel 3 --initial_ifuel 0 --max_ifuel 0"
let mov_mov_elim_correct (is:list ins) (s:machine_state) :
  Lemma (peephole_correct mov_mov_elim_ph is s)
    [SMTPat (peephole_correct mov_mov_elim_ph is s)] =
  if safe_mov_mov_elim is then (
    let [i1; i2] = is in
    lemma_mov_mov_is_mov i1 i2 s
  ) else ()
#pop-options
