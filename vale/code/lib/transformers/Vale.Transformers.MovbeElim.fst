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

let movbe_elim_ph = {
  ph = (function
      | [Instr i oprs (AnnotateMovbe64 proof_of_movbe)] ->
        let oprs:normal (instr_operands_t [out op64] [op64]) =
          coerce_to_normal #(instr_operands_t [out op64] [op64]) oprs in
        let (dst, (src, ())) = oprs in
        if OReg? dst then (
          let mov = make_instr ins_Mov64 dst src in
          let bswap = make_instr ins_Bswap64 dst in
          Some [mov; bswap]
        ) else None
      | _ -> None);
  input_hint = 1;
}

module T = Vale.Def.Types_s
module H = Vale.Arch.Heap

#push-options "--initial_fuel 2 --max_fuel 2 --initial_ifuel 0 --max_ifuel 0"
let lemma_movbe_is_mov_bswap (dst src:operand64) (s:machine_state) :
  Lemma
    (requires (OReg? dst))
    (ensures (
        let movbe = make_instr_annotate ins_MovBe64 (AnnotateMovbe64 ()) dst src in
        let mov = make_instr ins_Mov64 dst src in
        let bswap = make_instr ins_Bswap64 dst in
        let s1 = machine_eval_ins movbe s in
        let s2 = machine_eval_ins bswap (machine_eval_ins mov s) in
        s1.ms_ok ==> equiv_states s1 s2)) =
  let movbe = make_instr_annotate ins_MovBe64 (AnnotateMovbe64 ()) dst src in
  let mov = make_instr ins_Mov64 dst src in
  let bswap = make_instr ins_Bswap64 dst in
  let s_movbe = machine_eval_ins movbe s in
  let s_mov = machine_eval_ins mov s in
  let s_bswap = machine_eval_ins bswap s_mov in
  if valid_src_operand64_and_taint src s && valid_dst_operand64 dst s then (
    let src_v = eval_operand src s in
    let dst_movbe_v = T.reverse_bytes_nat64 src_v in
    let dst_mov_v = eval_operand dst s_mov in
    let dst_bswap_v = T.reverse_bytes_nat64 dst_mov_v in
    if s_movbe.ms_ok then (
      assert (Vale.X64.CPU_Features_s.movbe_enabled);
      assert (s_movbe == update_operand64_preserve_flags'' dst dst_movbe_v s s);
      assert (s_mov == update_operand64_preserve_flags'' dst src_v s s);
      lemma_update_to_valid_destination_keeps_it_as_valid_src dst s src_v;
      assert (eval_operand dst s_mov == src_v);
      assert (valid_src_operand64_and_taint dst s_mov);
      assert (s_bswap == update_operand64_preserve_flags'' dst dst_bswap_v s_mov s_mov);
      assert (src_v == dst_mov_v);
      assert (dst_movbe_v == dst_bswap_v);
      lemma_double_update_reg dst s s_mov s_bswap s_movbe src_v dst_bswap_v
    ) else ()
  ) else (
    assert (s_movbe == {s with ms_ok = false});
    assert (s_mov == {s with ms_ok = false});
    assert (s_bswap.ms_ok == false)
  )
#pop-options

#push-options "--initial_fuel 3 --max_fuel 3 --initial_ifuel 0 --max_ifuel 0"
let movbe_elim_correct (is:list ins) (s:machine_state) :
  Lemma (peephole_correct movbe_elim_ph is s)
    [SMTPat (peephole_correct movbe_elim_ph is s)] =
  match is with
  | [Instr i oprs (AnnotateMovbe64 proof_of_movbe)] ->
    let oprs:normal (instr_operands_t [out op64] [op64]) =
      coerce_to_normal #(instr_operands_t [out op64] [op64]) oprs in
    let (dst, (src, ())) = oprs in
    if OReg? dst then (
      let Some is' = movbe_elim_ph.ph is in
      lemma_movbe_is_mov_bswap dst src s
    ) else ()
  | _ -> ()
#pop-options
