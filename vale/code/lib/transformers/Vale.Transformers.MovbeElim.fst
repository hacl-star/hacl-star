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

let movbe_elim_input_hint : pos = 1

let movbe_elim_ph (is:list ins) : Tot (option (list ins)) =
  match is with
  | [Instr i oprs (AnnotateMovbe64 proof_of_movbe)] ->
    let oprs:normal (instr_operands_t [out op64] [op64]) =
      coerce_to_normal #(instr_operands_t [out op64] [op64]) oprs in
    let (dst, (src, ())) = oprs in
    if OReg? dst then (
      let mov = make_instr ins_Mov64 dst src in
      let bswap = make_instr ins_Bswap64 dst in
      Some [mov; bswap]
    ) else None
  | _ -> None

module T = Vale.Def.Types_s
module H = Vale.Arch.Heap

#push-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0 --initial_ifuel 2 --max_ifuel 2"
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

#push-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"
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
#pop-options

#push-options "--initial_fuel 2 --max_fuel 2 --initial_ifuel 0 --max_ifuel 0"
let lemma_movbe_is_mov_bswap (dst src:operand64) (s:machine_state) :
  Lemma
    (requires (OReg? dst))
    (ensures (
        let movbe = make_instr_annotate ins_MovBe64 (AnnotateMovbe64 ()) dst src in
        let mov = make_instr ins_Mov64 dst src in
        let bswap = make_instr ins_Bswap64 dst in
        equiv_states_or_both_not_ok
          (machine_eval_ins movbe s)
          (machine_eval_ins bswap (machine_eval_ins mov s)))) =
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
    assume (Vale.X64.CPU_Features_s.movbe_enabled);
    assert (s_movbe == update_operand64_preserve_flags'' dst dst_movbe_v s s); // this fails now, because there is a "movbe_enabled" check on movbe
    assert (s_mov == update_operand64_preserve_flags'' dst src_v s s);
    lemma_update_to_valid_destination_keeps_it_as_valid_src dst s src_v;
    assert (eval_operand dst s_mov == src_v);
    assert (valid_src_operand64_and_taint dst s_mov);
    assert (s_bswap == update_operand64_preserve_flags'' dst dst_bswap_v s_mov s_mov);
    assert (src_v == dst_mov_v);
    assert (dst_movbe_v == dst_bswap_v);
    lemma_double_update_reg dst s s_mov s_bswap s_movbe src_v dst_bswap_v
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
      let Some is' = movbe_elim_ph is in
      lemma_movbe_is_mov_bswap dst src s
    ) else ()
  | _ -> ()
#pop-options
