module Vale.Transformers.BoundedInstructionEffects

open Vale.X64.Bytes_Code_s
open Vale.X64.Instruction_s
open Vale.X64.Instructions_s
open Vale.X64.Machine_Semantics_s
open Vale.X64.Machine_s
open Vale.X64.Print_s

open Vale.Transformers.PossiblyMonad

open Vale.Transformers.Locations
friend Vale.Transformers.Locations

module L = FStar.List.Tot

(* See fsti *)
let rw_set_of_ins i =
  match i with
  | Instr i oprs _ ->
    read_set i oprs, write_set i oprs
  | Push src t ->
    ALocReg (Reg 0 rRsp) :: both (locations_of_operand64 src),
    [ALocReg (Reg 0 rRsp); ALocStack]
  | Pop dst t ->
    ALocReg (Reg 0 rRsp) :: ALocStack :: fst (locations_of_operand64 dst),
    ALocReg (Reg 0 rRsp) :: snd (locations_of_operand64 dst)
  | Alloc _
  | Dealloc _ ->
    [ALocReg (Reg 0 rRsp)], [ALocReg (Reg 0 rRsp)]

let lemma_machine_eval_ins_st_only_affects_write_aux (i:ins{Instr? i}) (s:machine_state) (a:location) :
  Lemma
    (requires (
        let r, w = rw_set_of_ins i in
        (!!(disjoint_location_from_locations a w))))
    (ensures (
        (eval_location a s == eval_location a (run (machine_eval_ins_st i) s)))) =
  admit ()

let lemma_machine_eval_ins_st_only_affects_write (i:ins{Instr? i}) (s:machine_state) :
  Lemma
    (ensures (
       (let r, w = rw_set_of_ins i in
        (unchanged_except w s (run (machine_eval_ins_st i) s))))) =
  FStar.Classical.forall_intro (
    FStar.Classical.move_requires (lemma_machine_eval_ins_st_only_affects_write_aux i s))

let lemma_machine_eval_ins_st_unchanged_behavior (i:ins{Instr? i}) (s1 s2:machine_state) :
  Lemma
    (requires (
        let r, w = rw_set_of_ins i in
        (unchanged_at r s1 s2)))
    (ensures (
        let r, w = rw_set_of_ins i in
        let f = machine_eval_ins_st i in
        (unchanged_at w (run f s1) (run f s2)) /\
        (run f s1).ms_ok = (run f s2).ms_ok)) =
  admit ()

let lemma_machine_eval_ins_st_bounded_effects_Instr (i:ins{Instr? i}) :
  Lemma
    (ensures (
        (let r, w = rw_set_of_ins i in
         (bounded_effects r w (machine_eval_ins_st i))))) =
  FStar.Classical.forall_intro (lemma_machine_eval_ins_st_only_affects_write i);
  FStar.Classical.forall_intro_2 (fun s1 ->
      FStar.Classical.move_requires (lemma_machine_eval_ins_st_unchanged_behavior i s1))

(* See fsti *)
let lemma_machine_eval_ins_st_bounded_effects i =
  match i with
  | Instr _ _ _ -> lemma_machine_eval_ins_st_bounded_effects_Instr i
  | Push _ _ ->
    admit ()
  | Pop _ _ ->
    admit ()
  | Alloc _ ->
    admit ()
  | Dealloc _ ->
    admit ()
