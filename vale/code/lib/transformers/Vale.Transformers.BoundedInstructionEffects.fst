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


let locations_of_maddr (m:maddr) : locations =
  match m with
  | MConst _ -> []
  | MReg r _ -> [ALocReg r]
  | MIndex b _ i _ -> [ALocReg b; ALocReg i]

let locations_of_operand64 (o:operand64) : locations & locations =
  match o with
  | OConst _ -> [], []
  | OReg r -> [ALocReg (Reg 0 r)], [ALocReg (Reg 0 r)]
  | OMem (m, _) -> locations_of_maddr m, [ALocMem]
  | OStack (m, _) -> locations_of_maddr m, [ALocStack]

let locations_of_operand128 (o:operand128) : locations & locations =
  match o with
  | OConst _ -> [], []
  | OReg r -> [ALocReg (Reg 1 r)], [ALocReg (Reg 1 r)]
  | OMem (m, _) -> locations_of_maddr m, [ALocMem]
  | OStack (m, _) -> locations_of_maddr m, [ALocStack]

let locations_of_explicit (t:instr_operand_explicit) (i:instr_operand_t t) : locations & locations =
  match t with
  | IOp64 -> locations_of_operand64 i
  | IOpXmm -> locations_of_operand128 i

let locations_of_implicit (t:instr_operand_implicit) : locations & locations =
  match t with
  | IOp64One i -> locations_of_operand64 i
  | IOpXmmOne i -> locations_of_operand128 i
  | IOpFlagsCf -> [ALocCf], [ALocCf]
  | IOpFlagsOf -> [ALocOf], [ALocOf]

let both (x: locations & locations) =
  let a, b = x in
  a `L.append` b

let rec aux_read_set0 (args:list instr_operand) (oprs:instr_operands_t_args args) : locations =
  match args with
  | [] -> []
  | (IOpEx i) :: args ->
    let l, r = coerce #(instr_operand_t i & instr_operands_t_args args) oprs in
    both (locations_of_explicit i l) `L.append` aux_read_set0 args r
  | (IOpIm i) :: args ->
    both (locations_of_implicit i) `L.append` aux_read_set0 args (coerce #(instr_operands_t_args args) oprs)

let rec aux_read_set1
    (outs:list instr_out) (args:list instr_operand) (oprs:instr_operands_t outs args) : locations =
  match outs with
  | [] -> aux_read_set0 args oprs
  | (Out, IOpEx i) :: outs ->
    let l, r = coerce #(instr_operand_t i & instr_operands_t outs args) oprs in
    fst (locations_of_explicit i l) `L.append` aux_read_set1 outs args r
  | (InOut, IOpEx i) :: outs ->
    let l, r = coerce #(instr_operand_t i & instr_operands_t outs args) oprs in
    both (locations_of_explicit i l) `L.append` aux_read_set1 outs args r
  | (Out, IOpIm i) :: outs ->
    fst (locations_of_implicit i) `L.append` aux_read_set1 outs args (coerce #(instr_operands_t outs args) oprs)
  | (InOut, IOpIm i) :: outs ->
    both (locations_of_implicit i) `L.append` aux_read_set1 outs args (coerce #(instr_operands_t outs args) oprs)

let read_set (i:instr_t_record) (oprs:instr_operands_t i.outs i.args) : locations =
  aux_read_set1 i.outs i.args oprs

let rec aux_write_set
    (outs:list instr_out) (args:list instr_operand) (oprs:instr_operands_t outs args) : locations =
  match outs with
  | [] -> []
  | (_, IOpEx i) :: outs ->
    let l, r = coerce #(instr_operand_t i & instr_operands_t outs args) oprs in
    snd (locations_of_explicit i l) `L.append` aux_write_set outs args r
  | (_, IOpIm i) :: outs ->
    snd (locations_of_implicit i) `L.append` aux_write_set outs args (coerce #(instr_operands_t outs args) oprs)

let write_set (i:instr_t_record) (oprs:instr_operands_t i.outs i.args) : list location =
  let InstrTypeRecord #outs #args #havoc_flags _ = i in
  let ws = aux_write_set outs args oprs in
  match havoc_flags with
  | HavocFlags -> ALocCf :: ALocOf :: ws
  | PreserveFlags -> ws

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

#push-options "--z3rlimit 20 --max_fuel 2 --max_ifuel 1"
let rec lemma_instr_write_outputs_only_affects_write
    (outs:list instr_out) (args:list instr_operand)
    (vs:instr_ret_t outs) (oprs:instr_operands_t outs args) (s_orig s:machine_state)
    (a:location) :
  Lemma
    (requires (
        let w = aux_write_set outs args oprs in
        !!(disjoint_location_from_locations a w)))
    (ensures (
        (eval_location a s == eval_location a (instr_write_outputs outs args vs oprs s_orig s)))) =
  match outs with
  | [] -> ()
  | (_, i) :: outs -> (
      let ((v:instr_val_t i), (vs:instr_ret_t outs)) =
        match outs with
        | [] -> (vs, ())
        | _::_ -> let vs = coerce vs in (fst vs, snd vs)
        in
      match i with
      | IOpEx i ->
        let oprs = coerce oprs in
        let s = instr_write_output_explicit i v (fst oprs) s_orig s in
        lemma_instr_write_outputs_only_affects_write outs args vs (snd oprs) s_orig s a
      | IOpIm i ->
        let s = instr_write_output_implicit i v s_orig s in
        lemma_instr_write_outputs_only_affects_write outs args vs (coerce oprs) s_orig s a
    )
#pop-options

let lemma_eval_instr_only_affects_write
    (it:instr_t_record) (oprs:instr_operands_t it.outs it.args) (ann:instr_annotation it)
    (s0:machine_state)
    (a:location) :
  Lemma
    (requires (
        (let r, w = rw_set_of_ins (Instr it oprs ann) in
         !!(disjoint_location_from_locations a w) /\
         (Some? (eval_instr it oprs ann s0)))))
    (ensures (
        (eval_location a s0 == eval_location a (Some?.v (eval_instr it oprs ann s0))))) =
  let r, w = rw_set_of_ins (Instr it oprs ann) in
  let InstrTypeRecord #outs #args #havoc_flags' i = it in
  let vs = instr_apply_eval outs args (instr_eval i) oprs s0 in
  let s1 =
    match havoc_flags' with
    | HavocFlags -> {s0 with ms_flags = havoc_flags}
    | PreserveFlags -> s0
  in
  let Some vs = vs in
  let _ = instr_write_outputs outs args vs oprs s0 s1 in
  lemma_instr_write_outputs_only_affects_write outs args vs oprs s0 s1 a

let lemma_machine_eval_ins_st_only_affects_write_aux (i:ins{Instr? i}) (s:machine_state) (a:location) :
  Lemma
    (requires (
        let r, w = rw_set_of_ins i in
        (!!(disjoint_location_from_locations a w))))
    (ensures (
        (eval_location a s == eval_location a (run (machine_eval_ins_st i) s)))) =
  let Instr it oprs ann = i in
  match eval_instr it oprs ann s with
  | Some _ -> lemma_eval_instr_only_affects_write it oprs ann s a
  | None -> ()

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
