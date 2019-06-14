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


let locations_of_maddr (m:maddr) (mem:location) : locations =
  mem :: (
    match m with
    | MConst _ -> []
    | MReg r _ -> [ALocReg r]
    | MIndex b _ i _ -> [ALocReg b; ALocReg i]
  )

let locations_of_operand64 (o:operand64) : locations & locations =
  match o with
  | OConst _ -> [], []
  | OReg r -> [ALocReg (Reg 0 r)], [ALocReg (Reg 0 r)]
  | OMem (m, _) -> locations_of_maddr m ALocMem, [ALocMem]
  | OStack (m, _) -> (ALocReg (Reg 0 rRsp)) :: locations_of_maddr m ALocStack, [ALocStack]

let locations_of_operand128 (o:operand128) : locations & locations =
  match o with
  | OConst _ -> [], []
  | OReg r -> [ALocReg (Reg 1 r)], [ALocReg (Reg 1 r)]
  | OMem (m, _) -> locations_of_maddr m ALocMem, [ALocMem]
  | OStack (m, _) -> (ALocReg (Reg 0 rRsp)) :: locations_of_maddr m ALocStack, [ALocStack]

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
    ALocReg (Reg 0 rRsp) :: ALocStack :: both (locations_of_operand64 src),
    [ALocReg (Reg 0 rRsp); ALocStack]
  | Pop dst t ->
    ALocReg (Reg 0 rRsp) :: ALocStack :: fst (locations_of_operand64 dst),
    ALocReg (Reg 0 rRsp) :: snd (locations_of_operand64 dst)
  | Alloc _ ->
    [ALocReg (Reg 0 rRsp)], [ALocReg (Reg 0 rRsp)]
  | Dealloc _ ->
    [ALocStack; ALocReg (Reg 0 rRsp)], [ALocStack; ALocReg (Reg 0 rRsp)]

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

let lemma_instr_eval_operand_explicit_same_read_both
    (i:instr_operand_explicit) (o:instr_operand_t i)
    (s1 s2:machine_state) :
  Lemma
    (requires (
        (unchanged_at (both (locations_of_explicit i o)) s1 s2)))
    (ensures (
        (instr_eval_operand_explicit i o s1) ==
        (instr_eval_operand_explicit i o s2))) = ()

let lemma_instr_eval_operand_implicit_same_read_both
    (i:instr_operand_implicit)
    (s1 s2:machine_state) :
  Lemma
    (requires (
        (unchanged_at (both (locations_of_implicit i)) s1 s2)))
    (ensures (
        (instr_eval_operand_implicit i s1) ==
        (instr_eval_operand_implicit i s2))) = ()

let rec lemma_unchanged_at_append (l1 l2:locations) (s1 s2:machine_state) :
  Lemma
    (ensures (
        (unchanged_at (l1 `L.append` l2) s1 s2) <==>
        (unchanged_at l1 s1 s2 /\ unchanged_at l2 s1 s2))) =
  match l1 with
  | [] -> ()
  | x :: xs ->
    lemma_unchanged_at_append xs l2 s1 s2

let rec lemma_instr_apply_eval_args_same_read
    (outs:list instr_out) (args:list instr_operand)
    (f:instr_args_t outs args) (oprs:instr_operands_t_args args)
    (s1 s2:machine_state) :
  Lemma
    (requires (unchanged_at (aux_read_set0 args oprs) s1 s2))
    (ensures (
        (instr_apply_eval_args outs args f oprs s1) ==
        (instr_apply_eval_args outs args f oprs s2))) =
  match args with
  | [] -> ()
  | i :: args ->
    let (v1, v2, oprs) : option _ & option _ & instr_operands_t_args args =
      match i with
      | IOpEx i ->
        let oprs = coerce oprs in
        lemma_unchanged_at_append (both (locations_of_explicit i (fst oprs))) (aux_read_set0 args (snd oprs)) s1 s2;
        lemma_instr_eval_operand_explicit_same_read_both i (fst oprs) s1 s2;
        (instr_eval_operand_explicit i (fst oprs) s1,
         instr_eval_operand_explicit i (fst oprs) s2,
         snd oprs)
      | IOpIm i ->
        let oprs = coerce oprs in
        lemma_unchanged_at_append (both (locations_of_implicit i)) (aux_read_set0 args oprs) s1 s2;
        lemma_instr_eval_operand_implicit_same_read_both i s1 s2;
        (instr_eval_operand_implicit i s1,
         instr_eval_operand_implicit i s2,
         coerce oprs)
    in
    assert (v1 == v2);
    let f:arrow (instr_val_t i) (instr_args_t outs args) = coerce f in
    let _ = bind_option v1 (fun v -> instr_apply_eval_args outs args (f v) oprs s1) in
    let _ = bind_option v2 (fun v -> instr_apply_eval_args outs args (f v) oprs s2) in
    match v1 with
    | None -> ()
    | Some v ->
      lemma_instr_apply_eval_args_same_read outs args (f v) oprs s1 s2

#push-options "--z3rlimit 25 --initial_fuel 6 --max_fuel 6 --initial_ifuel 2 --max_ifuel 2"
let rec lemma_instr_apply_eval_inouts_same_read
    (outs inouts:list instr_out) (args:list instr_operand)
    (f:instr_inouts_t outs inouts args) (oprs:instr_operands_t inouts args)
    (s1 s2:machine_state) :
  Lemma
    (requires (unchanged_at (aux_read_set1 inouts args oprs) s1 s2))
    (ensures (
        (instr_apply_eval_inouts outs inouts args f oprs s1) ==
        (instr_apply_eval_inouts outs inouts args f oprs s2))) =
  match inouts with
  | [] ->
    lemma_instr_apply_eval_args_same_read outs args f oprs s1 s2
  | (Out, i)::inouts ->
    let oprs =
      match i with
      | IOpEx i -> snd #(instr_operand_t i) (coerce oprs)
      | IOpIm i -> coerce oprs
    in
    lemma_instr_apply_eval_inouts_same_read outs inouts args (coerce f) oprs s1 s2
  | (InOut, i)::inouts ->
    let (v1, v2, oprs) : option _ & option _ & instr_operands_t inouts args =
      match i with
      | IOpEx i ->
        let oprs = coerce oprs in
        lemma_unchanged_at_append (both (locations_of_explicit i (fst oprs))) (aux_read_set1 inouts args (snd oprs)) s1 s2;
        lemma_instr_eval_operand_explicit_same_read_both i (fst oprs) s1 s2;
        (instr_eval_operand_explicit i (fst oprs) s1,
         instr_eval_operand_explicit i (fst oprs) s2,
         snd oprs)
      | IOpIm i ->
        lemma_instr_eval_operand_implicit_same_read_both i s1 s2;
        (instr_eval_operand_implicit i s1,
         instr_eval_operand_implicit i s2,
         coerce oprs)
    in
    assert (v1 == v2);
    let f:arrow (instr_val_t i) (instr_inouts_t outs inouts args) = coerce f in
    let _ = bind_option v1 (fun v -> instr_apply_eval_inouts outs inouts args (f v) oprs s1) in
    let _ = bind_option v2 (fun v -> instr_apply_eval_inouts outs inouts args (f v) oprs s2) in
    match v1 with
    | None -> ()
    | Some v ->
      lemma_instr_apply_eval_inouts_same_read outs inouts args (f v) oprs s1 s2
#pop-options

let lemma_instr_apply_eval_same_read
    (outs:list instr_out) (args:list instr_operand)
    (f:instr_eval_t outs args) (oprs:instr_operands_t outs args)
    (s1 s2:machine_state) :
  Lemma
    (requires (unchanged_at (aux_read_set1 outs args oprs) s1 s2))
    (ensures (
        (instr_apply_eval outs args f oprs s1) ==
        (instr_apply_eval outs args f oprs s2))) =
  lemma_instr_apply_eval_inouts_same_read outs outs args f oprs s1 s2

let unchanged_at' (l:locations) (s1 s2:machine_state) =
  (s1.ms_ok = s2.ms_ok) /\
  (s1.ms_ok /\ s2.ms_ok ==>
   unchanged_at l s1 s2)

#push-options "--z3rlimit 15 --initial_fuel 4 --max_fuel 4 --initial_ifuel 2 --max_ifuel 2"
let lemma_instr_write_output_explicit_only_writes
    (i:instr_operand_explicit) (v:instr_val_t (IOpEx i)) (o:instr_operand_t i)
    (s_orig1 s1 s_orig2 s2:machine_state) :
  Lemma
    (requires (
        (unchanged_at (fst (locations_of_explicit i o)) s_orig1 s_orig2) /\
        (unchanged_at' (fst (locations_of_explicit i o)) s1 s2)))
    (ensures (
        let s1', s2' =
          instr_write_output_explicit i v o s_orig1 s1,
          instr_write_output_explicit i v o s_orig2 s2 in
        let locs = snd (locations_of_explicit i o) in
        (unchanged_at' locs s1' s2' /\
         unchanged_except locs s1 s1' /\
         unchanged_except locs s2 s2'))) = ()
#pop-options

#push-options "--z3rlimit 15 --initial_fuel 4 --max_fuel 4 --initial_ifuel 2 --max_ifuel 2"
let lemma_instr_write_output_implicit_only_writes
    (i:instr_operand_implicit) (v:instr_val_t (IOpIm i))
    (s_orig1 s1 s_orig2 s2:machine_state) :
  Lemma
    (requires (
        (unchanged_at (fst (locations_of_implicit i)) s_orig1 s_orig2) /\
        (unchanged_at' (fst (locations_of_implicit i)) s1 s2)))
    (ensures (
        let s1', s2' =
          instr_write_output_implicit i v s_orig1 s1,
          instr_write_output_implicit i v s_orig2 s2 in
        let locs = snd (locations_of_implicit i) in
        (unchanged_at' locs s1' s2' /\
         unchanged_except locs s1 s1' /\
         unchanged_except locs s2 s2'))) = ()
#pop-options

let rec lemma_unchanged_at'_mem (as:locations) (a:location) (s1 s2:machine_state) :
  Lemma
    (requires (
        (unchanged_at' as s1 s2) /\
        (L.mem a as)))
    (ensures (
        (eval_location a s1 == eval_location a s2 \/ not s1.ms_ok))) =
  match as with
  | [_] -> ()
  | x :: xs ->
    if a = x then () else
    lemma_unchanged_at'_mem xs a s1 s2

let rec lemma_unchanged_except_not_mem (as:locations) (a:location) :
  Lemma
    (requires (
        (not (L.mem a as))))
    (ensures (
        !!(disjoint_location_from_locations a as))) =
  match as with
  | [] -> ()
  | x :: xs -> lemma_unchanged_except_not_mem xs a

let rec lemma_unchanged_at'_maintained (locs locs_change:locations) (s1 s1' s2 s2':machine_state) :
  Lemma
    (requires (
        (not s1.ms_ok ==> not s1'.ms_ok) /\
        (not s2.ms_ok ==> not s2'.ms_ok) /\
        (unchanged_at' locs s1 s2) /\
        (unchanged_except locs_change s1 s1') /\
        (unchanged_except locs_change s2 s2') /\
        (unchanged_at' locs_change s1' s2')))
    (ensures (
        (unchanged_at' locs s1' s2'))) =
  match locs with
  | [] -> ()
  | x :: xs ->
    lemma_unchanged_at'_maintained xs locs_change s1 s1' s2 s2';
    if x `L.mem` locs_change then (
      lemma_unchanged_at'_mem locs_change x s1' s2'
    ) else (
      lemma_unchanged_except_not_mem locs_change x
    )

let rec lemma_disjoint_location_from_locations_append
  (a:location) (as1 as2:list location) :
  Lemma (
    (!!(disjoint_location_from_locations a as1) /\
     !!(disjoint_location_from_locations a as2)) <==>
    (!!(disjoint_location_from_locations a (as1 `L.append` as2)))) =
  match as1 with
  | [] -> ()
  | x :: xs ->
    lemma_disjoint_location_from_locations_append a xs as2

let lemma_unchanged_except_extend (ls_extend ls:locations) (s1 s2:machine_state) :
  Lemma
    (requires (unchanged_except ls s1 s2))
    (ensures (unchanged_except (ls_extend `L.append` ls) s1 s2)) =
  let aux a :
    Lemma
      (requires (!!(disjoint_location_from_locations a (ls_extend `L.append` ls))))
      (ensures (eval_location a s1 == eval_location a s2)) =
    lemma_disjoint_location_from_locations_append a ls_extend ls
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let lemma_instr_write_outputs_only_affects_write_extend
    (outs:list instr_out) (args:list instr_operand)
    (vs:instr_ret_t outs) (oprs:instr_operands_t outs args)
    (s_orig s:machine_state)
    (locs_extension:locations) :
  Lemma
    (ensures (
        let s' = instr_write_outputs outs args vs oprs s_orig s in
        let locs = aux_write_set outs args oprs in
        unchanged_except (locs_extension `L.append` locs) s s')) =
  let s' = instr_write_outputs outs args vs oprs s_orig s in
  let locs = aux_write_set outs args oprs in
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires (lemma_instr_write_outputs_only_affects_write outs args vs oprs s_orig s));
  lemma_unchanged_except_extend locs_extension locs s s'

#push-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 1"
let rec lemma_instr_write_outputs_only_writes
    (outs:list instr_out) (args:list instr_operand)
    (vs:instr_ret_t outs) (oprs:instr_operands_t outs args)
    (s_orig1 s1 s_orig2 s2:machine_state) :
  Lemma
    (requires (
        (unchanged_at (aux_read_set1 outs args oprs) s_orig1 s_orig2) /\
        (unchanged_at' (aux_read_set1 outs args oprs) s1 s2) /\
        (s1.ms_ok = s2.ms_ok)))
    (ensures (
        let s1', s2' =
          instr_write_outputs outs args vs oprs s_orig1 s1,
          instr_write_outputs outs args vs oprs s_orig2 s2 in
        let locs = aux_write_set outs args oprs in
        (unchanged_at' locs s1' s2' /\
         unchanged_except locs s1 s1' /\
         unchanged_except locs s2 s2' /\
         (not s1.ms_ok ==> not s1'.ms_ok) /\
         (not s2.ms_ok ==> not s2'.ms_ok)))) =
  let s1', s2' =
    instr_write_outputs outs args vs oprs s_orig1 s1,
    instr_write_outputs outs args vs oprs s_orig2 s2 in
  match outs with
  | [] -> ()
  | (io, i) :: outs -> (
      let ((v:instr_val_t i), (vs:instr_ret_t outs)) =
        match outs with
        | [] -> (vs, ())
        | _::_ -> let vs = coerce vs in (fst vs, snd vs)
      in
      match i with
      | IOpEx i ->
        let o, oprs = coerce oprs in
        let loc_op_l, loc_op_r = locations_of_explicit i o in
        let loc_op_b = loc_op_l `L.append` loc_op_r in
        let loc_rest = aux_read_set1 outs args oprs in
        lemma_unchanged_at_append loc_op_l loc_op_r s_orig1 s_orig2;
        lemma_unchanged_at_append loc_op_l loc_rest s_orig1 s_orig2;
        lemma_unchanged_at_append loc_op_b loc_rest s_orig1 s_orig2;
        lemma_unchanged_at_append loc_op_l loc_rest s_orig1 s_orig2;
        lemma_unchanged_at_append loc_op_l loc_op_r s1 s2;
        lemma_unchanged_at_append loc_op_l loc_rest s1 s2;
        lemma_unchanged_at_append loc_op_b loc_rest s1 s2;
        lemma_unchanged_at_append loc_op_l loc_rest s1 s2;
        lemma_instr_write_output_explicit_only_writes i v o s_orig1 s1 s_orig2 s2;
        let s1_old, s1 = s1, instr_write_output_explicit i v o s_orig1 s1 in
        let s2_old, s2 = s2, instr_write_output_explicit i v o s_orig2 s2 in
        lemma_unchanged_at'_maintained loc_rest loc_op_r s1_old s1 s2_old s2;
        lemma_instr_write_outputs_only_writes outs args vs oprs s_orig1 s1 s_orig2 s2;
        lemma_instr_write_outputs_only_affects_write_extend outs args vs oprs s_orig1 s1 loc_op_r;
        lemma_instr_write_outputs_only_affects_write_extend outs args vs oprs s_orig2 s2 loc_op_r;
        lemma_instr_write_outputs_only_affects_write_extend outs args vs oprs s_orig1 s1 [];
        lemma_instr_write_outputs_only_affects_write_extend outs args vs oprs s_orig2 s2 [];
        let s1_old, s1 = s1, instr_write_outputs outs args vs oprs s_orig1 s1 in
        let s2_old, s2 = s2, instr_write_outputs outs args vs oprs s_orig2 s2 in
        lemma_unchanged_at_append loc_op_r (aux_write_set outs args oprs) s1 s2;
        lemma_unchanged_at'_maintained loc_op_r (aux_write_set outs args oprs) s1_old s1 s2_old s2
      | IOpIm i ->
        let oprs = coerce oprs in
        let loc_op_l, loc_op_r = locations_of_implicit i in
        let loc_op_b = loc_op_l `L.append` loc_op_r in
        let loc_rest = aux_read_set1 outs args oprs in
        lemma_unchanged_at_append loc_op_l loc_op_r s_orig1 s_orig2;
        lemma_unchanged_at_append loc_op_l loc_rest s_orig1 s_orig2;
        lemma_unchanged_at_append loc_op_b loc_rest s_orig1 s_orig2;
        lemma_unchanged_at_append loc_op_l loc_rest s_orig1 s_orig2;
        lemma_unchanged_at_append loc_op_l loc_op_r s1 s2;
        lemma_unchanged_at_append loc_op_l loc_rest s1 s2;
        lemma_unchanged_at_append loc_op_b loc_rest s1 s2;
        lemma_unchanged_at_append loc_op_l loc_rest s1 s2;
        lemma_instr_write_output_implicit_only_writes i v s_orig1 s1 s_orig2 s2;
        let s1_old, s1 = s1, instr_write_output_implicit i v s_orig1 s1 in
        let s2_old, s2 = s2, instr_write_output_implicit i v s_orig2 s2 in
        lemma_unchanged_at'_maintained loc_rest loc_op_r s1_old s1 s2_old s2;
        lemma_instr_write_outputs_only_writes outs args vs oprs s_orig1 s1 s_orig2 s2;
        lemma_instr_write_outputs_only_affects_write_extend outs args vs oprs s_orig1 s1 loc_op_r;
        lemma_instr_write_outputs_only_affects_write_extend outs args vs oprs s_orig2 s2 loc_op_r;
        lemma_instr_write_outputs_only_affects_write_extend outs args vs oprs s_orig1 s1 [];
        lemma_instr_write_outputs_only_affects_write_extend outs args vs oprs s_orig2 s2 [];
        let s1_old, s1 = s1, instr_write_outputs outs args vs oprs s_orig1 s1 in
        let s2_old, s2 = s2, instr_write_outputs outs args vs oprs s_orig2 s2 in
        lemma_unchanged_at_append loc_op_r (aux_write_set outs args oprs) s1 s2;
        lemma_unchanged_at'_maintained loc_op_r (aux_write_set outs args oprs) s1_old s1 s2_old s2
    )
#pop-options

let rec lemma_unchanged_at'_maintained_upon_flag_update (locs:locations) (s1 s2:machine_state) (flags:flags_t) :
  Lemma
    (requires (unchanged_at' locs s1 s2))
    (ensures (unchanged_at' locs
                ({s1 with ms_flags = flags})
                ({s2 with ms_flags = flags}))) =
  match locs with
  | [] -> ()
  | x :: xs -> lemma_unchanged_at'_maintained_upon_flag_update xs s1 s2 flags

let lemma_eval_instr_unchanged_at'
    (it:instr_t_record) (oprs:instr_operands_t it.outs it.args) (ann:instr_annotation it)
    (s1 s2:machine_state) :
  Lemma
    (requires (
        let r, w = rw_set_of_ins (Instr it oprs ann) in
        (s1.ms_ok = s2.ms_ok) /\
        (unchanged_at r s1 s2)))
    (ensures (
        let r, w = rw_set_of_ins (Instr it oprs ann) in
        let s1' = eval_instr it oprs ann s1 in
        let s2' = eval_instr it oprs ann s2 in
        (Some? s1' = Some? s2') /\
        (Some? s1' ==>
         unchanged_at' w (Some?.v s1') (Some?.v s2')))) =
  let r, w = rw_set_of_ins (Instr it oprs ann) in
  let InstrTypeRecord #outs #args #havoc_flags' i = it in
  let vs1 = instr_apply_eval outs args (instr_eval i) oprs s1 in
  let vs2 = instr_apply_eval outs args (instr_eval i) oprs s2 in
  lemma_instr_apply_eval_same_read outs args (instr_eval i) oprs s1 s2;
  assert (vs1 == vs2);
  let s11, s22 =
    match havoc_flags' with
    | HavocFlags -> {s1 with ms_flags = havoc_flags}, {s2 with ms_flags = havoc_flags}
    | PreserveFlags -> s1, s2
  in
  let s111 = FStar.Option.mapTot (fun vs -> instr_write_outputs outs args vs oprs s1 s11) vs1 in
  let s222 = FStar.Option.mapTot (fun vs -> instr_write_outputs outs args vs oprs s2 s22) vs2 in
  match vs1 with
  | None -> ()
  | Some vs ->
    lemma_unchanged_at'_maintained_upon_flag_update (aux_read_set1 outs args oprs) s1 s2 havoc_flags;
    lemma_instr_write_outputs_only_writes outs args vs oprs s1 s11 s2 s22;
    if havoc_flags' = HavocFlags then (
      let Some s1', Some s2' = s111, s222 in
      let locs = aux_write_set outs args oprs in
      if L.mem ALocOf locs then (
        lemma_unchanged_at'_mem locs ALocOf s1' s2'
      ) else (
        lemma_unchanged_except_not_mem locs ALocOf
      );
      if L.mem ALocCf locs then (
        lemma_unchanged_at'_mem locs ALocCf s1' s2'
      ) else (
        lemma_unchanged_except_not_mem locs ALocCf
      )
    ) else ()

let lemma_machine_eval_ins_st_ok (i:ins{Instr? i}) (s1 s2:machine_state) :
  Lemma
    (requires (
        let r, w = rw_set_of_ins i in
        (s1.ms_ok = s2.ms_ok) /\
        (unchanged_at r s1 s2)))
    (ensures (
        let r, w = rw_set_of_ins i in
        let f = machine_eval_ins_st i in
        (run f s1).ms_ok = (run f s2).ms_ok)) =
  let Instr it oprs ann = i in
  lemma_eval_instr_unchanged_at' it oprs ann s1 s2

let lemma_machine_eval_ins_st_unchanged_behavior (i:ins{Instr? i}) (s1 s2:machine_state) :
  Lemma
    (requires (
        let r, w = rw_set_of_ins i in
        let f = machine_eval_ins_st i in
        (s1.ms_ok = s2.ms_ok) /\
        (unchanged_at r s1 s2) /\
        (run f s1).ms_ok /\
        (run f s2).ms_ok))
    (ensures (
        let r, w = rw_set_of_ins i in
        let f = machine_eval_ins_st i in
        (unchanged_at w (run f s1) (run f s2)))) =
  let Instr it oprs ann = i in
  lemma_eval_instr_unchanged_at' it oprs ann s1 s2

let lemma_machine_eval_ins_st_bounded_effects_Instr (i:ins{Instr? i}) :
  Lemma
    (ensures (
        (let r, w = rw_set_of_ins i in
         (bounded_effects r w (machine_eval_ins_st i))))) =
  FStar.Classical.forall_intro (lemma_machine_eval_ins_st_only_affects_write i);
  FStar.Classical.forall_intro_2 (fun s1 ->
      FStar.Classical.move_requires (lemma_machine_eval_ins_st_ok i s1));
  FStar.Classical.forall_intro_2 (fun s1 ->
      FStar.Classical.move_requires (lemma_machine_eval_ins_st_unchanged_behavior i s1))

(* See fsti *)
let lemma_machine_eval_ins_st_bounded_effects i =
  match i with
  | Instr _ _ _ -> lemma_machine_eval_ins_st_bounded_effects_Instr i
  | _ -> assert_norm (not (safely_bounded i))
