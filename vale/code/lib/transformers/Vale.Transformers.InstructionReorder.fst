(**

   This module defines a transformer that performs safe instruction
   reordering.

   Example:

     The following set of instructions can be reordered in any order
     without any observable change in behavior:

       mov rax, 10
       mov rbx, 3

   Usage:

     Actual vale-tool or user-facing code should probably use the even
     nicer interface provided by the [Vale.Transformers.Transform]
     module.

     To use this module, you need to generate a [transformation_hints]
     object (a nice default is provided in this module via
     [find_transformation_hints], but users of this module can write
     their own, without needing to change any proofs), that can then
     be applied to a [codes] object (say [c1]) via
     [perform_reordering_with_hints] which tells you if this is a safe
     reordering, and if so, it produces the transformed [codes]
     object. If it is not considered to be safe, then the transformer
     gives a (human-readable) reason for why it doesn't consider it a
     safe reordering. If the transformation is safe and was indeed
     performed, then you can use [lemma_perform_reordering_with_hints]
     to reason about the reordered code having semantically equivalent
     behavior as the untransformed code.

*)
module Vale.Transformers.InstructionReorder

/// Open all the relevant modules

open Vale.X64.Bytes_Code_s
open Vale.X64.Instruction_s
open Vale.X64.Instructions_s
open Vale.X64.Machine_Semantics_s
open Vale.X64.Machine_s
open Vale.X64.Print_s

open Vale.Def.PossiblyMonad

open Vale.Transformers.Locations
open Vale.Transformers.BoundedInstructionEffects

module L = FStar.List.Tot

/// Some convenience functions

let rec locations_of_locations_with_values (lv:locations_with_values) : locations =
  match lv with
  | [] -> []
  | (|l,v|) :: lv ->
    l :: locations_of_locations_with_values lv

/// Given two read/write sets corresponding to two neighboring
/// instructions, we can say whether exchanging those two instructions
/// should be allowed.

let write_same_constants (c1 c2:locations_with_values) : pbool =
  for_all (fun (x1:location_with_value) ->
      for_all (fun (x2:location_with_value) ->
          let (| l1, v1 |) = x1 in
          let (| l2, v2 |) = x2 in
          (if l1 = l2 then v1 = v2 else true) /- "not writing same constants"
        ) c2
    ) c1

let aux_write_exchange_allowed (w2:locations) (c1 c2:locations_with_values) (x:location) : pbool =
  let cv1, cv2 =
    locations_of_locations_with_values c1,
    locations_of_locations_with_values c2 in
  (disjoint_location_from_locations x w2) ||.
  ((x `L.mem` cv1 && x `L.mem` cv2) /- "non constant write")

let write_exchange_allowed (w1 w2:locations) (c1 c2:locations_with_values) : pbool =
  write_same_constants c1 c2 &&.
  for_all (aux_write_exchange_allowed w2 c1 c2) w1 &&.
  (* REVIEW: Just to make the symmetry proof easier, we write the
     other way around too. However, this makes things not as fast as
     they _could_ be. *)
  for_all (aux_write_exchange_allowed w1 c2 c1) w2

let rw_exchange_allowed (rw1 rw2 : rw_set) : pbool =
  let r1, w1, c1 = rw1.loc_reads, rw1.loc_writes, rw1.loc_constant_writes in
  let r2, w2, c2 = rw2.loc_reads, rw2.loc_writes, rw2.loc_constant_writes in
  (disjoint_locations r1 w2 /+< "read set of 1st not disjoint from write set of 2nd because ") &&.
  (disjoint_locations r2 w1 /+< "read set of 2nd not disjoint from write set of 1st because ") &&.
  (write_exchange_allowed w1 w2 c1 c2 /+< "write sets not disjoint because ")

let ins_exchange_allowed (i1 i2 : ins) : pbool =
  (
    match i1, i2 with
    | Instr _ _ _, Instr _ _ _ ->
      (rw_exchange_allowed (rw_set_of_ins i1) (rw_set_of_ins i2))
    | _, _ ->
      ffalse "non-generic instructions: conservatively disallowed exchange"
  ) /+> normal (" for instructions " ^ print_ins i1 gcc ^ " and " ^ print_ins i2 gcc)

let rec lemma_write_same_constants_symmetric (c1 c2:locations_with_values) :
  Lemma
    (ensures (!!(write_same_constants c1 c2) = !!(write_same_constants c2 c1))) =
  match c1, c2 with
  | [], [] -> ()
  | x :: xs, [] ->
    lemma_write_same_constants_symmetric xs []
  | [], y :: ys ->
    lemma_write_same_constants_symmetric [] ys
  | x :: xs, y :: ys ->
    lemma_write_same_constants_symmetric c1 ys;
    lemma_write_same_constants_symmetric xs c2;
    lemma_write_same_constants_symmetric xs ys

let rec lemma_write_exchange_allowed_symmetric (w1 w2:locations) (c1 c2:locations_with_values) :
  Lemma
    (ensures (!!(write_exchange_allowed w1 w2 c1 c2) = !!(write_exchange_allowed w2 w1 c2 c1))) =
  lemma_write_same_constants_symmetric c1 c2

let lemma_ins_exchange_allowed_symmetric (i1 i2 : ins) :
  Lemma
    (requires (
        !!(ins_exchange_allowed i1 i2)))
    (ensures (
        !!(ins_exchange_allowed i2 i1))) =
  let rw1, rw2 = rw_set_of_ins i1, rw_set_of_ins i2 in
  let r1, w1, c1 = rw1.loc_reads, rw1.loc_writes, rw1.loc_constant_writes in
  let r2, w2, c2 = rw2.loc_reads, rw2.loc_writes, rw2.loc_constant_writes in
  lemma_write_exchange_allowed_symmetric w1 w2 c1 c2

/// First, we must define what it means for two states to be
/// equivalent. Here, we basically say they must be exactly the same.

let equiv_states (s1 s2 : machine_state) : GTot Type0 =
  (s1.ms_ok == s2.ms_ok) /\
  (s1.ms_regs == s2.ms_regs) /\
  (cf s1.ms_flags = cf s2.ms_flags) /\
  (overflow s1.ms_flags = overflow s2.ms_flags) /\
  (s1.ms_heap == s2.ms_heap) /\
  (s1.ms_stack == s2.ms_stack) /\
  (s1.ms_stackTaint == s2.ms_stackTaint)

(** Same as [equiv_states] but uses extensionality to "think harder";
    useful at lower-level details of the proof. *)
let equiv_states_ext (s1 s2 : machine_state) : GTot Type0 =
  let open FStar.FunctionalExtensionality in
  (feq s1.ms_regs s2.ms_regs) /\
  (s1.ms_heap == s2.ms_heap) /\
  (Map.equal s1.ms_stack.stack_mem s2.ms_stack.stack_mem) /\
  (Map.equal s1.ms_stackTaint s2.ms_stackTaint) /\
  (equiv_states s1 s2)

(** A weaker version of [equiv_states] that makes all non-ok states
    equivalent. Since non-ok states indicate something "gone-wrong" in
    execution, we can safely say that the rest of the state is
    irrelevant. *)
let equiv_states_or_both_not_ok (s1 s2:machine_state) =
  (equiv_states s1 s2) \/
  ((not s1.ms_ok) /\ (not s2.ms_ok))

(** Convenience wrapper around [equiv_states] *)
unfold
let equiv_ostates (s1 s2 : option machine_state) : GTot Type0 =
  (Some? s1 = Some? s2) /\
  (Some? s1 ==>
   (equiv_states (Some?.v s1) (Some?.v s2)))

(** An [option state] is said to be erroring if it is either [None] or
    if it is [Some] but is not ok.  *)
unfold
let erroring_option_state (s:option machine_state) =
  match s with
  | None -> true
  | Some s -> not (s.ms_ok)

(** [equiv_option_states s1 s2] means that [s1] and [s2] are
    equivalent [option machine_state]s iff both have same erroring behavior
    and if they are non-erroring, they are [equiv_states]. *)
unfold
let equiv_option_states (s1 s2:option machine_state) =
  (erroring_option_state s1 == erroring_option_state s2) /\
  (not (erroring_option_state s1) ==> equiv_states (Some?.v s1) (Some?.v s2))

/// If evaluation starts from a set of equivalent states, and the
/// exact same thing is evaluated, then the final states are still
/// equivalent.

unfold
let proof_run (s:machine_state) (f:st unit) : machine_state =
  let (), s1 = f s in
  { s1 with ms_ok = s1.ms_ok && s.ms_ok }

let rec lemma_instr_apply_eval_args_equiv_states
    (outs:list instr_out) (args:list instr_operand)
    (f:instr_args_t outs args) (oprs:instr_operands_t_args args)
    (s1 s2:machine_state) :
  Lemma
    (requires (equiv_states s1 s2))
    (ensures (
        (instr_apply_eval_args outs args f oprs s1) ==
        (instr_apply_eval_args outs args f oprs s2))) =
  match args with
  | [] -> ()
  | i :: args ->
    let (v, oprs) : option (instr_val_t i) & _ =
      match i with
      | IOpEx i -> let oprs = coerce oprs in (instr_eval_operand_explicit i (fst oprs) s1, snd oprs)
      | IOpIm i -> (instr_eval_operand_implicit i s1, coerce oprs)
    in
    let f:arrow (instr_val_t i) (instr_args_t outs args) = coerce f in
    match v with
    | None -> ()
    | Some v ->
      lemma_instr_apply_eval_args_equiv_states outs args (f v) oprs s1 s2

#push-options "--z3rlimit 10"
let rec lemma_instr_apply_eval_inouts_equiv_states
    (outs inouts:list instr_out) (args:list instr_operand)
    (f:instr_inouts_t outs inouts args) (oprs:instr_operands_t inouts args)
    (s1 s2:machine_state) :
  Lemma
    (requires (equiv_states s1 s2))
    (ensures (
        (instr_apply_eval_inouts outs inouts args f oprs s1) ==
        (instr_apply_eval_inouts outs inouts args f oprs s2))) =
  match inouts with
  | [] ->
    lemma_instr_apply_eval_args_equiv_states outs args f oprs s1 s2
  | (Out, i) :: inouts ->
    let oprs =
      match i with
      | IOpEx i -> snd #(instr_operand_t i) (coerce oprs)
      | IOpIm i -> coerce oprs
    in
    lemma_instr_apply_eval_inouts_equiv_states outs inouts args (coerce f) oprs s1 s2
  | (InOut, i)::inouts ->
    let (v, oprs) : option (instr_val_t i) & _ =
      match i with
      | IOpEx i -> let oprs = coerce oprs in (instr_eval_operand_explicit i (fst oprs) s1, snd oprs)
      | IOpIm i -> (instr_eval_operand_implicit i s1, coerce oprs)
    in
    let f:arrow (instr_val_t i) (instr_inouts_t outs inouts args) = coerce f in
    match v with
    | None -> ()
    | Some v ->
      lemma_instr_apply_eval_inouts_equiv_states outs inouts args (f v) oprs s1 s2
#pop-options

#push-options "--z3rlimit 10 --max_fuel 1 --max_ifuel 0"

let lemma_instr_write_output_implicit_equiv_states
    (i:instr_operand_implicit) (v:instr_val_t (IOpIm i))
    (s_orig1 s1 s_orig2 s2:machine_state) :
  Lemma
    (requires (
        (equiv_states s_orig1 s_orig2) /\
        (equiv_states s1 s2)))
    (ensures (
        (equiv_states
           (instr_write_output_implicit i v s_orig1 s1)
           (instr_write_output_implicit i v s_orig2 s2)))) =
  let snew1, snew2 =
    (instr_write_output_implicit i v s_orig1 s1),
    (instr_write_output_implicit i v s_orig2 s2) in
  assert (equiv_states_ext snew1 snew2) (* OBSERVE *)

let lemma_instr_write_output_explicit_equiv_states
    (i:instr_operand_explicit) (v:instr_val_t (IOpEx i)) (o:instr_operand_t i)
    (s_orig1 s1 s_orig2 s2:machine_state) :
  Lemma
    (requires (
        (equiv_states s_orig1 s_orig2) /\
        (equiv_states s1 s2)))
    (ensures (
        (equiv_states
           (instr_write_output_explicit i v o s_orig1 s1)
           (instr_write_output_explicit i v o s_orig2 s2)))) =
  let snew1, snew2 =
    (instr_write_output_explicit i v o s_orig1 s1),
    (instr_write_output_explicit i v o s_orig2 s2) in
  assert (equiv_states_ext snew1 snew2) (* OBSERVE *)

#pop-options

let rec lemma_instr_write_outputs_equiv_states
    (outs:list instr_out) (args:list instr_operand)
    (vs:instr_ret_t outs) (oprs:instr_operands_t outs args)
    (s_orig1 s1:machine_state)
    (s_orig2 s2:machine_state) :
  Lemma
    (requires (
        (equiv_states s_orig1 s_orig2) /\
        (equiv_states s1 s2)))
    (ensures (
        (equiv_states
           (instr_write_outputs outs args vs oprs s_orig1 s1)
           (instr_write_outputs outs args vs oprs s_orig2 s2)))) =
  match outs with
  | [] -> ()
  | (_, i)::outs ->
    (
      let ((v:instr_val_t i), (vs:instr_ret_t outs)) =
        match outs with
        | [] -> (vs, ())
        | _::_ -> let vs = coerce vs in (fst vs, snd vs)
      in
      match i with
      | IOpEx i ->
        let oprs = coerce oprs in
        lemma_instr_write_output_explicit_equiv_states i v (fst oprs) s_orig1 s1 s_orig2 s2;
        let s1 = instr_write_output_explicit i v (fst oprs) s_orig1 s1 in
        let s2 = instr_write_output_explicit i v (fst oprs) s_orig2 s2 in
        lemma_instr_write_outputs_equiv_states outs args vs (snd oprs) s_orig1 s1 s_orig2 s2
      | IOpIm i ->
        lemma_instr_write_output_implicit_equiv_states i v s_orig1 s1 s_orig2 s2;
        let s1 = instr_write_output_implicit i v s_orig1 s1 in
        let s2 = instr_write_output_implicit i v s_orig2 s2 in
        lemma_instr_write_outputs_equiv_states outs args vs (coerce oprs) s_orig1 s1 s_orig2 s2
    )

let lemma_eval_instr_equiv_states
    (it:instr_t_record) (oprs:instr_operands_t it.outs it.args) (ann:instr_annotation it)
    (s1 s2:machine_state) :
  Lemma
    (requires (equiv_states s1 s2))
    (ensures (
        equiv_ostates
          (eval_instr it oprs ann s1)
          (eval_instr it oprs ann s2))) =
  let InstrTypeRecord #outs #args #havoc_flags' i = it in
  let vs1 = instr_apply_eval outs args (instr_eval i) oprs s1 in
  let vs2 = instr_apply_eval outs args (instr_eval i) oprs s2 in
  lemma_instr_apply_eval_inouts_equiv_states outs outs args (instr_eval i) oprs s1 s2;
  assert (vs1 == vs2);
  let s1_new =
    match havoc_flags' with
    | HavocFlags -> {s1 with ms_flags = havoc_flags}
    | PreserveFlags -> s1
  in
  let s2_new =
    match havoc_flags' with
    | HavocFlags -> {s2 with ms_flags = havoc_flags}
    | PreserveFlags -> s2
  in
  assert (overflow s1_new.ms_flags == overflow s2_new.ms_flags);
  assert (cf s1_new.ms_flags == cf s2_new.ms_flags);
  assert (equiv_states s1_new s2_new);
  let os1 = FStar.Option.mapTot (fun vs -> instr_write_outputs outs args vs oprs s1 s1_new) vs1 in
  let os2 = FStar.Option.mapTot (fun vs -> instr_write_outputs outs args vs oprs s2 s2_new) vs2 in
  match vs1 with
  | None -> ()
  | Some vs ->
    lemma_instr_write_outputs_equiv_states outs args vs oprs s1 s1_new s2 s2_new

#push-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 1"
(* REVIEW: This proof is INSANELY annoying to deal with due to the [Pop].

   TODO: Figure out why it is slowing down so much. It practically
         brings F* to a standstill even when editing, and it acts
         worse during an interactive proof. *)
let lemma_machine_eval_ins_st_equiv_states (i : ins) (s1 s2 : machine_state) :
  Lemma
    (requires (equiv_states s1 s2))
    (ensures (
        equiv_states
          (run (machine_eval_ins_st i) s1)
          (run (machine_eval_ins_st i) s2))) =
  let s1_orig, s2_orig = s1, s2 in
  let s1_final = run (machine_eval_ins_st i) s1 in
  let s2_final = run (machine_eval_ins_st i) s2 in
  match i with
  | Instr it oprs ann ->
    lemma_eval_instr_equiv_states it oprs ann s1 s2
  | Push _ _ ->
    assert_spinoff (equiv_states_ext s1_final s2_final)
  | Pop dst t ->
    let stack_op = OStack (MReg (Reg 0 rRsp) 0, t) in
    let s1 = proof_run s1 (check (valid_src_operand64_and_taint stack_op)) in
    let s2 = proof_run s2 (check (valid_src_operand64_and_taint stack_op)) in
    // assert (equiv_states s1 s2);
    let new_dst1 = eval_operand stack_op s1 in
    let new_dst2 = eval_operand stack_op s2 in
    // assert (new_dst1 == new_dst2);
    let new_rsp1 = (eval_reg_64 rRsp s1 + 8) % pow2_64 in
    let new_rsp2 = (eval_reg_64 rRsp s2 + 8) % pow2_64 in
    // assert (new_rsp1 == new_rsp2);
    let s1 = proof_run s1 (update_operand64_preserve_flags dst new_dst1) in
    let s2 = proof_run s2 (update_operand64_preserve_flags dst new_dst2) in
    assert (equiv_states_ext s1 s2);
    let s1 = proof_run s1 (free_stack (new_rsp1 - 8) new_rsp1) in
    let s2 = proof_run s2 (free_stack (new_rsp2 - 8) new_rsp2) in
    // assert (equiv_states s1 s2);
    let s1 = proof_run s1 (update_rsp new_rsp1) in
    let s2 = proof_run s2 (update_rsp new_rsp2) in
    assert (equiv_states_ext s1 s2);
    assert_spinoff (equiv_states s1_final s2_final)
  | Alloc _ ->
    assert_spinoff (equiv_states_ext s1_final s2_final)
  | Dealloc _ ->
    assert_spinoff (equiv_states_ext s1_final s2_final)
#pop-options

let lemma_eval_ins_equiv_states (i : ins) (s1 s2 : machine_state) :
  Lemma
    (requires (equiv_states s1 s2))
    (ensures (
        equiv_states
          (machine_eval_ins i s1)
          (machine_eval_ins i s2))) =
  lemma_machine_eval_ins_st_equiv_states i s1 s2

(** Filter out observation related stuff from the state. *)
let filt_state (s:machine_state) =
  { s with
    ms_trace = [] }

#push-options "--z3rlimit 10 --max_fuel 1 --max_ifuel 1"

let rec lemma_eval_code_equiv_states (c : code) (fuel:nat) (s1 s2 : machine_state) :
  Lemma
    (requires (equiv_states s1 s2))
    (ensures (
        let s1'', s2'' =
          machine_eval_code c fuel s1,
          machine_eval_code c fuel s2 in
        equiv_ostates s1'' s2''))
    (decreases %[fuel; c; 1]) =
  match c with
  | Ins ins ->
    lemma_eval_ins_equiv_states ins (filt_state s1) (filt_state s2)
  | Block l ->
    lemma_eval_codes_equiv_states l fuel s1 s2
  | IfElse ifCond ifTrue ifFalse ->
    let (st1, b1) = machine_eval_ocmp s1 ifCond in
    let (st2, b2) = machine_eval_ocmp s2 ifCond in
    assert (equiv_states st1 st2);
    assert (b1 == b2);
    let s1' = { st1 with ms_trace = (BranchPredicate b1) :: s1.ms_trace } in
    let s2' = { st2 with ms_trace = (BranchPredicate b2) :: s2.ms_trace } in
    assert (equiv_states s1' s2');
    if b1 then (
      lemma_eval_code_equiv_states ifTrue fuel s1' s2'
    ) else (
      lemma_eval_code_equiv_states ifFalse fuel s1' s2'
    )
  | While _ _ ->
    lemma_eval_while_equiv_states c fuel s1 s2

and lemma_eval_codes_equiv_states (cs : codes) (fuel:nat) (s1 s2 : machine_state) :
  Lemma
    (requires (equiv_states s1 s2))
    (ensures (
        let s1'', s2'' =
          machine_eval_codes cs fuel s1,
          machine_eval_codes cs fuel s2 in
        equiv_ostates s1'' s2''))
    (decreases %[fuel; cs]) =
  match cs with
  | [] -> ()
  | c :: cs ->
    lemma_eval_code_equiv_states c fuel s1 s2;
    let s1'', s2'' =
      machine_eval_code c fuel s1,
      machine_eval_code c fuel s2 in
    match s1'' with
    | None -> ()
    | _ ->
      let Some s1, Some s2 = s1'', s2'' in
      lemma_eval_codes_equiv_states cs fuel s1 s2

and lemma_eval_while_equiv_states (c : code{While? c}) (fuel:nat) (s1 s2:machine_state) :
  Lemma
    (requires (equiv_states s1 s2))
    (ensures (
        equiv_ostates
          (machine_eval_while c fuel s1)
          (machine_eval_while c fuel s2)))
    (decreases %[fuel; c; 0]) =
  if fuel = 0 then () else (
    let While cond body = c in
    let (s1, b1) = machine_eval_ocmp s1 cond in
    let (s2, b2) = machine_eval_ocmp s2 cond in
    assert (equiv_states s1 s2);
    assert (b1 == b2);
    if not b1 then () else (
      let s1 = { s1 with ms_trace = (BranchPredicate true) :: s1.ms_trace } in
      let s2 = { s2 with ms_trace = (BranchPredicate true) :: s2.ms_trace } in
      assert (equiv_states s1 s2);
      let s_opt1 = machine_eval_code body (fuel - 1) s1 in
      let s_opt2 = machine_eval_code body (fuel - 1) s2 in
      lemma_eval_code_equiv_states body (fuel - 1) s1 s2;
      assert (equiv_ostates s_opt1 s_opt2);
      match s_opt1 with
      | None -> ()
      | Some _ ->
        let Some s1, Some s2 = s_opt1, s_opt2 in
        if s1.ms_ok then (
          lemma_eval_while_equiv_states c (fuel - 1) s1 s2
        ) else ()
    )
  )

#pop-options

/// If an exchange is allowed between two instructions based off of
/// their read/write sets, then both orderings of the two instructions
/// behave exactly the same, as per the previously defined
/// [equiv_states] relation.
///
/// Note that we require (for the overall proof) a notion of the
/// following:
///
///         s1  =====  s2        Key:
///         |          |
///         .          .            + s1, s2, ... : machine_states
///         . f1       . f2         + f1, f2 : some function from a
///         .          .                         machine_state to a
///         |          |                         machine_state
///         V          V            + ===== : equiv_states
///         s1' ===== s2'
///
/// However, proving with the [equiv_states s1 s2] as part of the
/// preconditions requires come complex wrangling and thinking about
/// how different states [s1] and [s2] evolve. In particular, we'd
/// need to show and write something similar _every_ step of the
/// execution of [f1] and [f2]. Instead, we decompose the above
/// diagram into the following:
///
///
///             s1  =====  s2
///            /  \          \
///           .    .          .
///          . f1   . f2       . f2
///         .        .          .
///        /          \          \
///        V          V          V
///        s1' =====  s2''===== s2'
///
///
/// We now have the ability to decompose the left "triangular" portion
/// which is similar to the rectangular diagram above, except the
/// issue of having to manage both [s1] and [s2] is mitigated. Next,
/// if we look at the right "parallelogram" portion of the diagram, we
/// see that this is just the same as saying "running [f2] on
/// [equiv_states] leads to [equiv_states]" which is something that is
/// easier to prove.
///
/// All the parallelogram proofs have already been completed by this
/// point in the file, so only the triangular portions remain (and the
/// one proof that links the two up into a single diagram as above).

unfold
let run2 (f1 f2:st unit) (s:machine_state) : machine_state =
  let open Vale.X64.Machine_Semantics_s in
  run (f1;; f2;; return ()) s

let commutes (s:machine_state) (f1 f2:st unit) : GTot Type0 =
  equiv_states_or_both_not_ok
    (run2 f1 f2 s)
    (run2 f2 f1 s)

let rec lemma_disjoint_implies_unchanged_at (reads changes:list location) (s1 s2:machine_state) :
  Lemma
    (requires (!!(disjoint_locations reads changes) /\
               unchanged_except changes s1 s2))
    (ensures (unchanged_at reads s1 s2)) =
  match reads with
  | [] -> ()
  | x :: xs ->
    lemma_disjoint_implies_unchanged_at xs changes s1 s2

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

let lemma_unchanged_except_transitive (a12 a23:list location) (s1 s2 s3:machine_state) :
  Lemma
    (requires (unchanged_except a12 s1 s2 /\ unchanged_except a23 s2 s3))
    (ensures (unchanged_except (a12 `L.append` a23) s1 s3)) =
  let aux a : Lemma
    (requires (!!(disjoint_location_from_locations a (a12 `L.append` a23))))
    (ensures (eval_location a s1 == eval_location a s3)) =
    lemma_disjoint_location_from_locations_append a a12 a23 in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let lemma_unchanged_except_append_symmetric (a1 a2:list location) (s1 s2:machine_state) :
  Lemma
    (requires (unchanged_except (a1 `L.append` a2) s1 s2))
    (ensures (unchanged_except (a2 `L.append` a1) s1 s2)) =
  let aux a : Lemma
    (requires (
       (!!(disjoint_location_from_locations a (a1 `L.append` a2))) \/
       (!!(disjoint_location_from_locations a (a2 `L.append` a1)))))
    (ensures (eval_location a s1 == eval_location a s2)) =
    lemma_disjoint_location_from_locations_append a a1 a2;
    lemma_disjoint_location_from_locations_append a a2 a1 in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

#push-options "--initial_fuel 2 --max_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let rec lemma_disjoint_location_from_locations_mem
    (a1 a2:list location) (a:location) :
  Lemma
    (requires (
        (L.mem a a1) /\
        !!(disjoint_locations a1 a2)))
    (ensures (
        !!(disjoint_location_from_locations a a2))) =
  match a1 with
  | [_] -> ()
  | x :: xs ->
    if a = x then () else
    lemma_disjoint_location_from_locations_mem xs a2 a
#pop-options

#push-options "--initial_fuel 2 --max_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let rec lemma_constant_on_execution_mem
    (locv:locations_with_values) (f:st unit) (s:machine_state)
    (l:location_eq) (v:location_val_eqt l) :
  Lemma
    (requires (
        (constant_on_execution locv f s) /\
        ((run f s).ms_ok) /\
        ((| l, v |) `L.mem` locv)))
    (ensures (
        (eval_location l (run f s) == raise_location_val_eqt v))) =
  match locv with
  | [_] -> ()
  | x :: xs ->
    if x = (| l, v |) then () else (
      lemma_constant_on_execution_mem xs f s l v
    )
#pop-options

let rec lemma_disjoint_location_from_locations_mem1 (a:location) (as:locations) :
  Lemma
    (requires (not (L.mem a as)))
    (ensures (!!(disjoint_location_from_locations a as))) =
  match as with
  | [] -> ()
  | x :: xs -> lemma_disjoint_location_from_locations_mem1 a xs

let rec value_of_const_loc (lv:locations_with_values) (l:location_eq{
    L.mem l (locations_of_locations_with_values lv)
  }) : location_val_eqt l =
  let x :: xs = lv in
  if dfst x = l then dsnd x else value_of_const_loc xs l

let rec lemma_write_same_constants_append (c1 c1' c2:locations_with_values) :
  Lemma
    (ensures (
        !!(write_same_constants (c1 `L.append` c1') c2) = (
          !!(write_same_constants c1 c2) &&
          !!(write_same_constants c1' c2)))) =
  match c1 with
  | [] -> ()
  | x :: xs -> lemma_write_same_constants_append xs c1' c2

let rec lemma_write_same_constants_mem_both (c1 c2:locations_with_values)
    (l:location_eq) :
  Lemma
    (requires (!!(write_same_constants c1 c2) /\
               L.mem l (locations_of_locations_with_values c1) /\
               L.mem l (locations_of_locations_with_values c2)))
    (ensures (value_of_const_loc c1 l = value_of_const_loc c2 l)) =
  let x :: xs = c1 in
  let y :: ys = c2 in
  if dfst x = l then (
    if dfst y = l then () else (
      lemma_write_same_constants_symmetric c1 c2;
      lemma_write_same_constants_symmetric ys c1;
      lemma_write_same_constants_mem_both c1 ys l
    )
  ) else (
    lemma_write_same_constants_mem_both xs c2 l
  )

let rec lemma_value_of_const_loc_mem (c:locations_with_values) (l:location_eq) (v:location_val_eqt l) :
  Lemma
    (requires (
        L.mem l (locations_of_locations_with_values c) /\
        value_of_const_loc c l = v))
    (ensures (L.mem (|l,v|) c)) =
  let x :: xs = c in
  if dfst x = l then () else lemma_value_of_const_loc_mem xs l v

#push-options "--initial_fuel 2 --max_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let rec lemma_unchanged_at_mem (as:list location) (a:location) (s1 s2:machine_state) :
  Lemma
    (requires (
        (unchanged_at as s1 s2) /\
        (L.mem a as)))
    (ensures (
        (eval_location a s1 == eval_location a s2))) =
  match as with
  | [_] -> ()
  | x :: xs ->
    if a = x then () else
    lemma_unchanged_at_mem xs a s1 s2
#pop-options

let lemma_unchanged_at_combine (a1 a2:locations) (c1 c2:locations_with_values) (sa1 sa2 sb1 sb2:machine_state) :
  Lemma
    (requires (
        !!(write_exchange_allowed a1 a2 c1 c2) /\
        (unchanged_at (locations_of_locations_with_values c1) sb1 sb2) /\
        (unchanged_at (locations_of_locations_with_values c2) sb1 sb2) /\
        (unchanged_at a1 sa1 sb2) /\
        (unchanged_except a2 sa1 sb1) /\
        (unchanged_at a2 sa2 sb1) /\
        (unchanged_except a1 sa2 sb2)))
    (ensures (
        (unchanged_at (a1 `L.append` a2) sb1 sb2))) =
  let precond = !!(write_exchange_allowed a1 a2 c1 c2) /\
                (unchanged_at (locations_of_locations_with_values c1) sb1 sb2) /\
                (unchanged_at (locations_of_locations_with_values c2) sb1 sb2) /\
                (unchanged_at a1 sa1 sb2) /\
                (unchanged_except a2 sa1 sb1) /\
                (unchanged_at a2 sa2 sb1) /\
                (unchanged_except a1 sa2 sb2) in
  let aux1 a :
    Lemma
      (requires (L.mem a a1 /\ precond))
      (ensures (eval_location a sb1 == eval_location a sb2)) =
    if L.mem a (locations_of_locations_with_values c1) then (
      lemma_unchanged_at_mem (locations_of_locations_with_values c1) a sb1 sb2
    ) else (
      lemma_for_all_elim (aux_write_exchange_allowed a2 c1 c2) a1;
      L.mem_memP a a1;
      assert !!(aux_write_exchange_allowed a2 c1 c2 a);
      assert !!(disjoint_location_from_locations a a2);
      assert (eval_location a sb1 == eval_location a sa1);
      lemma_unchanged_at_mem a1 a sa1 sb2
    )
  in
  let aux2 a :
    Lemma
      (requires (L.mem a a2 /\ precond))
      (ensures (eval_location a sb1 == eval_location a sb2)) =
    if L.mem a (locations_of_locations_with_values c2) then (
      lemma_unchanged_at_mem (locations_of_locations_with_values c2) a sb1 sb2
    ) else (
      lemma_write_exchange_allowed_symmetric a1 a2 c1 c2;
      lemma_for_all_elim (aux_write_exchange_allowed a1 c2 c1) a2;
      L.mem_memP a a2;
      assert !!(aux_write_exchange_allowed a1 c2 c1 a);
      assert !!(disjoint_location_from_locations a a1);
      assert (eval_location a sb2 == eval_location a sa2);
      lemma_unchanged_at_mem a2 a sa2 sb1
    )
  in
  let rec aux a1' a1'' a2' a2'' :
    Lemma
      (requires (a1' `L.append` a1'' == a1 /\ a2' `L.append` a2'' == a2 /\ precond))
      (ensures (unchanged_at (a1'' `L.append` a2'') sb1 sb2))
      (decreases %[a1''; a2'']) =
    match a1'' with
    | [] -> (
        match a2'' with
        | [] -> ()
        | y :: ys -> (
            L.append_l_cons y ys a2';
            L.append_mem a2' a2'' y;
            aux2 y;
            aux a1' a1'' (a2' `L.append` [y]) ys
          )
      )
    | x :: xs ->
      L.append_l_cons x xs a1';
      L.append_mem a1' a1'' x;
      aux1 x;
      aux (a1' `L.append` [x]) xs a2' a2''
  in
  aux [] a1 [] a2

let lemma_unchanged_except_same_transitive (as:list location) (s1 s2 s3:machine_state) :
  Lemma
    (requires (
        (unchanged_except as s1 s2) /\
        (unchanged_except as s2 s3)))
    (ensures (
        (unchanged_except as s1 s3))) = ()

let rec lemma_unchanged_at_and_except (as:list location) (s1 s2:machine_state) :
  Lemma
    (requires (
        (unchanged_at as s1 s2) /\
        (unchanged_except as s1 s2)))
    (ensures (
        (unchanged_except [] s1 s2))) =
  match as with
  | [] -> ()
  | x :: xs ->
    lemma_unchanged_at_and_except xs s1 s2

let lemma_equiv_states_when_except_none (s1 s2:machine_state) (ok:bool) :
  Lemma
    (requires (
        (unchanged_except [] s1 s2)))
    (ensures (
        (equiv_states ({s1 with ms_ok=ok}) ({s2 with ms_ok=ok})))) =
  assert_norm (cf s2.ms_flags == cf (filter_state s2 s1.ms_flags ok []).ms_flags); (* OBSERVE *)
  assert_norm (overflow s2.ms_flags == overflow (filter_state s2 s1.ms_flags ok []).ms_flags); (* OBSERVE *)
  lemma_locations_complete s1 s2 s1.ms_flags ok []

#push-options "--initial_fuel 2 --max_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let rec lemma_mem_not_disjoint (a:location) (as1 as2:list location) :
  Lemma
    (requires (L.mem a as1 /\ L.mem a as2))
    (ensures (
        (not !!(disjoint_locations as1 as2)))) =
  match as1, as2 with
  | [_], [_] -> ()
  | [_], y :: ys ->
    if a = y then () else (
      lemma_mem_not_disjoint a as1 ys
    )
  | x :: xs, y :: ys ->
    if a = x then (
      if a = y then () else (
        lemma_mem_not_disjoint a as1 ys;
        lemma_disjoint_locations_symmetric as1 as2;
        lemma_disjoint_locations_symmetric as1 ys
      )
    ) else (
      lemma_mem_not_disjoint a xs as2
    )
#pop-options

let lemma_bounded_effects_means_same_ok (rw:rw_set) (f:st unit) (s1 s2 s1' s2':machine_state) :
  Lemma
    (requires (
        (bounded_effects rw f) /\
        (s1.ms_ok = s2.ms_ok) /\
        (unchanged_at rw.loc_reads s1 s2) /\
        (s1' == run f s1) /\
        (s2' == run f s2)))
    (ensures (
        ((run f s1).ms_ok = (run f s2).ms_ok))) = ()

let lemma_both_not_ok (f1 f2:st unit) (rw1 rw2:rw_set) (s:machine_state) :
  Lemma
    (requires (
        (bounded_effects rw1 f1) /\
        (bounded_effects rw2 f2) /\
        !!(rw_exchange_allowed rw1 rw2)))
    (ensures (
        (run2 f1 f2 s).ms_ok =
        (run2 f2 f1 s).ms_ok)) =
  if (run f1 s).ms_ok then (
    lemma_disjoint_implies_unchanged_at rw2.loc_reads rw1.loc_writes s (run f1 s)
  ) else ();
  if (run f2 s).ms_ok then (
    lemma_disjoint_implies_unchanged_at rw1.loc_reads rw2.loc_writes s (run f2 s)
  ) else ()

#push-options "--initial_fuel 2 --max_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let lemma_constant_on_execution_stays_constant (f1 f2:st unit) (rw1 rw2:rw_set) (s s1 s2:machine_state) :
  Lemma
    (requires (
        s1.ms_ok /\ s2.ms_ok /\
        (run f1 s1).ms_ok /\ (run f2 s2).ms_ok /\
        (bounded_effects rw1 f1) /\
        (bounded_effects rw2 f2) /\
        (s1 == run f2 s) /\
        (s2 == run f1 s) /\
        !!(write_exchange_allowed rw1.loc_writes rw2.loc_writes rw1.loc_constant_writes rw2.loc_constant_writes)))
    (ensures (
        unchanged_at (locations_of_locations_with_values rw1.loc_constant_writes)
          (run f1 s1)
          (run f2 s2) /\
        unchanged_at (locations_of_locations_with_values rw2.loc_constant_writes)
          (run f1 s1)
          (run f2 s2))) =
  let precond =
    s1.ms_ok /\ s2.ms_ok /\
    (run f1 s1).ms_ok /\ (run f2 s2).ms_ok /\
    (bounded_effects rw1 f1) /\
    (bounded_effects rw2 f2) /\
    (s1 == run f2 s) /\
    (s2 == run f1 s) /\
    !!(write_exchange_allowed rw1.loc_writes rw2.loc_writes rw1.loc_constant_writes rw2.loc_constant_writes) in
  let r1, w1, c1 = rw1.loc_reads, rw1.loc_writes, rw1.loc_constant_writes in
  let r2, w2, c2 = rw2.loc_reads, rw2.loc_writes, rw2.loc_constant_writes in
  let cv1, cv2 =
    locations_of_locations_with_values rw1.loc_constant_writes,
    locations_of_locations_with_values rw2.loc_constant_writes in
  let rec aux1 lv lv' :
    Lemma
      (requires (
          (precond) /\
          lv `L.append` lv' == c1))
      (ensures (
          (unchanged_at (locations_of_locations_with_values lv') (run f1 s1) (run f2 s2))))
      (decreases %[lv']) =
    match lv' with
    | [] -> ()
    | x :: xs ->
      let (|l,v|) = x in
      L.append_mem lv lv' x;
      lemma_constant_on_execution_mem (lv `L.append` lv') f1 s1 l v;
      lemma_for_all_elim (aux_write_exchange_allowed w2 c1 c2) w1;
      assert (eval_location l (run f1 s1) == raise_location_val_eqt v);
      if L.mem l w2 then (
        L.mem_memP l w1;
        assert !!(aux_write_exchange_allowed w2 c1 c2 l);
        lemma_mem_not_disjoint l [l] w2;
        assert (not !!(disjoint_location_from_locations l w2));
        //assert (L.mem (coerce l) cv2);
        assert !!(write_same_constants c1 c2);
        assert (value_of_const_loc lv' l = v);
        lemma_write_same_constants_append lv lv' c2;
        lemma_write_same_constants_mem_both lv' c2 l;
        lemma_value_of_const_loc_mem c2 l v;
        lemma_constant_on_execution_mem c2 f2 s2 l v
      ) else (
        assert (constant_on_execution c1 f1 s);
        lemma_constant_on_execution_mem (lv `L.append` lv') f1 s l v;
        assert (eval_location l (run f1 s) == raise_location_val_eqt v);
        assert (unchanged_except w2 s2 (run f2 s2));
        lemma_disjoint_location_from_locations_mem1 l w2;
        assert (!!(disjoint_location_from_locations l w2));
        assert (eval_location l (run f2 s2) == raise_location_val_eqt v)
      );
      L.append_l_cons x xs lv;
      aux1 (lv `L.append` [x]) xs
  in
  let rec aux2 lv lv' :
    Lemma
      (requires (
          (precond) /\
          lv `L.append` lv' == c2))
      (ensures (
          (unchanged_at (locations_of_locations_with_values lv') (run f1 s1) (run f2 s2))))
      (decreases %[lv']) =
    match lv' with
    | [] -> ()
    | x :: xs ->
      let (|l,v|) = x in
      L.append_mem lv lv' x;
      lemma_constant_on_execution_mem (lv `L.append` lv') f2 s2 l v;
      lemma_write_exchange_allowed_symmetric w1 w2 c1 c2;
      lemma_for_all_elim (aux_write_exchange_allowed w1 c2 c1) w2;
      assert (eval_location l (run f2 s2) == raise_location_val_eqt v);
      if L.mem l w1 then (
        L.mem_memP l w2;
        assert !!(aux_write_exchange_allowed w1 c2 c1 l);
        lemma_mem_not_disjoint l [l] w1;
        assert (not !!(disjoint_location_from_locations l w1));
        //assert (L.mem (coerce l) cv1);
        assert !!(write_same_constants c2 c1);
        assert (value_of_const_loc lv' l = v);
        lemma_write_same_constants_append lv lv' c1;
        lemma_write_same_constants_mem_both lv' c1 l;
        lemma_value_of_const_loc_mem c1 l v;
        lemma_constant_on_execution_mem c1 f1 s1 l v
      ) else (
        assert (constant_on_execution c2 f2 s);
        lemma_constant_on_execution_mem (lv `L.append` lv') f2 s l v;
        assert (eval_location l (run f2 s) == raise_location_val_eqt v);
        assert (unchanged_except w1 s1 (run f1 s1));
        lemma_disjoint_location_from_locations_mem1 l w1;
        assert (!!(disjoint_location_from_locations l w1));
        assert (eval_location l (run f1 s1) == raise_location_val_eqt v)
      );
      L.append_l_cons x xs lv;
      aux2 (lv `L.append` [x]) xs
  in
  aux1 [] c1;
  aux2 [] c2
#pop-options

let lemma_commute (f1 f2:st unit) (rw1 rw2:rw_set) (s:machine_state) :
  Lemma
    (requires (
        (bounded_effects rw1 f1) /\
        (bounded_effects rw2 f2) /\
        !!(rw_exchange_allowed rw1 rw2)))
    (ensures (
        equiv_states_or_both_not_ok
          (run2 f1 f2 s)
          (run2 f2 f1 s))) =
  let s12 = run2 f1 f2 s in
  let s21 = run2 f2 f1 s in
  if not s12.ms_ok || not s21.ms_ok then (
    lemma_both_not_ok f1 f2 rw1 rw2 s
  ) else (
    let s1 = run f1 s in
    let s2 = run f2 s in
    let r1, w1, c1 = rw1.loc_reads, rw1.loc_writes, rw1.loc_constant_writes in
    let r2, w2, c2 = rw2.loc_reads, rw2.loc_writes, rw2.loc_constant_writes in
    assert (s12 == run f2 s1 /\ s21 == run f1 s2);
    lemma_disjoint_implies_unchanged_at r1 w2 s s2;
    lemma_disjoint_implies_unchanged_at r2 w1 s s1;
    assert (unchanged_at w1 s1 s21);
    assert (unchanged_at w2 s2 s12);
    assert (unchanged_except w2 s s2);
    assert (unchanged_except w1 s s1);
    assert (unchanged_except w2 s1 s12);
    assert (unchanged_except w1 s2 s21);
    lemma_unchanged_except_transitive w1 w2 s s1 s12;
    assert (unchanged_except (w1 `L.append` w2) s s12);
    lemma_unchanged_except_transitive w2 w1 s s2 s21;
    assert (unchanged_except (w2 `L.append` w1) s s21);
    lemma_unchanged_except_append_symmetric w1 w2 s s12;
    lemma_unchanged_except_append_symmetric w2 w1 s s21;
    lemma_unchanged_except_same_transitive (w1 `L.append` w2) s s12 s21;
    lemma_write_exchange_allowed_symmetric w1 w2 c1 c2;
    lemma_constant_on_execution_stays_constant f2 f1 rw2 rw1 s s1 s2;
    lemma_unchanged_at_combine w1 w2 c1 c2 s1 s2 s12 s21;
    lemma_unchanged_at_and_except (w1 `L.append` w2) s12 s21;
    assert (unchanged_except [] s12 s21);
    assert (s21.ms_ok = s12.ms_ok);
    lemma_equiv_states_when_except_none s12 s21 s12.ms_ok;
    assert (equiv_states (run2 f1 f2 s) (run2 f2 f1 s))
  )

let wrap_ss (f:machine_state -> machine_state) : st unit =
  let open Vale.X64.Machine_Semantics_s in
  s <-- get;
  set (f s)

let wrap_sos (f:machine_state -> option machine_state) : st unit =
  fun s -> (
      match f s with
      | None -> (), { s with ms_ok = false }
      | Some s' -> (), s'
    )

let lemma_feq_bounded_effects (rw:rw_set) (f1 f2:st unit) :
  Lemma
    (requires (bounded_effects rw f1 /\ FStar.FunctionalExtensionality.feq f1 f2))
    (ensures (bounded_effects rw f2)) =
  let open FStar.FunctionalExtensionality in
  assert (only_affects rw.loc_writes f2);
  let rec aux w s :
    Lemma
      (requires (feq f1 f2 /\ constant_on_execution w f1 s))
      (ensures (constant_on_execution w f2 s))
      [SMTPat (constant_on_execution w f2 s)] =
    match w with
    | [] -> ()
    | x :: xs -> aux xs s
  in
  assert (forall s. {:pattern (constant_on_execution rw.loc_constant_writes f2 s)}
            constant_on_execution rw.loc_constant_writes f2 s);
  assert (forall l v. {:pattern (L.mem (|l,v|) rw.loc_constant_writes); (L.mem l rw.loc_writes)}
            L.mem (|l,v|) rw.loc_constant_writes ==> L.mem l rw.loc_writes);
  assert (
    forall s1 s2. {:pattern (run f2 s1); (run f2 s2)} (
      (s1.ms_ok = s2.ms_ok /\ unchanged_at rw.loc_reads s1 s2) ==> (
        ((run f2 s1).ms_ok = (run f2 s2).ms_ok) /\
        ((run f2 s1).ms_ok ==>
         unchanged_at rw.loc_writes (run f2 s1) (run f2 s2))
      )
    )
  )

let rec safely_bounded_code_p (c:code) : bool =
  match c with
  | Ins i -> safely_bounded i
  | Block l -> safely_bounded_codes_p l
  | IfElse c t f -> false (* Temporarily disabled. TODO: Re-enable this. safely_bounded_code_p t && safely_bounded_code_p f *)
  | While c b -> false (* Temporarily disabled. TODO: Re-enable this. safely_bounded_code_p b *)

and safely_bounded_codes_p (l:codes) : bool =
  match l with
  | [] -> true
  | x :: xs ->
    safely_bounded_code_p x &&
    safely_bounded_codes_p xs

type safely_bounded_ins = (i:ins{safely_bounded i})
type safely_bounded_code = (c:code{safely_bounded_code_p c})
type safely_bounded_codes = (c:codes{safely_bounded_codes_p c})

let lemma_machine_eval_ins_bounded_effects (i:safely_bounded_ins) :
  Lemma
    (ensures (bounded_effects (rw_set_of_ins i) (wrap_ss (machine_eval_ins i)))) =
  lemma_machine_eval_ins_st_bounded_effects i;
  lemma_feq_bounded_effects (rw_set_of_ins i) (machine_eval_ins_st i) (wrap_ss (machine_eval_ins i))

let lemma_machine_eval_ins_st_exchange (i1 i2 : ins) (s : machine_state) :
  Lemma
    (requires (!!(ins_exchange_allowed i1 i2)))
    (ensures (commutes s
                (machine_eval_ins_st i1)
                (machine_eval_ins_st i2))) =
  lemma_machine_eval_ins_st_bounded_effects i1;
  lemma_machine_eval_ins_st_bounded_effects i2;
  let rw1 = rw_set_of_ins i1 in
  let rw2 = rw_set_of_ins i2 in
  lemma_commute (machine_eval_ins_st i1) (machine_eval_ins_st i2) rw1 rw2 s

let lemma_instruction_exchange' (i1 i2 : ins) (s1 s2 : machine_state) :
  Lemma
    (requires (
        !!(ins_exchange_allowed i1 i2) /\
        (equiv_states s1 s2)))
    (ensures (
        (let s1', s2' =
           machine_eval_ins i2 (machine_eval_ins i1 s1),
           machine_eval_ins i1 (machine_eval_ins i2 s2) in
         equiv_states_or_both_not_ok s1' s2'))) =
  lemma_machine_eval_ins_st_exchange i1 i2 s1;
  lemma_eval_ins_equiv_states i2 s1 s2;
  lemma_eval_ins_equiv_states i1 (machine_eval_ins i2 s1) (machine_eval_ins i2 s2)

let lemma_instruction_exchange (i1 i2 : ins) (s1 s2 : machine_state) :
  Lemma
    (requires (
        !!(ins_exchange_allowed i1 i2) /\
        (equiv_states s1 s2)))
    (ensures (
        (let s1', s2' =
           machine_eval_ins i2 (filt_state (machine_eval_ins i1 (filt_state s1))),
           machine_eval_ins i1 (filt_state (machine_eval_ins i2 (filt_state s2))) in
         equiv_states_or_both_not_ok s1' s2'))) =
  lemma_eval_ins_equiv_states i1 s1 (filt_state s1);
  lemma_eval_ins_equiv_states i2 s2 (filt_state s2);
  lemma_eval_ins_equiv_states i2 (machine_eval_ins i1 (filt_state s1)) (filt_state (machine_eval_ins i1 (filt_state s1)));
  lemma_eval_ins_equiv_states i1 (machine_eval_ins i2 (filt_state s2)) (filt_state (machine_eval_ins i2 (filt_state s2)));
  lemma_eval_ins_equiv_states i2 (machine_eval_ins i1 s1) (machine_eval_ins i1 (filt_state s1));
  lemma_eval_ins_equiv_states i1 (machine_eval_ins i2 s2) (machine_eval_ins i2 (filt_state s2));
  lemma_instruction_exchange' i1 i2 s1 s2

/// Not-ok states lead to erroring states upon execution

#push-options "--initial_fuel 2 --max_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let rec lemma_not_ok_propagate_code (c:code) (fuel:nat) (s:machine_state) :
  Lemma
    (requires (not s.ms_ok))
    (ensures (erroring_option_state (machine_eval_code c fuel s)))
    (decreases %[fuel; c; 1]) =
  match c with
  | Ins _ -> ()
  | Block l ->
    lemma_not_ok_propagate_codes l fuel s
  | IfElse ifCond ifTrue ifFalse ->
    let (st, b) = machine_eval_ocmp s ifCond in
    let s' = {st with ms_trace = (BranchPredicate b)::s.ms_trace} in
    if b then lemma_not_ok_propagate_code ifTrue fuel s' else lemma_not_ok_propagate_code ifFalse fuel s'
  | While _ _ ->
    lemma_not_ok_propagate_while c fuel s

and lemma_not_ok_propagate_codes (l:codes) (fuel:nat) (s:machine_state) :
  Lemma
    (requires (not s.ms_ok))
    (ensures (erroring_option_state (machine_eval_codes l fuel s)))
    (decreases %[fuel; l]) =
  match l with
  | [] -> ()
  | x :: xs ->
    lemma_not_ok_propagate_code x fuel s;
    match machine_eval_code x fuel s with
    | None -> ()
    | Some s -> lemma_not_ok_propagate_codes xs fuel s

and lemma_not_ok_propagate_while (c:code{While? c}) (fuel:nat) (s:machine_state) :
  Lemma
    (requires (not s.ms_ok))
    (ensures (erroring_option_state (machine_eval_code c fuel s)))
    (decreases %[fuel; c; 0]) =
  if fuel = 0 then () else (
    let While cond body = c in
    let (s, b) = machine_eval_ocmp s cond in
    if not b then () else (
      let s = { s with ms_trace = (BranchPredicate true) :: s.ms_trace } in
      lemma_not_ok_propagate_code body (fuel - 1) s
    )
  )
#pop-options

/// Given that we have bounded instructions, we can compute bounds on
/// [code] and [codes].

let rec rw_set_of_code (c:safely_bounded_code) : rw_set =
  match c with
  | Ins i -> rw_set_of_ins i
  | Block l -> rw_set_of_codes l
  | IfElse c t f ->
    add_r_to_rw_set
      (locations_of_ocmp c)
      (rw_set_in_parallel
         (rw_set_of_code t)
         (rw_set_of_code f))
  | While c b ->
    {
      add_r_to_rw_set
        (locations_of_ocmp c)
        (rw_set_of_code b)
      with
        loc_constant_writes = [] (* Since the loop may not execute, we are not sure of any constant writes *)
    }

and rw_set_of_codes (c:safely_bounded_codes) : rw_set =
  match c with
  | [] -> {
      loc_reads = [];
      loc_writes = [];
      loc_constant_writes = [];
    }
  | x :: xs ->
    rw_set_in_series
      (rw_set_of_code x)
      (rw_set_of_codes xs)

let lemma_bounded_effects_on_functional_extensionality (rw:rw_set) (f1 f2:st unit) :
  Lemma
    (requires (FStar.FunctionalExtensionality.feq f1 f2 /\ bounded_effects rw f1))
    (ensures (bounded_effects rw f2)) =
  let pre = FStar.FunctionalExtensionality.feq f1 f2 /\ bounded_effects rw f1 in
  assert (only_affects rw.loc_writes f1 <==> only_affects rw.loc_writes f2);
  let rec aux c s :
    Lemma
      (requires (pre /\ constant_on_execution c f1 s))
      (ensures (constant_on_execution c f2 s)) =
    match c with
    | [] -> ()
    | (|l,v|) :: xs ->
      aux xs s
  in
  let aux = FStar.Classical.move_requires (aux rw.loc_constant_writes) in
  FStar.Classical.forall_intro aux;
  let aux s1 s2 :
    Lemma
      (requires (pre /\ s1.ms_ok = s2.ms_ok /\ unchanged_at rw.loc_reads s1 s2 /\ (run f2 s1).ms_ok))
      (ensures (unchanged_at rw.loc_writes (run f2 s1) (run f2 s2))) = ()
  in
  let aux s1 = FStar.Classical.move_requires (aux s1) in
  FStar.Classical.forall_intro_2 aux

let lemma_only_affects_to_unchanged_except locs f s : (* REVIEW: Why is this even needed?! *)
  Lemma
    (requires (only_affects locs f /\ (run f s).ms_ok))
    (ensures (unchanged_except locs s (run f s))) = ()

let lemma_equiv_code_codes (c:code) (cs:codes) (fuel:nat) (s:machine_state) :
  Lemma
    (ensures (
        let open Vale.X64.Machine_Semantics_s in
        let f1 = wrap_sos (machine_eval_code c fuel) in
        let f2 = wrap_sos (machine_eval_codes cs fuel) in
        let f12 = wrap_sos (machine_eval_codes (c :: cs) fuel) in
        equiv_states_or_both_not_ok
          (run (f1;;f2) s)
          (run f12 s))) =
  let open Vale.X64.Machine_Semantics_s in
  let f1 = wrap_sos (machine_eval_code c fuel) in
  let f2 = wrap_sos (machine_eval_codes cs fuel) in
  let f12 = wrap_sos (machine_eval_codes (c :: cs) fuel) in
  let s_1 = run f1 s in
  let s_1_2 = run f2 s_1 in
  let s_12 = run (f1;;f2) s in
  let s12 = run f12 s in
  assert (s_12 == {s_1_2 with ms_ok = s.ms_ok && s_1.ms_ok && s_1_2.ms_ok});
  if s.ms_ok then (
    if s_1.ms_ok then () else (
      lemma_not_ok_propagate_codes cs fuel s_1
    )
  ) else (
    lemma_not_ok_propagate_code c fuel s;
    lemma_not_ok_propagate_codes cs fuel s_1;
    lemma_not_ok_propagate_codes (c :: cs) fuel s
  )

let lemma_bounded_effects_code_codes_aux1 (c:code) (cs:codes) (rw:rw_set) (fuel:nat) s a :
  Lemma
    (requires (
        let open Vale.X64.Machine_Semantics_s in
        let f1 = wrap_sos (machine_eval_code c fuel) in
        let f2 = wrap_sos (machine_eval_codes cs fuel) in
        let f12 = wrap_sos (machine_eval_codes (c :: cs) fuel) in
        (bounded_effects rw (f1 ;; f2)) /\
        !!(disjoint_location_from_locations a rw.loc_writes) /\
        (run f12 s).ms_ok))
    (ensures (
        let f12 = wrap_sos (machine_eval_codes (c :: cs) fuel) in
        eval_location a s == eval_location a (run f12 s))) =
  let open Vale.X64.Machine_Semantics_s in
  let f1 = wrap_sos (machine_eval_code c fuel) in
  let f2 = wrap_sos (machine_eval_codes cs fuel) in
  let f = (f1;;f2) in
  let f12 = wrap_sos (machine_eval_codes (c :: cs) fuel) in
  let s_12 = run (f1;;f2) s in
  let s12 = run f12 s in
  lemma_equiv_code_codes c cs fuel s;
  assert (equiv_states_or_both_not_ok s_12 s12);
  lemma_only_affects_to_unchanged_except rw.loc_writes f s

let rec lemma_bounded_effects_code_codes_aux2 (c:code) (cs:codes) (fuel:nat) cw s :
  Lemma
    (requires (
        let open Vale.X64.Machine_Semantics_s in
        let f1 = wrap_sos (machine_eval_code c fuel) in
        let f2 = wrap_sos (machine_eval_codes cs fuel) in
        (constant_on_execution cw (f1;;f2) s)))
    (ensures (
        let f12 = wrap_sos (machine_eval_codes (c :: cs) fuel) in
        (constant_on_execution cw f12 s))) =
  let open Vale.X64.Machine_Semantics_s in
  let f1 = wrap_sos (machine_eval_code c fuel) in
  let f2 = wrap_sos (machine_eval_codes cs fuel) in
  let f = (f1;;f2) in
  let f12 = wrap_sos (machine_eval_codes (c :: cs) fuel) in
  lemma_equiv_code_codes c cs fuel s;
  if (run f s).ms_ok then (
    match cw with
    | [] -> ()
    | (|l, v|) :: xs -> (
        lemma_bounded_effects_code_codes_aux2 c cs fuel xs s
      )
  ) else ()

let lemma_unchanged_at_reads_implies_both_ok_equal (rw:rw_set) (f:st unit) s1 s2 : (* REVIEW: Why is this necessary?! *)
  Lemma
    (requires (bounded_effects rw f /\ s1.ms_ok = s2.ms_ok /\ unchanged_at rw.loc_reads s1 s2))
    (ensures (
        ((run f s1).ms_ok = (run f s2).ms_ok) /\
        ((run f s1).ms_ok ==>
         unchanged_at rw.loc_writes (run f s1) (run f s2)))) = ()

let lemma_bounded_effects_code_codes_aux3 (c:code) (cs:codes) (rw:rw_set) (fuel:nat) s1 s2 :
  Lemma
    (requires (
        let open Vale.X64.Machine_Semantics_s in
        let f1 = wrap_sos (machine_eval_code c fuel) in
        let f2 = wrap_sos (machine_eval_codes cs fuel) in
        (bounded_effects rw (f1 ;; f2)) /\
        s1.ms_ok = s2.ms_ok /\ unchanged_at rw.loc_reads s1 s2))
    (ensures (
        let open Vale.X64.Machine_Semantics_s in
        let f1 = wrap_sos (machine_eval_code c fuel) in
        let f2 = wrap_sos (machine_eval_codes cs fuel) in
        let f12 = wrap_sos (machine_eval_codes (c :: cs) fuel) in
        (run f12 s1).ms_ok = (run f12 s2).ms_ok /\
        (run (f1 ;; f2) s1).ms_ok = (run f12 s1).ms_ok)) =
  let open Vale.X64.Machine_Semantics_s in
  let f1 = wrap_sos (machine_eval_code c fuel) in
  let f2 = wrap_sos (machine_eval_codes cs fuel) in
  let f = (f1;;f2) in
  let f12 = wrap_sos (machine_eval_codes (c :: cs) fuel) in
  let pre = bounded_effects rw f in
  lemma_equiv_code_codes c cs fuel s1;
  lemma_equiv_code_codes c cs fuel s2;
  assert ((run f s1).ms_ok == (run f12 s1).ms_ok);
  assert ((run f s2).ms_ok == (run f12 s2).ms_ok);
  lemma_unchanged_at_reads_implies_both_ok_equal rw f s1 s2

let lemma_bounded_effects_code_codes_aux4 (c:code) (cs:codes) (rw:rw_set) (fuel:nat) s1 s2 :
  Lemma
    (requires (
        let open Vale.X64.Machine_Semantics_s in
        let f1 = wrap_sos (machine_eval_code c fuel) in
        let f2 = wrap_sos (machine_eval_codes cs fuel) in
        (bounded_effects rw (f1 ;; f2)) /\
        s1.ms_ok = s2.ms_ok /\ unchanged_at rw.loc_reads s1 s2 /\ (run (f1 ;; f2) s1).ms_ok))
    (ensures (
        let f12 = wrap_sos (machine_eval_codes (c :: cs) fuel) in
        unchanged_at rw.loc_writes (run f12 s1) (run f12 s2))) =
  let open Vale.X64.Machine_Semantics_s in
  let f1 = wrap_sos (machine_eval_code c fuel) in
  let f2 = wrap_sos (machine_eval_codes cs fuel) in
  let f = (f1;;f2) in
  let f12 = wrap_sos (machine_eval_codes (c :: cs) fuel) in
  let pre = bounded_effects rw f in
  lemma_equiv_code_codes c cs fuel s1;
  lemma_equiv_code_codes c cs fuel s2;
  lemma_unchanged_at_reads_implies_both_ok_equal rw f s1 s2;
  assert (run f12 s1).ms_ok;
  assert (run f12 s2).ms_ok;
  assert (unchanged_at rw.loc_writes (run f s1) (run f s2));
  assert (run f s1 == run f12 s1);
  assert (run f s2 == run f12 s2)

let lemma_bounded_effects_code_codes (c:code) (cs:codes) (rw:rw_set) (fuel:nat) :
  Lemma
    (requires (
        let open Vale.X64.Machine_Semantics_s in
        let f1 = wrap_sos (machine_eval_code c fuel) in
        let f2 = wrap_sos (machine_eval_codes cs fuel) in
        (bounded_effects rw (f1 ;; f2))))
    (ensures (
        let f12 = wrap_sos (machine_eval_codes (c :: cs) fuel) in
        bounded_effects rw f12)) =
  let open Vale.X64.Machine_Semantics_s in
  let f1 = wrap_sos (machine_eval_code c fuel) in
  let f2 = wrap_sos (machine_eval_codes cs fuel) in
  let f = f1;;f2 in
  let f12 = wrap_sos (machine_eval_codes (c :: cs) fuel) in
  let pre = bounded_effects rw f in
  let aux s = FStar.Classical.move_requires (lemma_bounded_effects_code_codes_aux1 c cs rw fuel s) in
  FStar.Classical.forall_intro_2 aux;
  let aux = FStar.Classical.move_requires (lemma_bounded_effects_code_codes_aux2 c cs fuel rw.loc_constant_writes) in
  FStar.Classical.forall_intro aux;
  let aux s1 = FStar.Classical.move_requires (lemma_bounded_effects_code_codes_aux3 c cs rw fuel s1) in
  FStar.Classical.forall_intro_2 aux;
  let aux s1 = FStar.Classical.move_requires (lemma_bounded_effects_code_codes_aux4 c cs rw fuel s1) in
  FStar.Classical.forall_intro_2 aux

let rec lemma_bounded_code (c:safely_bounded_code) (fuel:nat) :
  Lemma
    (ensures (bounded_effects (rw_set_of_code c) (wrap_sos (machine_eval_code c fuel))))
    (decreases %[c]) =
  match c with
  | Ins i ->
    lemma_machine_eval_code_Ins_bounded_effects i fuel;
    lemma_bounded_effects_on_functional_extensionality
      (rw_set_of_ins i)
      (fun s -> (), (Some?.v (machine_eval_code (Ins i) fuel s)))
      (wrap_sos (machine_eval_code c fuel))
  | Block l ->
    lemma_bounded_codes l fuel;
    lemma_bounded_effects_on_functional_extensionality
      (rw_set_of_codes l)
      (wrap_sos (machine_eval_codes l fuel))
      (wrap_sos (machine_eval_code (Block l) fuel))
  | IfElse c t f -> ()
  | While c b -> ()

and lemma_bounded_codes (c:safely_bounded_codes) (fuel:nat) :
  Lemma
    (ensures (bounded_effects (rw_set_of_codes c) (wrap_sos (machine_eval_codes c fuel))))
    (decreases %[c]) =
  let open Vale.X64.Machine_Semantics_s in
  match c with
  | [] -> ()
  | x :: xs ->
    lemma_bounded_code x fuel;
    lemma_bounded_codes xs fuel;
    lemma_bounded_effects_series
      (rw_set_of_code x)
      (rw_set_of_codes xs)
      (wrap_sos (machine_eval_code x fuel))
      (wrap_sos (machine_eval_codes xs fuel));
    lemma_bounded_effects_code_codes x xs (rw_set_of_codes c) fuel

/// Given that we can perform simple swaps between instructions, we
/// can do swaps between [code]s.

let code_exchange_allowed (c1 c2:safely_bounded_code) : pbool =
  rw_exchange_allowed (rw_set_of_code c1) (rw_set_of_code c2)
  /+> normal (" for instructions " ^ fst (print_code c1 0 gcc) ^ " and " ^ fst (print_code c2 0 gcc))

#push-options "--initial_fuel 3 --max_fuel 3 --initial_ifuel 0 --max_ifuel 0"
let lemma_code_exchange_allowed (c1 c2:safely_bounded_code) (fuel:nat) (s:machine_state) :
  Lemma
    (requires (
        !!(code_exchange_allowed c1 c2)))
    (ensures (
        equiv_option_states
          (machine_eval_codes [c1; c2] fuel s)
          (machine_eval_codes [c2; c1] fuel s))) =
  lemma_bounded_code c1 fuel;
  lemma_bounded_code c2 fuel;
  let f1 = wrap_sos (machine_eval_code c1 fuel) in
  let f2 = wrap_sos (machine_eval_code c2 fuel) in
  lemma_commute f1 f2 (rw_set_of_code c1) (rw_set_of_code c2) s;
  assert (equiv_states_or_both_not_ok (run2 f1 f2 s) (run2 f2 f1 s));
  let s1 = run f1 s in
  let s12 = run f2 s1 in
  let s2 = run f2 s in
  let s21 = run f1 s2 in
  FStar.Classical.move_requires (lemma_not_ok_propagate_code c1 fuel) s;
  FStar.Classical.move_requires (lemma_not_ok_propagate_code c2 fuel) s1;
  FStar.Classical.move_requires (lemma_not_ok_propagate_code c2 fuel) s;
  FStar.Classical.move_requires (lemma_not_ok_propagate_code c1 fuel) s2;
  FStar.Classical.move_requires (lemma_not_ok_propagate_codes [c1;c2] fuel) s;
  FStar.Classical.move_requires (lemma_not_ok_propagate_codes [c2;c1] fuel) s
#pop-options

/// Given that we can perform simple swaps between [code]s, we can
/// define a relation that tells us if some [codes] can be transformed
/// into another using only allowed swaps.

#push-options "--initial_fuel 2 --max_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let rec bubble_to_top (cs:codes) (i:nat{i < L.length cs}) : possibly (cs':codes{
    let a, b, c = L.split3 cs i in
    cs' == L.append a c /\
    L.length cs' = L.length cs - 1
  }) =
  match cs with
  | [_] -> return []
  | h :: t ->
    if i = 0 then (
      return t
    ) else (
      let x = L.index cs i in
      if not (safely_bounded_code_p x) then (
        Err ("Cannot safely move " ^ fst (print_code x 0 gcc))
      ) else (
        if not (safely_bounded_code_p h) then (
          Err ("Cannot safely move beyond " ^ fst (print_code h 0 gcc))
        ) else (
          match bubble_to_top t (i - 1) with
          | Err reason -> Err reason
          | Ok res ->
            match code_exchange_allowed x h with
            | Err reason -> Err reason
            | Ok () ->
              return (h :: res)
        )
      )
    )
#pop-options

let rec num_blocks_in_codes (c:codes) : nat =
  match c with
  | [] -> 0
  | Block l :: t -> 1 + num_blocks_in_codes l + num_blocks_in_codes t
  | _ :: t -> num_blocks_in_codes t

let rec lemma_num_blocks_in_codes_append (c1 c2:codes) :
  Lemma
    (ensures (num_blocks_in_codes (c1 `L.append` c2) == num_blocks_in_codes c1 + num_blocks_in_codes c2))
    [SMTPat (num_blocks_in_codes (c1 `L.append` c2))] =
  match c1 with
  | [] -> ()
  | x :: xs -> lemma_num_blocks_in_codes_append xs c2

type transformation_hint =
  | MoveUpFrom : p:nat -> transformation_hint
  | DiveInAt : p:nat -> q:transformation_hint -> transformation_hint
  | InPlaceIfElse : ifTrue:transformation_hints -> ifFalse:transformation_hints -> transformation_hint
  | InPlaceWhile : whileBody:transformation_hints -> transformation_hint

and transformation_hints = list transformation_hint

let rec string_of_transformation_hint (th:transformation_hint) :
  Tot string
    (decreases %[th]) =
  match th with
  | MoveUpFrom p -> "(MoveUpFrom " ^ string_of_int p ^ ")"
  | DiveInAt p q -> "(DiveInAt " ^ string_of_int p ^ " " ^ string_of_transformation_hint q ^ ")"
  | InPlaceIfElse tr fa -> "(InPlaceIfElse " ^ string_of_transformation_hints tr ^ " " ^ string_of_transformation_hints fa ^ ")"
  | InPlaceWhile bo -> "(InPlaceWhile " ^ string_of_transformation_hints bo ^ ")"

and aux_string_of_transformation_hints (ts:transformation_hints) :
  Tot string
    (decreases %[ts; 0]) =
  match ts with
  | [] -> ""
  | x :: xs -> string_of_transformation_hint x ^ "; " ^ aux_string_of_transformation_hints xs

and string_of_transformation_hints (ts:transformation_hints) :
  Tot string
    (decreases %[ts; 1]) =
  "[" ^ aux_string_of_transformation_hints ts ^ "]"

let rec wrap_diveinat (p:nat) (l:transformation_hints) : transformation_hints =
  match l with
  | [] -> []
  | x :: xs ->
    DiveInAt p x :: wrap_diveinat p xs

(* XXX: Copied from List.Tot.Base because of an extraction issue.
   See https://github.com/FStarLang/FStar/pull/1822. *)
val split3: #a:Type -> l:list a -> i:nat{i < L.length l} -> Tot (list a * a * list a)
let split3 #a l i =
  let a, as = L.splitAt i l in
  L.lemma_splitAt_snd_length i l;
  let b :: c = as in
  a, b, c

let rec is_empty_code (c:code) : bool =
  match c with
  | Ins _ -> false
  | Block l -> is_empty_codes l
  | IfElse _ t f -> false
  | While _ c -> false

and is_empty_codes (c:codes) : bool =
  match c with
  | [] -> true
  | x :: xs -> is_empty_code x && is_empty_codes xs

let rec perform_reordering_with_hint (t:transformation_hint) (c:codes) : possibly codes =
  match c with
  | [] -> Err "trying to transform empty code"
  | x :: xs ->
    if is_empty_codes [x] then perform_reordering_with_hint t xs else (
      match t with
      | MoveUpFrom i -> (
          if i < L.length c then (
            c' <-- bubble_to_top c i;
            return (L.index c i :: c')
          ) else (
            Err ("invalid hint : " ^ string_of_transformation_hint t)
          )
        )
      | DiveInAt i t' ->
        if i < L.length c then (
          FStar.List.Pure.lemma_split3_length c i;
          let left, mid, right = split3 c i in
          match mid with
          | Block l ->
            l' <-- perform_reordering_with_hint t' l; (
              match l' with
              | [] -> Err "impossible"
              | y :: ys ->
                L.append_length left [y];
                left' <-- bubble_to_top (left `L.append` [y]) i;
                return (y :: (left' `L.append` (Block ys :: right)))
            )
          | _ ->
            Err ("trying to dive into a non-block : " ^ string_of_transformation_hint t ^ " " ^ fst (print_code (Block c) 0 gcc))
        ) else (
          Err ("invalid hint : " ^ string_of_transformation_hint t)
        )
      | InPlaceIfElse tht thf -> (
          match x with
          | IfElse c (Block t) (Block f) ->
            tt <-- perform_reordering_with_hints tht t;
            ff <-- perform_reordering_with_hints thf f;
            return (IfElse c (Block tt) (Block ff) :: xs)
          | _ ->
            Err ("Invalid hint : " ^ string_of_transformation_hint t ^ " for codes " ^ fst (print_code (Block c) 0 gcc))
        )
      | InPlaceWhile thb -> (
          match x with
          | While c (Block b) ->
            bb <-- perform_reordering_with_hints thb b;
            return (While c (Block bb) :: xs)
          | _ ->
            Err ("Invalid hint : " ^ string_of_transformation_hint t ^ " for codes " ^ fst (print_code (Block c) 0 gcc))
        )
    )

and perform_reordering_with_hints (ts:transformation_hints) (c:codes) : possibly codes =
  (*
  let _ = IO.debug_print_string (
      "-----------------------------\n" ^
      " th : " ^ string_of_transformation_hints ts ^ "\n" ^
      " c  :\n" ^
      fst (print_code (Block c) 0 gcc) ^ "\n" ^
      "-----------------------------\n" ^
      "") in
  *)
  match ts with
  | [] -> (
      if is_empty_codes c then (
        return []
      ) else (
        (*
        let _ = IO.debug_print_string (
            "failed here!!!\n" ^
            "\n") in
        *)
        Err ("no more transformation hints for " ^ fst (print_code (Block c) 0 gcc))
      )
    )
  | t :: ts' ->
    c' <-- perform_reordering_with_hint t c;
    match c' with
    | [] -> Err "impossible"
    | x :: xs ->
      if is_empty_codes [x] then (
        Err "Trying to move 'empty' code."
      ) else (
      (*
        let _ = IO.debug_print_string (
            "dragged up: \n" ^
            fst (print_code x 0 gcc) ^
            "\n") in
        *)
        xs' <-- perform_reordering_with_hints ts' xs;
        return (x :: xs')
      )

(* NOTE: We assume this function since it is not yet exposed. Once
   exposed from the instructions module, we should be able to remove
   it from here.

   Also, note that we don't require any other properties from
   [eq_ins]. It is an uninterpreted function that simply gives us a
   "hint" to find equivalent instructions!

   For testing purposes, we have it set to an [irreducible] function
   that looks at the printed representation of the instructions. Since
   it is irreducible, no other function should be able to "look into"
   the definition of this function, but instead should be limited only
   to its signature. However, the OCaml extraction _should_ be able to
   peek inside, and be able to proceed. *)
irreducible
let eq_ins (i1 i2:ins) : bool =
  print_ins i1 gcc = print_ins i2 gcc

let rec eq_code (c1 c2:code) : bool =
  match c1, c2 with
  | Ins i1, Ins i2 -> eq_ins i1 i2
  | Block l1, Block l2 -> eq_codes l1 l2
  | IfElse c1 t1 f1, IfElse c2 t2 f2 -> c1 = c2 && eq_code t1 t2 && eq_code f1 f2
  | While c1 b1, While c2 b2 -> c1 = c2 && eq_code b1 b2
  | _, _ -> false

and eq_codes (c1 c2:codes) : bool =
  match c1, c2 with
  | [], [] -> true
  | _, [] | [], _ -> false
  | x :: xs, y :: ys ->
    eq_code x y &&
    eq_codes xs ys

let rec fully_unblocked_code (c:code) : codes =
  match c with
  | Ins i -> [c]
  | Block l -> fully_unblocked_codes l
  | IfElse c t f -> [IfElse c (Block (fully_unblocked_code t)) (Block (fully_unblocked_code f))]
  | While c b -> [While c (Block (fully_unblocked_code b))]

and fully_unblocked_codes (c:codes) : codes =
  match c with
  | [] -> []
  | x :: xs ->
    fully_unblocked_code x `L.append` fully_unblocked_codes xs

let increment_hint (th:transformation_hint) : transformation_hint =
  match th with
  | MoveUpFrom p -> MoveUpFrom (p + 1)
  | DiveInAt p q -> DiveInAt (p + 1) q
  | _ -> th

let rec find_deep_code_transform (c:code) (cs:codes) : possibly transformation_hint =
  match cs with
  | [] ->
    Err ("Not found (during find_deep_code_transform): " ^ fst (print_code c 0 gcc))
  | x :: xs ->
    (*
    let _ = IO.debug_print_string (
        "---------------------------------\n" ^
        " c : \n" ^
        fst (print_code c 0 gcc) ^ "\n" ^
        " x : \n" ^
        fst (print_code x 0 gcc) ^ "\n" ^
        " xs : \n" ^
        fst (print_code (Block xs) 0 gcc) ^ "\n" ^
        "---------------------------------\n" ^
        "") in
    *)
    if is_empty_code x then find_deep_code_transform c xs else (
      if eq_codes (fully_unblocked_code x) (fully_unblocked_code c) then (
        return (MoveUpFrom 0)
      ) else (
        match x with
        | Block l -> (
            match find_deep_code_transform c l with
            | Ok t ->
              return (DiveInAt 0 t)
            | Err reason ->
              th <-- find_deep_code_transform c xs;
              return (increment_hint th)
          )
        | _ ->
          th <-- find_deep_code_transform c xs;
          return (increment_hint th)
      )
    )

let rec metric_for_code (c:code) : GTot nat =
  1 + (
    match c with
    | Ins _ -> 0
    | Block l -> metric_for_codes l
    | IfElse _ t f -> metric_for_code t + metric_for_code f
    | While _ b -> metric_for_code b
  )

and metric_for_codes (c:codes) : GTot nat =
  match c with
  | [] -> 0
  | x :: xs -> 1 + metric_for_code x + metric_for_codes xs

let rec lemma_metric_for_codes_append (c1 c2:codes) :
  Lemma
    (ensures (metric_for_codes (c1 `L.append` c2) == metric_for_codes c1 + metric_for_codes c2))
    [SMTPat (metric_for_codes (c1 `L.append` c2))] =
  match c1 with
  | [] -> ()
  | x :: xs -> lemma_metric_for_codes_append xs c2

irreducible
(* Our proofs do not depend on how the hints are found. As long as
   some hints are provided, we validate the hints to perform the
   transformation and use it. Thus, we make this function
   [irreducible] to explicitly prevent any of the proofs from
   reasoning about it. *)
let rec find_transformation_hints (c1 c2:codes) :
  Tot (possibly transformation_hints)
    (decreases %[metric_for_codes c2; metric_for_codes c1]) =
  let e1, e2 = is_empty_codes c1, is_empty_codes c2 in
  if e1 && e2 then (
    return []
  ) else if e2 then (
    Err ("non empty first code: " ^ fst (print_code (Block c1) 0 gcc))
  ) else if e1 then (
    Err ("non empty second code: " ^ fst (print_code (Block c2) 0 gcc))
  ) else (
    let h1 :: t1 = c1 in
    let h2 :: t2 = c2 in
    assert (metric_for_codes c2 >= metric_for_code h2); (* OBSERVE *)
    if is_empty_code h1 then (
      find_transformation_hints t1 c2
    ) else if is_empty_code h2 then (
      find_transformation_hints c1 t2
    ) else (
      match find_deep_code_transform h2 c1 with
      | Ok th -> (
          match perform_reordering_with_hint th c1 with
          | Ok (h1 :: t1) ->
            t_hints2 <-- find_transformation_hints t1 t2;
            return (th :: t_hints2)
          | Ok [] -> Err "Impossible"
          | Err reason ->
            Err ("Unable to find valid movement for : " ^ fst (print_code h2 0 gcc) ^ ". Reason: " ^ reason)
        )
      | Err reason -> (
          let h1 :: t1 = c1 in
          match h1, h2 with
          | Block l1, Block l2 -> (
              match (
                t_hints1 <-- find_transformation_hints l1 l2;
                t_hints2 <-- find_transformation_hints t1 t2;
                return (wrap_diveinat 0 t_hints1 `L.append` t_hints2)
              ) with
              | Ok ths -> return ths
              | Err reason ->
                find_transformation_hints c1 (l2 `L.append` t2)
            )
          | IfElse co1 (Block tr1) (Block fa1), IfElse co2 (Block tr2) (Block fa2) ->
            (co1 = co2) /- ("Non-same conditions for IfElse: (" ^
                            print_cmp co1 0 gcc ^ ") and (" ^ print_cmp co2 0 gcc ^ ")");;
            assert (metric_for_code h2 > metric_for_code (Block tr2)); (* OBSERVE *)
            assert (metric_for_code h2 > metric_for_code (Block fa2)); (* OBSERVE *)
            tr_hints <-- find_transformation_hints tr1 tr2;
            fa_hints <-- find_transformation_hints fa1 fa2;
            t_hints2 <-- find_transformation_hints t1 t2;
            return (InPlaceIfElse tr_hints fa_hints :: t_hints2)
          | While co1 (Block bo1), While co2 (Block bo2) ->
            (co1 = co2) /- ("Non-same conditions for While: (" ^
                            print_cmp co1 0 gcc ^ ") and (" ^ print_cmp co2 0 gcc ^ ")");;
            assert (metric_for_code h2 > metric_for_code (Block bo2)); (* OBSERVE *)
            bo_hints <-- find_transformation_hints bo1 bo2;
            t_hints2 <-- find_transformation_hints t1 t2;
            return (InPlaceWhile bo_hints :: t_hints2)
          | Block l1, IfElse _ _ _
          | Block l1, While _ _ ->
            assert (metric_for_codes (l1 `L.append` t1) == metric_for_codes l1 + metric_for_codes t1); (* OBSERVE *)
            assert_norm (metric_for_codes c1 == 2 + metric_for_codes l1 + metric_for_codes t1); (* OBSERVE *)
            t_hints1 <-- find_transformation_hints (l1 `L.append` t1) c2;
            (
              match t_hints1 with
              | [] -> Err "Impossible"
              | th :: _ ->
                let th = DiveInAt 0 th in
                match perform_reordering_with_hint th c1 with
                | Ok (h1 :: t1) ->
                  t_hints2 <-- find_transformation_hints t1 t2;
                  return (th :: t_hints2)
                | Ok [] -> Err "Impossible"
                | Err reason ->
                  Err ("Failed during left-unblock for " ^ fst (print_code h2 0 gcc) ^ ". Reason: " ^ reason)
            )
          | _, Block l2 ->
            find_transformation_hints c1 (l2 `L.append` t2)
          | IfElse _ _ _, IfElse _ _ _
          | While _ _, While _ _ ->
            Err ("Found weird non-standard code: " ^ fst (print_code h1 0 gcc))
          | _ ->
            Err ("Find deep code failure. Reason: " ^ reason)
        )
    )
  )

/// If a transformation can be performed, then the result behaves
/// identically as per the [equiv_states] relation.

#push-options "--z3rlimit 10 --initial_fuel 3 --max_fuel 3 --initial_ifuel 1 --max_ifuel 1"
let rec lemma_bubble_to_top (cs : codes) (i:nat{i < L.length cs}) (fuel:nat) (s s' : machine_state) :
  Lemma
    (requires (
        (s'.ms_ok) /\
        (Some s' == machine_eval_codes cs fuel s) /\
        (Ok? (bubble_to_top cs i))))
    (ensures (
        let x = L.index cs i in
        let Ok xs = bubble_to_top cs i in
        let s1' = machine_eval_code x fuel s in
        (Some? s1') /\ (
          let Some s1 = s1' in
          let s2' = machine_eval_codes xs fuel s1 in
          (Some? s2') /\ (
            let Some s2 = s2' in
            equiv_states s' s2)))) =
  match cs with
  | [_] -> ()
  | h :: t ->
    let x = L.index cs i in
    let Ok xs = bubble_to_top cs i in
    if i = 0 then () else (
      let Some s_h = machine_eval_code h fuel s in
      lemma_bubble_to_top (L.tl cs) (i-1) fuel s_h s';
      let Some s_h_x = machine_eval_code x fuel s_h in
      let Some s_hx = machine_eval_codes [h;x] fuel s in
      assert (s_h_x == s_hx);
      lemma_code_exchange_allowed x h fuel s;
      FStar.Classical.move_requires (lemma_not_ok_propagate_codes (L.tl xs) fuel) s_hx;
      assert (s_hx.ms_ok);
      let Some s_xh = machine_eval_codes [x;h] fuel s in
      lemma_eval_codes_equiv_states (L.tl xs) fuel s_hx s_xh
    )
#pop-options

#push-options "--initial_fuel 3 --max_fuel 3 --initial_ifuel 1 --max_ifuel 1"
let rec lemma_machine_eval_codes_block_to_append (c1 c2 : codes) (fuel:nat) (s:machine_state) :
  Lemma
    (ensures (machine_eval_codes (c1 `L.append` c2) fuel s == machine_eval_codes (Block c1 :: c2) fuel s)) =
  match c1 with
  | [] -> ()
  | x :: xs ->
    match machine_eval_code x fuel s with
    | None -> ()
    | Some s1 ->
      lemma_machine_eval_codes_block_to_append xs c2 fuel s1
#pop-options

let rec lemma_append_single (xs:list 'a) (y:'a) (i:nat) :
  Lemma
    (requires (i == L.length xs))
    (ensures (
        L.length (xs `L.append` [y]) = L.length xs + 1 /\
        L.index (xs `L.append` [y]) i == y)) =
  match xs with
  | [] -> ()
  | x :: xs -> lemma_append_single xs y (i - 1)

#push-options "--initial_fuel 3 --max_fuel 3 --initial_ifuel 1 --max_ifuel 1"
let rec lemma_is_empty_code (c:code) (fuel:nat) (s:machine_state) :
  Lemma
    (requires (is_empty_code c))
    (ensures ((machine_eval_code c fuel s) == (machine_eval_codes [] fuel s))) =
  match c with
  | Ins _ -> ()
  | Block l -> lemma_is_empty_codes l fuel s
  | IfElse _ t f -> ()
  | While _ c -> ()
and lemma_is_empty_codes (cs:codes) (fuel:nat) (s:machine_state) :
  Lemma
    (requires (is_empty_codes cs))
    (ensures ((machine_eval_codes cs fuel s) == (machine_eval_codes [] fuel s))) =
  match cs with
  | [] -> ()
  | x :: xs ->
    lemma_is_empty_code x fuel s;
    lemma_is_empty_codes xs fuel s
#pop-options

#restart-solver
#push-options "--z3rlimit 100 --initial_fuel 3 --max_fuel 3 --initial_ifuel 1 --max_ifuel 1"
let rec lemma_perform_reordering_with_hint (t:transformation_hint) (cs:codes) (fuel:nat) (s:machine_state) :
  Lemma
    (requires (
        (Ok? (perform_reordering_with_hint t cs)) /\
        (Some? (machine_eval_codes cs fuel s)) /\
        (Some?.v (machine_eval_codes cs fuel s)).ms_ok))
    (ensures (
        let Ok cs' = perform_reordering_with_hint t cs in
        equiv_ostates
          (machine_eval_codes cs fuel s)
          (machine_eval_codes cs' fuel s)))
    (decreases %[t; fuel; cs]) =
  let c = cs in
  let Ok cs' = perform_reordering_with_hint t cs in
  let Some s' = machine_eval_codes cs fuel s in
  let x :: xs = cs in
  if is_empty_codes [x] then (
    lemma_is_empty_codes [x] fuel s;
    match machine_eval_code x fuel s with
    | None -> ()
    | Some s' ->
      lemma_eval_codes_equiv_states xs fuel s s';
      lemma_perform_reordering_with_hint t xs fuel s
  ) else (
    match t with
    | MoveUpFrom i -> (
        let Ok c' = bubble_to_top c i in
        lemma_bubble_to_top c i fuel s s'
      )
    | DiveInAt i t' -> (
        FStar.List.Pure.lemma_split3_append c i;
        FStar.List.Pure.lemma_split3_length c i;
        let left, mid, right = L.split3 c i in
        let Block l = mid in
        let Ok (y :: ys) = perform_reordering_with_hint t' l in
        L.append_length left [y];
        let Ok left' = bubble_to_top (left `L.append` [y]) i in
        //
        assert (cs' == y :: (left' `L.append` (Block ys :: right)));
        assert (left `L.append` (mid :: right) == c);
        L.append_l_cons mid right left;
        assert ((left `L.append` [mid]) `L.append` right == c);
        lemma_machine_eval_codes_block_to_append (left `L.append` [mid]) right fuel s;
        let Some s_1 = machine_eval_code (Block (left `L.append` [mid])) fuel s in
        assert (Some s_1 == machine_eval_codes (left `L.append` [mid]) fuel s);
        lemma_machine_eval_codes_block_to_append left [mid] fuel s;
        let Some s_2 = machine_eval_code (Block left) fuel s in
        assert (Some s_2 == machine_eval_codes left fuel s);
        //
        assert (Some s_1 == machine_eval_codes [mid] fuel s_2);
        assert (Some s_1 == machine_eval_code (Block l) fuel s_2);
        assert (Some s_1 == machine_eval_codes l fuel s_2);
        assert (Some s' == machine_eval_codes right fuel s_1);
        if s_1.ms_ok then () else lemma_not_ok_propagate_codes right fuel s_1;
        lemma_perform_reordering_with_hint t' l fuel s_2;
        //
        let Some s_11 = machine_eval_codes (y :: ys) fuel s_2 in
        let Some s_12 = machine_eval_code y fuel s_2 in
        if s_12.ms_ok then () else lemma_not_ok_propagate_codes ys fuel s_12;
        assert (Some s_2 == machine_eval_codes left fuel s);
        assert (Some s_2 == machine_eval_code (Block left) fuel s);
        assert (Some s_12 == machine_eval_codes (Block left :: [y]) fuel s);
        lemma_machine_eval_codes_block_to_append left [y] fuel s;
        assert (Some s_12 == machine_eval_codes (left `L.append` [y]) fuel s);
        lemma_bubble_to_top (left `L.append` [y]) i fuel s s_12;
        //
        lemma_append_single left y i;
        assert (L.index (left `L.append` [y]) i == y);
        //
        let Some s_3 = machine_eval_codes (y :: left') fuel s in
        assert (equiv_states s_3 s_12);
        lemma_eval_codes_equiv_states right fuel s_1 s_11;
        let Some s_0 = machine_eval_codes right fuel s_11 in
        lemma_eval_codes_equiv_states (Block ys :: right) fuel s_12 s_3;
        let Some s_00 = machine_eval_codes (Block ys :: right) fuel s_3 in
        //
        assert (equiv_states s_00 s');
        assert (Some s_3 == machine_eval_code (Block (y :: left')) fuel s);
        assert (Some s_00 == machine_eval_codes (Block ys :: right) fuel s_3);
        lemma_machine_eval_codes_block_to_append (y :: left') (Block ys :: right) fuel s
      )
    | InPlaceIfElse tht thf -> (
        let IfElse cond c_ift c_iff :: xs = cs in
        let Block cs_ift, Block cs_iff = c_ift, c_iff in
        let (st, b) = machine_eval_ocmp s cond in
        let s1 = {st with ms_trace = (BranchPredicate b)::s.ms_trace} in
        if b then (
          assert (Some s' == machine_eval_codes (c_ift :: xs) fuel s1);
          let Some s'' = machine_eval_code c_ift fuel s1 in
          if not s''.ms_ok then (lemma_not_ok_propagate_codes xs fuel s'') else ();
          lemma_perform_reordering_with_hints tht cs_ift fuel s1;
          let Some s''' = machine_eval_code (IfElse cond c_ift c_iff) fuel s in
          let x' :: _ = cs' in
          let Some s'''' = machine_eval_code x' fuel s in
          assert (equiv_states s''' s'''');
          lemma_eval_codes_equiv_states xs fuel s''' s''''
        ) else (
          let Some s'' = machine_eval_code c_iff fuel s1 in
          if not s''.ms_ok then (lemma_not_ok_propagate_codes xs fuel s'') else ();
          lemma_perform_reordering_with_hints thf cs_iff fuel s1;
          let Some s''' = machine_eval_code (IfElse cond c_ift c_iff) fuel s in
          let x' :: _ = cs' in
          let Some s'''' = machine_eval_code x' fuel s in
          lemma_eval_codes_equiv_states xs fuel s''' s''''
        )
      )
    | InPlaceWhile thb -> (
        assert (fuel <> 0);
        let While cond body :: xs = cs in
        let Block cs_body = body in
        let (s0, b) = machine_eval_ocmp s cond in
        if not b then () else (
          let s0 = {s0 with ms_trace = (BranchPredicate true)::s0.ms_trace} in
          let Some s1 = machine_eval_code body (fuel - 1) s0 in
          if s1.ms_ok then () else lemma_not_ok_propagate_codes xs fuel s1;
          lemma_perform_reordering_with_hints thb cs_body (fuel - 1) s0;
          let x' :: xs' = cs' in
          assert (xs' == xs);
          let While cond' body' = x' in
          let cs_body' = body' in
          let Some s11 = machine_eval_code (While cond body) (fuel - 1) s1 in
          if s11.ms_ok then () else lemma_not_ok_propagate_codes xs fuel s11;
          assert (Some s' == machine_eval_codes xs fuel s11);
          lemma_perform_reordering_with_hint t [While cond body] (fuel - 1) s1;
          let Some s11' = machine_eval_code x' (fuel - 1) s1 in
          lemma_eval_codes_equiv_states xs fuel s11 s11';
          let Some s'' = machine_eval_codes xs fuel s11' in
          assert (machine_eval_codes cs fuel s == Some s');
          assert (equiv_states s' s'');
          let Some s1' = machine_eval_code body' (fuel - 1) s0 in
          lemma_eval_code_equiv_states x' (fuel-1) s1 s1';
          let Some s11'' = machine_eval_code x' (fuel-1) s1' in
          assert (machine_eval_codes cs' fuel s == machine_eval_codes xs fuel s11'');
          lemma_eval_codes_equiv_states xs fuel s11' s11''
        )
      )
  )

and lemma_perform_reordering_with_hints (ts:transformation_hints) (cs:codes) (fuel:nat) (s:machine_state) :
  Lemma
    (requires (
        (Ok? (perform_reordering_with_hints ts cs)) /\
        (Some? (machine_eval_codes cs fuel s)) /\
        (Some?.v (machine_eval_codes cs fuel s)).ms_ok))
    (ensures (
        let Ok cs' = perform_reordering_with_hints ts cs in
        equiv_ostates
          (machine_eval_codes cs fuel s)
          (machine_eval_codes cs' fuel s)))
    (decreases %[ts; fuel; cs]) =
  let c = cs in
  let Ok cs' = perform_reordering_with_hints ts cs in
  let Some s' = machine_eval_codes cs fuel s in
  match ts with
  | [] -> lemma_is_empty_codes cs fuel s
  | t :: ts' ->
    let Ok (x :: xs) = perform_reordering_with_hint t c in
    lemma_perform_reordering_with_hint t c fuel s;
    let Ok xs' = perform_reordering_with_hints ts' xs in
    let Some s1 = machine_eval_code x fuel s in
    lemma_perform_reordering_with_hints ts' xs fuel s1
#pop-options

/// Some convenience functions to be run before the pass, to ensure
/// that we don't have miscounting due to empty code.

let rec purge_empty_code (c:code) : code =
  match c with
  | Block l ->
    Block (purge_empty_codes l)
  | IfElse c t f ->
    IfElse c (purge_empty_code t) (purge_empty_code f)
  | While c b ->
    While c (purge_empty_code b)
  | _ ->
    c

and purge_empty_codes (cs:codes) : codes =
  match cs with
  | [] -> []
  | x :: xs ->
    if is_empty_code x then (
      purge_empty_codes xs
    ) else (
      purge_empty_code x :: purge_empty_codes xs
    )

#push-options "--initial_fuel 2 --max_fuel 2 --initial_ifuel 0 --initial_ifuel 0"
let rec lemma_purge_empty_code (c:code) (fuel:nat) (s:machine_state) :
  Lemma
    (ensures (machine_eval_code c fuel s == machine_eval_code (purge_empty_code c) fuel s))
    (decreases %[fuel; c; 1]) =
  match c with
  | Block l -> lemma_purge_empty_codes l fuel s
  | IfElse c t f ->
    let (st, b) = machine_eval_ocmp s c in
    let s' = {st with ms_trace = (BranchPredicate b)::s.ms_trace} in
    if b then lemma_purge_empty_code t fuel s' else lemma_purge_empty_code f fuel s'
  | While _ _ ->
    lemma_purge_empty_while c fuel s
  | _ -> ()

and lemma_purge_empty_codes (cs:codes) (fuel:nat) (s:machine_state) :
  Lemma
    (ensures (machine_eval_codes cs fuel s == machine_eval_codes (purge_empty_codes cs) fuel s))
    (decreases %[fuel; cs]) =
  match cs with
  | [] -> ()
  | x :: xs ->
    if is_empty_code x then (
      lemma_is_empty_code x fuel s;
      lemma_purge_empty_codes xs fuel s
    ) else (
      lemma_purge_empty_code x fuel s;
      match machine_eval_code x fuel s with
      | None -> ()
      | Some s' ->
        lemma_purge_empty_codes xs fuel s'
    )

and lemma_purge_empty_while (c:code{While? c}) (fuel:nat) (s0:machine_state) :
  Lemma
    (ensures (machine_eval_code c fuel s0 == machine_eval_code (purge_empty_code c) fuel s0))
    (decreases %[fuel; c; 0]) =
  if fuel = 0 then () else (
    let While cond body = c in
    let (s0, b) = machine_eval_ocmp s0 cond in
    if not b then ()
    else
      let s0 = {s0 with ms_trace = (BranchPredicate true)::s0.ms_trace} in
      let s_opt = machine_eval_code body (fuel - 1) s0 in
      lemma_purge_empty_code body (fuel - 1) s0;
      match s_opt with
      | None -> ()
      | Some s1 ->
        if s1.ms_ok then lemma_purge_empty_while c (fuel - 1) s1
        else ()
  )
#pop-options
