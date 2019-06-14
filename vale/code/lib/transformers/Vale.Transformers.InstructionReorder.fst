(**

   This module defines a transformer that performs safe instruction
   reordering.

   Example:

     The following set of instructions can be reordered in any order
     without any observable change in behavior:

       mov rax, 10
       mov rbx, 3

   Usage:

     Given two [codes], [reordering_allowed] tells you whether this
     transformer considers them to be safe permutations of each-other.
     If so, then by using [lemma_reordering], the transformer shows
     that both behave identically (i.e., starting from equivalent
     states, execution of the two [codes] objects should lead to
     equivalent final states).

     If the reordering is not allowed, then this transformer gives a
     (human-readable) reason for why it believes that the reordering
     is not possible.

*)
module Vale.Transformers.InstructionReorder

/// Open all the relevant modules from the x64 semantics.

open Vale.X64.Bytes_Code_s
open Vale.X64.Instruction_s
open Vale.X64.Instructions_s
open Vale.X64.Machine_Semantics_s
open Vale.X64.Machine_s
open Vale.X64.Print_s

/// Relevant modules from Transformers

open Vale.Transformers.PossiblyMonad
open Vale.Transformers.Locations
open Vale.Transformers.BoundedInstructionEffects

/// Finally some convenience module renamings

module L = FStar.List.Tot

/// Given two read/write sets corresponding to two neighboring
/// instructions, we can say whether exchanging those two instructions
/// should be allowed.

let rw_exchange_allowed (rw1 rw2 : rw_set) : pbool =
  let (r1, w1), (r2, w2) = rw1, rw2 in
  (disjoint_locations r1 w2 /+< "read set of 1st not disjoint from write set of 2nd because ") &&.
  (disjoint_locations r2 w1 /+< "read set of 2nd not disjoint from write set of 1st because ") &&.
  (disjoint_locations w1 w2 /+< "write sets not disjoint because ")

let ins_exchange_allowed (i1 i2 : ins) : pbool =
  (
    match i1, i2 with
    | Instr _ _ _, Instr _ _ _ ->
      (rw_exchange_allowed (rw_set_of_ins i1) (rw_set_of_ins i2))
    | _, _ ->
      ffalse "non-generic instructions: conservatively disallowed exchange"
  ) /+> normal (" for instructions " ^ print_ins i1 gcc ^ " and " ^ print_ins i2 gcc)

let lemma_ins_exchange_allowed_symmetric (i1 i2 : ins) :
  Lemma
    (requires (
        !!(ins_exchange_allowed i1 i2)))
    (ensures (
        !!(ins_exchange_allowed i2 i1))) =
  let b1 = !!(ins_exchange_allowed i1 i2) in
  let b2 = !!(ins_exchange_allowed i2 i1) in
  assert (b1 == !!(rw_exchange_allowed (rw_set_of_ins i1) (rw_set_of_ins i2)));
  assert (b2 == !!(rw_exchange_allowed (rw_set_of_ins i2) (rw_set_of_ins i1)));
  let r1, w1 = rw_set_of_ins i1 in
  let r2, w2 = rw_set_of_ins i2 in
  let disjoint = disjoint_locations in
  let aux l1 l2 : (b:bool) = !!(disjoint l1 l2) in
  assert (b1 == (aux r1 w2 && aux r2 w1 && aux w1 w2));
  assert (b2 == (aux r2 w1 && aux r1 w2 && aux w2 w1));
  lemma_disjoint_locations_symmetric w1 w2;
  assert (aux w1 w2 = aux w2 w1)

/// First, we must define what it means for two states to be
/// equivalent. Here, we basically say they must be exactly the same.
///
/// TODO: We should figure out a way to handle flags better. Currently
/// any two instructions that havoc flags cannot be exchanged since
/// they will not lead to equiv states.

let equiv_states (s1 s2 : machine_state) : GTot Type0 =
  (s1.ms_ok == s2.ms_ok) /\
  (s1.ms_regs == s2.ms_regs) /\
  (cf s1.ms_flags = cf s2.ms_flags) /\
  (overflow s1.ms_flags = overflow s2.ms_flags) /\
  (s1.ms_heap == s2.ms_heap) /\
  (s1.ms_memTaint == s2.ms_memTaint) /\
  (s1.ms_stack == s2.ms_stack) /\
  (s1.ms_stackTaint == s2.ms_stackTaint)

(** Same as [equiv_states] but uses extensionality to "think harder";
    useful at lower-level details of the proof. *)
let equiv_states_ext (s1 s2 : machine_state) : GTot Type0 =
  let open FStar.FunctionalExtensionality in
  (feq s1.ms_regs s2.ms_regs) /\
  (Map.equal s1.ms_heap s2.ms_heap) /\
  (Map.equal s1.ms_memTaint s2.ms_memTaint) /\
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

let lemma_unchanged_at_combine (a1 a2:list location) (sa1 sa2 sb1 sb2:machine_state) :
  Lemma
    (requires (
        !!(disjoint_locations a1 a2) /\
        (unchanged_at a1 sa1 sb2) /\
        (unchanged_except a2 sa1 sb1) /\
        (unchanged_at a2 sa2 sb1) /\
        (unchanged_except a1 sa2 sb2)))
    (ensures (
        (unchanged_at (a1 `L.append` a2) sb1 sb2))) =
  let precond = !!(disjoint_locations a1 a2) /\
                 (unchanged_at a1 sa1 sb2) /\
                 (unchanged_except a2 sa1 sb1) /\
                 (unchanged_at a2 sa2 sb1) /\
                 (unchanged_except a1 sa2 sb2) in
  let aux1 a :
    Lemma
      (requires (L.mem a a1 /\ precond))
      (ensures (eval_location a sb1 == eval_location a sb2)) =
    lemma_disjoint_location_from_locations_mem a1 a2 a;
    assert (!!(disjoint_location_from_locations a a2));
    assert (eval_location a sb1 == eval_location a sa1);
    lemma_unchanged_at_mem a1 a sa1 sb2
  in
  let aux2 a :
    Lemma
      (requires (L.mem a a2 /\ precond))
      (ensures (eval_location a sb1 == eval_location a sb2)) =
    lemma_disjoint_locations_symmetric a1 a2;
    lemma_disjoint_location_from_locations_mem a2 a1 a;
    assert (!!(disjoint_location_from_locations a a1));
    assert (eval_location a sb2 == eval_location a sa2);
    lemma_unchanged_at_mem a2 a sa2 sb1
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

let lemma_bounded_effects_means_same_ok (r w:locations) (f:st unit) (s1 s2 s1' s2':machine_state) :
  Lemma
    (requires (
        (bounded_effects r w f) /\
        (s1.ms_ok = s2.ms_ok) /\
        (unchanged_at r s1 s2) /\
        (s1' == run f s1) /\
        (s2' == run f s2)))
    (ensures (
        ((run f s1).ms_ok = (run f s2).ms_ok))) = ()

let lemma_both_not_ok (f1 f2:st unit) (r1 w1 r2 w2:locations) (s:machine_state) :
  Lemma
    (requires (
        (bounded_effects r1 w1 f1) /\
        (bounded_effects r2 w2 f2) /\
        !!(rw_exchange_allowed (r1, w1) (r2, w2))))
    (ensures (
        (run2 f1 f2 s).ms_ok =
        (run2 f2 f1 s).ms_ok)) =
  lemma_disjoint_implies_unchanged_at r1 w2 s (run f2 s);
  lemma_disjoint_implies_unchanged_at r2 w1 s (run f1 s)

let lemma_commute (f1 f2:st unit) (r1 w1 r2 w2:list location) (s:machine_state) :
  Lemma
    (requires (
        (bounded_effects r1 w1 f1) /\
        (bounded_effects r2 w2 f2) /\
        !!(rw_exchange_allowed (r1, w1) (r2, w2))))
    (ensures (
        equiv_states_or_both_not_ok
          (run2 f1 f2 s)
          (run2 f2 f1 s))) =
  let s12 = run2 f1 f2 s in
  let s21 = run2 f2 f1 s in
  if not s12.ms_ok || not s21.ms_ok then (
    lemma_both_not_ok f1 f2 r1 w1 r2 w2 s
  ) else (
    let is1 = run f1 s in
    let is2 = run f2 s in
    let is12 = run f2 is1 in
    let is21 = run f1 is2 in
    lemma_disjoint_implies_unchanged_at r1 w2 s is2;
    lemma_disjoint_implies_unchanged_at r2 w1 s is1;
    assert (unchanged_at w1 is1 is21);
    assert (unchanged_at w2 is2 is12);
    assert (unchanged_except w2 s is2);
    assert (unchanged_except w1 s is1);
    assert (unchanged_except w2 is1 is12);
    assert (unchanged_except w1 is2 is21);
    lemma_unchanged_except_transitive w1 w2 s is1 is12;
    assert (unchanged_except (w1 `L.append` w2) s is12);
    lemma_unchanged_except_transitive w2 w1 s is2 is21;
    assert (unchanged_except (w2 `L.append` w1) s is21);
    lemma_unchanged_except_append_symmetric w1 w2 s is12;
    lemma_unchanged_except_append_symmetric w2 w1 s is21;
    lemma_unchanged_except_same_transitive (w1 `L.append` w2) s is12 is21;
    lemma_unchanged_at_combine w1 w2 is1 is2 is12 is21;
    lemma_unchanged_at_and_except (w1 `L.append` w2) is12 is21;
    assert (unchanged_except [] is12 is21);
    assert (s21.ms_ok = s12.ms_ok);
    lemma_equiv_states_when_except_none is12 is21 s12.ms_ok;
    assert (equiv_states (run2 f1 f2 s) (run2 f2 f1 s))
  )

let lemma_machine_eval_ins_st_exchange (i1 i2 : ins) (s : machine_state) :
  Lemma
    (requires (!!(ins_exchange_allowed i1 i2)))
    (ensures (commutes s
                (machine_eval_ins_st i1)
                (machine_eval_ins_st i2))) =
  lemma_machine_eval_ins_st_bounded_effects i1;
  lemma_machine_eval_ins_st_bounded_effects i2;
  let r1, w1 = rw_set_of_ins i1 in
  let r2, w2 = rw_set_of_ins i2 in
  lemma_commute (machine_eval_ins_st i1) (machine_eval_ins_st i2) r1 w1 r2 w2 s

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

/// Given that we can perform simple swaps between instructions, we
/// can do swaps between [code]s.

let code_exchange_allowed (c1 c2:code) : pbool =
  match c1, c2 with
  | Ins i1, Ins i2 -> ins_exchange_allowed i1 i2
  | _ -> ffalse "non instruction swaps conservatively disallowed"

#push-options "--initial_fuel 3 --max_fuel 3 --max_ifuel 0"
let lemma_code_exchange (c1 c2 : code) (fuel:nat) (s1 s2 : machine_state) :
  Lemma
    (requires (
        !!(code_exchange_allowed c1 c2) /\
        (equiv_states s1 s2) /\
        (Some? (machine_eval_codes [c1; c2] fuel s1))))
    (ensures (
        (Some? (machine_eval_codes [c2; c1] fuel s2)) /\
        (let Some s1', Some s2' =
           machine_eval_codes [c1; c2] fuel s1,
           machine_eval_codes [c2; c1] fuel s2 in
         equiv_states_or_both_not_ok s1' s2'))) =
  let Some s1', Some s2' =
    machine_eval_codes [c1; c2] fuel s1,
    machine_eval_codes [c2; c1] fuel s2 in
  match c1, c2 with
  | Ins i1, Ins i2 ->
    let Some s10 = machine_eval_code c1 fuel s1 in
    let Some s11 = machine_eval_code c1 fuel (filt_state s1) in
    // assert_norm (equiv_states s10 s11);
    // assert_norm (equiv_states (machine_eval_ins i1 (filt_state s1)) s11);
    let Some s12 = machine_eval_code c2 fuel (machine_eval_ins i1 (filt_state s1)) in
    // assert_norm (equiv_states s1' s12);
    let Some s13 = machine_eval_code c2 fuel (filt_state (machine_eval_ins i1 (filt_state s1))) in
    // assert_norm (equiv_states s12 s13);
    let s14 = machine_eval_ins i2 (filt_state (machine_eval_ins i1 (filt_state s1))) in
    // assert_norm (equiv_states s13 s14);
    assert (equiv_states s1' s14);
    let Some s20 = machine_eval_code c2 fuel s2 in
    let Some s21 = machine_eval_code c2 fuel (filt_state s2) in
    // assert_norm (equiv_states s20 s21);
    // assert_norm (equiv_states (machine_eval_ins i2 (filt_state s2)) s21);
    let Some s22 = machine_eval_code c1 fuel (machine_eval_ins i2 (filt_state s2)) in
    // assert_norm (equiv_states s2' s22);
    let Some s23 = machine_eval_code c1 fuel (filt_state (machine_eval_ins i2 (filt_state s2))) in
    // assert_norm (equiv_states s22 s23);
    let s24 = machine_eval_ins i1 (filt_state (machine_eval_ins i2 (filt_state s2))) in
    // assert_norm (equiv_states s23 s24);
    assert (equiv_states s2' s24);
    lemma_instruction_exchange i1 i2 s1 s2;
    assert (equiv_states_or_both_not_ok s14 s24);
    assert (equiv_states_or_both_not_ok s1' s2')
  | _ -> ()
#pop-options

/// Given that we can perform simple swaps between [code]s, we can
/// define a relation that tells us if some [codes] can be transformed
/// into another using only allowed swaps.

(* WARNING: We assume this function since it is not yet exposed. Once
   exposed, we should be able to remove it from here *)
assume val eq_code (c1 c2:code) : (b:bool{
    b ==> (machine_eval_code c1 == machine_eval_code c2)})

let lemma_eq_code_exchange_allowed (c1 c1' c2:code) :
  Lemma
    (requires (
        !!(code_exchange_allowed c1 c2) /\
        (eq_code c1' c1)))
    (ensures (!!(code_exchange_allowed c1' c2))) =
  admit ()

let rec find_code (c1:code) (cs2:codes) : possibly (i:nat{i < L.length cs2 /\ eq_code c1 (L.index cs2 i)}) =
  match cs2 with
  | [] -> Err ("Not found: " ^ fst (print_code c1 0 gcc))
  | h2 :: t2 ->
    if eq_code c1 h2 then (
      return 0
    ) else (
      match find_code c1 t2 with
      | Err reason -> Err reason
      | Ok i ->
        return (i+1)
    )

let rec bubble_to_top (cs:codes) (i:nat{i < L.length cs}) : possibly (cs':codes{
    let a, b, c = L.split3 cs i in
    cs' == L.append a c
  }) =
  match cs with
  | [_] -> return []
  | h :: t ->
    let x = L.index cs i in
    if i = 0 then (
      return t
    ) else (
      match bubble_to_top t (i - 1) with
      | Err reason -> Err reason
      | Ok res ->
        match code_exchange_allowed x h with
        | Err reason -> Err reason
        | Ok () ->
          return (h :: res)
    )

let rec reordering_allowed (c1 c2 : codes) : pbool =
  match c1, c2 with
  | [], [] -> ttrue
  | [], _ | _, [] -> ffalse "disagreeing lengths of codes"
  | h1 :: t1, _ ->
    i <-- find_code h1 c2;
    t2 <-- bubble_to_top c2 i;
    (* TODO: Also check _inside_ blocks/ifelse/etc rather than just at the highest level *)
    reordering_allowed t1 t2

/// Not-ok states lead to erroring states upon execution

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

/// If there are two sequences of instructions that can be transformed
/// amongst each other, then they behave identically as per the
/// [equiv_states] relation.

#push-options "--initial_fuel 3 --max_fuel 3"
let rec lemma_bubble_to_top (cs : codes) (i:nat{i < L.length cs}) (fuel:nat) (s : machine_state)
    (x : _{eq_code x (L.index cs i)}) (xs : _{Ok xs == bubble_to_top cs i})
    (s_0 : _{Some s_0 == machine_eval_code x fuel s})
    (s_1 : _{Some s_1 == machine_eval_codes xs fuel s_0}) :
  Lemma
    (requires (s_1.ms_ok))
    (ensures (
        let s_final' = machine_eval_codes cs fuel s in
        equiv_option_states (Some s_1) s_final')) =
  let s_final' = machine_eval_codes cs fuel s in
  match i with
  | 0 -> ()
  | _ ->
    lemma_eq_code_exchange_allowed (L.index cs i) x (L.hd cs);
    assert !!(code_exchange_allowed x (L.hd cs));
    lemma_code_exchange x (L.hd cs) fuel s s;
    let Ok tlxs = bubble_to_top (L.tl cs) (i - 1) in
    assert (L.tl xs == tlxs);
    assert (L.hd xs == L.hd cs);
    let Some s_start = machine_eval_code (L.hd cs) fuel s in
    let Some s_0' = machine_eval_code x fuel s_start in
    let Some s_0'' = machine_eval_code (L.hd cs) fuel s_0 in
    assert (equiv_states_or_both_not_ok s_0' s_0'');
    if not s_0'.ms_ok && not s_0''.ms_ok then (
      lemma_not_ok_propagate_codes tlxs fuel s_0';
      lemma_not_ok_propagate_codes tlxs fuel s_0''
    ) else (
      lemma_eval_codes_equiv_states tlxs fuel s_0' s_0'';
      let Some s_1' = machine_eval_codes tlxs fuel s_0' in
      lemma_bubble_to_top (L.tl cs) (i - 1) fuel s_start x tlxs s_0' s_1'
    )
#pop-options

let rec lemma_reordering (c1 c2 : codes) (fuel:nat) (s1 s2 : machine_state) :
  Lemma
    (requires (
        !!(reordering_allowed c1 c2) /\
        (equiv_states s1 s2) /\
        (Some? (machine_eval_codes c1 fuel s1)) /\
        (Some?.v (machine_eval_codes c1 fuel s1)).ms_ok))
    (ensures (
        (Some? (machine_eval_codes c2 fuel s2)) /\
        (let Some s1', Some s2' =
           machine_eval_codes c1 fuel s1,
           machine_eval_codes c2 fuel s2 in
         equiv_states_or_both_not_ok s1' s2'))) =
  match c1 with
  | [] -> ()
  | h1 :: t1 ->
    let Ok i = find_code h1 c2 in
    let Ok t2 = bubble_to_top c2 i in
    lemma_eval_code_equiv_states h1 fuel s1 s2;
    lemma_reordering t1 t2 fuel (Some?.v (machine_eval_code h1 fuel s1)) (Some?.v (machine_eval_code h1 fuel s2));
    let Some s_0 = machine_eval_code h1 fuel s2 in
    let Some s_1 = machine_eval_codes t2 fuel s_0 in
    lemma_bubble_to_top c2 i fuel s2 h1 t2 s_0 s_1
