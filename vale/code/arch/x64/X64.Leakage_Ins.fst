module X64.Leakage_Ins
open X64.Machine_s
open X64.Instruction_s
module BC = X64.Bytes_Code_s
module S = X64.Bytes_Semantics_s
open X64.Taint_Semantics_s
open X64.Leakage_s
open X64.Leakage_Helpers
open X64.Bytes_Semantics

let rec has_mem_operand = function
  | [] -> false
  | a::q -> if OMem? a || OStack? a then true else has_mem_operand q

let rec check_if_consumes_fixed_time_args
    (args:list instr_operand) (oprs:instr_operands_t_args args) (ts:taintState)
  : Pure bool
    (requires True)
    (ensures fun b -> b ==> (forall (s1 s2:traceState).{:pattern (constTimeInvariant ts s1 s2)}
      constTimeInvariant ts s1 s2 ==> obs_args args oprs s1 == obs_args args oprs s2))
  =
  match args with
  | [] -> true
  | (IOpEx i)::args ->
    let ((o:instr_operand_t i), (oprs:instr_operands_t_args args)) = coerce oprs in
    let b' =
      match i with
      | IOp64 ->
        let o = match coerce o with | OMem _ | OStack _ -> o | _ -> o in // REVIEW: this avoids extra ifuel, but it leads to a lot of duplicate code
        operand_does_not_use_secrets o ts
      | IOpXmm ->
        let o = match coerce o with | Mov128Mem _ | Mov128Stack _ | _ -> o in
        operand128_does_not_use_secrets o ts
      in
    let b'' = check_if_consumes_fixed_time_args args oprs ts in
    b' && b''
  | (IOpIm i)::args ->
    let b' =
      match i with
      | IOp64One o ->
        let o = match coerce o with | OMem _ | OStack _ -> o | _ -> o in
        operand_does_not_use_secrets o ts
      | IOpXmmOne o ->
        let o = match coerce o with | Mov128Mem _ | Mov128Stack _ | _ -> o in
        operand128_does_not_use_secrets o ts
      | IOpFlagsCf -> true
      | IOpFlagsOf -> true
      in
    let b'' = check_if_consumes_fixed_time_args args (coerce oprs) ts in
    b' && b''

let rec check_if_consumes_fixed_time_outs
    (outs:list instr_out) (args:list instr_operand) (oprs:instr_operands_t outs args)
    (ts:taintState) (t_ins t_out:taint)
  : Pure bool
    (requires True)
    (ensures fun b -> b ==> (forall (s1 s2:traceState).{:pattern (constTimeInvariant ts s1 s2)}
      constTimeInvariant ts s1 s2 ==> obs_inouts outs args oprs s1 == obs_inouts outs args oprs s2))
  =
  match outs with
  | [] -> check_if_consumes_fixed_time_args args oprs ts
  | (_, IOpEx i)::outs ->
    let ((o:instr_operand_t i), (oprs:instr_operands_t outs args)) = coerce oprs in
    let b' =
      match i with
      | IOp64 ->
        let o = match coerce o with | OMem _ | OStack _ -> o | _ -> o in
        operand_does_not_use_secrets o ts && operand_taint_allowed o t_ins t_out
      | IOpXmm ->
        let o = match coerce o with | Mov128Mem _ | Mov128Stack _ | _ -> o in
        operand128_does_not_use_secrets o ts && operand128_taint_allowed o t_ins t_out
      in
    let b'' = check_if_consumes_fixed_time_outs outs args oprs ts t_ins t_out in
    b' && b''
  | (_, IOpIm i)::outs ->
    let b' =
      match i with
      | IOp64One o ->
        let o = match coerce o with | OMem _ | OStack _ -> o | _ -> o in
        operand_does_not_use_secrets o ts && operand_taint_allowed o t_ins t_out
      | IOpXmmOne o ->
        let o = match coerce o with | Mov128Mem _ | Mov128Stack _ | _ -> o in
        operand128_does_not_use_secrets o ts && operand128_taint_allowed o t_ins t_out
      | IOpFlagsCf -> true
      | IOpFlagsOf -> true
      in
    let b'' = check_if_consumes_fixed_time_outs outs args (coerce oprs) ts t_ins t_out in
    b' && b''

#reset-options "--z3rlimit 100"
let rec lemma_args_taint
    (outs:list instr_out) (args:list instr_operand)
    (f:instr_args_t outs args) (oprs:instr_operands_t_args args)
    (ts:taintState) (t_ins:taint) (s1 s2:traceState)
  : Lemma
    (requires
      constTimeInvariant ts s1 s2 /\
      taint_match_args args oprs t_ins s1.memTaint s1.stackTaint s1.state /\
      taint_match_args args oprs t_ins s2.memTaint s2.stackTaint s2.state /\
      Some? (S.instr_apply_eval_args outs args f oprs s1.state) /\
      Some? (S.instr_apply_eval_args outs args f oprs s2.state) /\
      check_if_consumes_fixed_time_args args oprs ts /\
      args_taint args oprs ts t_ins == Public)
    (ensures
      S.instr_apply_eval_args outs args f oprs s1.state ==
      S.instr_apply_eval_args outs args f oprs s2.state)
  =
  match args with
  | [] -> ()
  | i::args ->
    let i = (match i with | IOpIm (IOpXmmOne _) | IOpIm (IOp64One _) | _ -> i) in // REVIEW: hack to avoid extra ifuel
    let (v1, v2, oprs) : option (instr_val_t i) & option (instr_val_t i) & instr_operands_t_args args =
      match i with
      | IOpEx i ->
        let oprs = coerce oprs in (
          S.instr_eval_operand_explicit i (fst oprs) s1.state,
          S.instr_eval_operand_explicit i (fst oprs) s2.state,
          snd oprs)
      | IOpIm i ->
        let oprs = coerce oprs in (
          S.instr_eval_operand_implicit i s1.state,
          S.instr_eval_operand_implicit i s2.state,
          oprs)
      in
    let f:arrow (instr_val_t i) (instr_args_t outs args) = coerce f in
    Opaque_s.reveal_opaque S.get_heap_val32_def;
    Opaque_s.reveal_opaque S.get_heap_val64_def;
    Opaque_s.reveal_opaque S.get_heap_val128_def;
    assert (v1 == v2);
    let Some v = v1 in
    lemma_args_taint outs args (f v) oprs ts t_ins s1 s2

let rec lemma_inouts_taint
    (outs inouts:list instr_out) (args:list instr_operand)
    (f:instr_inouts_t outs inouts args) (oprs:instr_operands_t inouts args)
    (ts:taintState) (t_ins:taint) (s1 s2:traceState)
  : Lemma
    (requires
      constTimeInvariant ts s1 s2 /\
      taint_match_inouts inouts args oprs t_ins s1.memTaint s1.stackTaint s1.state /\
      taint_match_inouts inouts args oprs t_ins s2.memTaint s2.stackTaint s2.state /\
      Some? (S.instr_apply_eval_inouts outs inouts args f oprs s1.state) /\
      Some? (S.instr_apply_eval_inouts outs inouts args f oprs s2.state) /\
      check_if_consumes_fixed_time_outs inouts args oprs ts t_ins Public /\
      inouts_taint inouts args oprs ts t_ins == Public)
    (ensures
      S.instr_apply_eval_inouts outs inouts args f oprs s1.state ==
      S.instr_apply_eval_inouts outs inouts args f oprs s2.state)
  =
  match inouts with
  | [] -> lemma_args_taint outs args f oprs ts t_ins s1 s2
  | (Out, i)::inouts ->
    let oprs =
      match i with
      | IOpEx i -> snd #(instr_operand_t i) (coerce oprs)
      | IOpIm i -> coerce oprs
      in
    lemma_inouts_taint outs inouts args (coerce f) oprs ts t_ins s1 s2
  | (InOut, i)::inouts ->
    let i = (match i with | IOpIm (IOpXmmOne _) | IOpIm (IOp64One _) | _ -> i) in // REVIEW: hack to avoid extra ifuel
    let (v1, v2, oprs) : option (instr_val_t i) & option (instr_val_t i) & instr_operands_t inouts args =
      match i with
      | IOpEx i ->
        let oprs = coerce oprs in (
          S.instr_eval_operand_explicit i (fst oprs) s1.state,
          S.instr_eval_operand_explicit i (fst oprs) s2.state,
          snd oprs)
      | IOpIm i ->
        let oprs = coerce oprs in (
          S.instr_eval_operand_implicit i s1.state,
          S.instr_eval_operand_implicit i s2.state,
          oprs)
      in
    let f:arrow (instr_val_t i) (instr_inouts_t outs inouts args) = coerce f in
    Opaque_s.reveal_opaque S.get_heap_val32_def;
    Opaque_s.reveal_opaque S.get_heap_val64_def;
    Opaque_s.reveal_opaque S.get_heap_val128_def;
    assert (v1 == v2);
    let Some v = v1 in
    lemma_inouts_taint outs inouts args (f v) oprs ts t_ins s1 s2

let instr_set_taint_explicit
    (i:instr_operand_explicit) (o:instr_operand_t i) (ts:taintState) (t:taint)
  : taintState =
  match i with
  | IOp64 -> set_taint o ts t
  | IOpXmm -> set_taint128 o ts t

[@instr_attr]
let instr_set_taint_implicit (i:instr_operand_implicit) (ts:taintState) (t:taint) : taintState =
  match i with
  | IOp64One o -> set_taint o ts t
  | IOpXmmOne o -> set_taint128 o ts t
  | IOpFlagsCf -> set_taint_cf_and_flags ts t
  | IOpFlagsOf -> set_taint_of_and_flags ts t

let rec instr_set_taints
    (outs:list instr_out) (args:list instr_operand)
    (oprs:instr_operands_t outs args) (ts:taintState) (t:taint)
  : taintState =
  match outs with
  | [] -> ts
  | (_, i)::outs ->
    (
      match i with
      | IOpEx i ->
        let oprs:instr_operand_t i & instr_operands_t outs args = coerce oprs in
        instr_set_taints outs args (snd oprs) (instr_set_taint_explicit i (fst oprs) ts t) t
      | IOpIm i -> instr_set_taints outs args (coerce oprs) (instr_set_taint_implicit i ts t) t
    )

let rec lemma_instr_write_outputs_ok
    (outs:list instr_out) (args:list instr_operand)
    (vs:instr_ret_t outs) (oprs:instr_operands_t outs args) (s_orig s:S.state)
  : Lemma
    (requires (S.instr_write_outputs outs args vs oprs s_orig s).S.ok)
    (ensures s.S.ok)
  =
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
          let oprs:instr_operand_t i & instr_operands_t outs args = coerce oprs in
          let s' = S.instr_write_output_explicit i v (fst oprs) s_orig s in
          lemma_instr_write_outputs_ok outs args vs (snd oprs) s_orig s'
      | IOpIm i ->
          let s' = S.instr_write_output_implicit i v s_orig s in
          lemma_instr_write_outputs_ok outs args vs (coerce oprs) s_orig s'
    )

[@"opaque_to_smt"]
let update_heap32_val (ptr:int) (v:Types_s.nat32) (i:int) : Types_s.nat8 =
  let open Words_s in
  let open Words.Four_s in
  let v = nat_to_four 8 v in
  match (i - ptr) with
  | 0 -> v.lo0
  | 1 -> v.lo1
  | 2 -> v.hi2
  | 3 -> v.hi3
  | _ -> 0

let valid_addr32 (ptr:int) (mem:S.heap) : bool =
  S.valid_addr (ptr + 0) mem &&
  S.valid_addr (ptr + 1) mem &&
  S.valid_addr (ptr + 2) mem &&
  S.valid_addr (ptr + 3) mem

let lemma_update_heap32_val (ptr:int) (v:Types_s.nat32) (mem:S.heap) (i:int) : Lemma
  (requires True)
  (ensures (S.update_heap32 ptr v mem).[i] ==
    (if ptr <= i && i < ptr + 4 then update_heap32_val ptr v i else mem.[i]))
  [SMTPat ((S.update_heap32 ptr v mem).[i])]
  =
  Opaque_s.reveal_opaque S.update_heap32_def;
  FStar.Pervasives.reveal_opaque (`%update_heap32_val) update_heap32_val

let lemma_update_heap32_domain (ptr:int) (v:Types_s.nat32) (mem:S.heap) : Lemma
  (requires valid_addr32 ptr mem)
  (ensures Map.domain (S.update_heap32 ptr v mem) == Map.domain mem)
  [SMTPat (S.update_heap32 ptr v mem)]
  =
  Opaque_s.reveal_opaque S.update_heap32_def;
  assert (Set.equal (Map.domain (S.update_heap32 ptr v mem)) (Map.domain mem))

[@"opaque_to_smt"]
let update_heap64_val (ptr:int) (v:nat64) (i:int) : Types_s.nat8 =
  let open Words_s in
  let open Words.Two_s in
  let open Words.Four_s in
  let v = nat_to_two 32 v in
  let lo = nat_to_four 8 v.lo in
  let hi = nat_to_four 8 v.hi in
  match (i - ptr) with
  | 0 -> lo.lo0
  | 1 -> lo.lo1
  | 2 -> lo.hi2
  | 3 -> lo.hi3
  | 4 -> hi.lo0
  | 5 -> hi.lo1
  | 6 -> hi.hi2
  | 7 -> hi.hi3
  | _ -> 0

// TODO: this and lemma_update_heap32_val are convenient,
// but they make lemma_instr_set_taints_* slow to verify.
// Consider writing lemma_instr_set_taints_* in a more manual style.
let lemma_update_heap64_val (ptr:int) (v:nat64) (mem:S.heap) (i:int) : Lemma
  (requires True)
  (ensures (S.update_heap64 ptr v mem).[i] ==
    (if ptr <= i && i < ptr + 8 then update_heap64_val ptr v i else mem.[i]))
  [SMTPat ((S.update_heap64 ptr v mem).[i])]
  =
  Opaque_s.reveal_opaque S.update_heap64_def;
  FStar.Pervasives.reveal_opaque (`%update_heap64_val) update_heap64_val

let lemma_update_heap64_domain (ptr:int) (v:nat64) (mem:S.heap) : Lemma
  (requires S.valid_addr64 ptr mem)
  (ensures Map.domain (S.update_heap64 ptr v mem) == Map.domain mem)
  [SMTPat (S.update_heap64 ptr v mem)]
  =
  Opaque_s.reveal_opaque S.update_heap64_def;
  assert (Set.equal (Map.domain (S.update_heap64 ptr v mem)) (Map.domain mem))

#reset-options "--z3rlimit 500"
let rec lemma_instr_set_taints_secret
    (outs:list instr_out) (args:list instr_operand)
    (vs1 vs2:instr_ret_t outs) (oprs:instr_operands_t outs args) (ts_orig ts:taintState) (t_ins t_out:taint)
    (s1_orig s1 s2_orig s2:traceState)
  : Lemma
    (requires (
      let s1_state' = S.instr_write_outputs outs args vs1 oprs s1_orig.state s1.state in
      let s2_state' = S.instr_write_outputs outs args vs2 oprs s2_orig.state s2.state in
      s1_state'.S.ok /\ s2_state'.S.ok /\
      t_out == Secret /\
      Set.equal (Map.domain s1_orig.state.S.mem) (Map.domain s1.state.S.mem) /\
      Set.equal (Map.domain s2_orig.state.S.mem) (Map.domain s2.state.S.mem) /\
      check_if_consumes_fixed_time_outs outs args oprs ts_orig t_ins t_out /\
      publicValuesAreSame ts_orig s1_orig s2_orig /\
      publicValuesAreSame ts s1 s2
    ))
    (ensures (
      let memTaint1, stackTaint1 = update_taint_outputs outs args oprs t_ins s1.memTaint s1.stackTaint s1_orig.state in
      let s1' = {
        state = S.instr_write_outputs outs args vs1 oprs s1_orig.state s1.state;
        trace = s1.trace;
        memTaint = memTaint1;
        stackTaint = stackTaint1;
      } in
      let memTaint2, stackTaint2 = update_taint_outputs outs args oprs t_ins s2.memTaint s2.stackTaint s2_orig.state in
      let s2' = {
        state = S.instr_write_outputs outs args vs2 oprs s2_orig.state s2.state;
        trace = s2.trace;
        memTaint = memTaint2;
        stackTaint = stackTaint2;
      } in
      let ts' = instr_set_taints outs args oprs ts t_out in
      publicValuesAreSame ts' s1' s2'
    ))
  =
  match outs with
  | [] -> ()
  | (_, i)::outs ->
    (
      let ((v1:instr_val_t i), (vs1:instr_ret_t outs)) =
        match outs with
        | [] -> (vs1, ())
        | _::_ -> let vs1 = coerce vs1 in (fst vs1, snd vs1)
        in
      let ((v2:instr_val_t i), (vs2:instr_ret_t outs)) =
        match outs with
        | [] -> (vs2, ())
        | _::_ -> let vs2 = coerce vs2 in (fst vs2, snd vs2)
        in
      match i with
      | IOpEx i ->
        let (o, oprs):instr_operand_t i & instr_operands_t outs args = coerce oprs in
        let o =
          match i with
          | IOp64 -> (match coerce o with OMem _ | OStack _ | _ -> o)
          | IOpXmm -> (match coerce o with Mov128Mem _ | Mov128Stack _ | _ -> o)
          in
        let memTaint1, stackTaint1 = update_taint_operand_explicit i o t_ins s1.memTaint s1.stackTaint s1_orig.state in
        let s1' = {
          state = S.instr_write_output_explicit i v1 o s1_orig.state s1.state;
          trace = s1.trace;
          memTaint = memTaint1;
          stackTaint = stackTaint1;
        } in
        let memTaint2, stackTaint2 = update_taint_operand_explicit i o t_ins s2.memTaint s2.stackTaint s2_orig.state in
        let s2' = {
          state = S.instr_write_output_explicit i v2 o s2_orig.state s2.state;
          trace = s2.trace;
          memTaint = memTaint2;
          stackTaint = stackTaint2;
        } in
        lemma_instr_write_outputs_ok outs args vs1 oprs s1_orig.state s1'.state;
        lemma_instr_write_outputs_ok outs args vs2 oprs s2_orig.state s2'.state;
        let ts' = instr_set_taint_explicit i o ts t_out in
        lemma_instr_set_taints_secret outs args vs1 vs2 oprs ts_orig ts' t_ins t_out s1_orig s1' s2_orig s2'
      | IOpIm i ->
        let i = match i with IOp64One (OMem _) | IOpXmmOne (Mov128Mem _) | IOp64One (OStack _) | IOpXmmOne (Mov128Stack _) | _ -> i in
        let memTaint1, stackTaint1 = update_taint_operand_implicit i t_ins s1.memTaint s1.stackTaint s1_orig.state in
        let s1' = {
          state = S.instr_write_output_implicit i v1 s1_orig.state s1.state;
          trace = s1.trace;
          memTaint = memTaint1;
          stackTaint = stackTaint1;
        } in
        let memTaint2, stackTaint2 = update_taint_operand_implicit i t_ins s2.memTaint s2.stackTaint s2_orig.state in
        let s2' = {
          state = S.instr_write_output_implicit i v2 s2_orig.state s2.state;
          trace = s2.trace;
          memTaint = memTaint2;
          stackTaint = stackTaint2;
        } in
        lemma_instr_write_outputs_ok outs args vs1 (coerce oprs) s1_orig.state s1'.state;
        lemma_instr_write_outputs_ok outs args vs2 (coerce oprs) s2_orig.state s2'.state;
        let ts' = instr_set_taint_implicit i ts t_out in
        lemma_instr_set_taints_secret outs args vs1 vs2 (coerce oprs) ts_orig ts' t_ins t_out s1_orig s1' s2_orig s2'
    )

#reset-options "--z3rlimit 500"

let rec lemma_instr_set_taints_public
    (outs:list instr_out) (args:list instr_operand)
    (vs:instr_ret_t outs) (oprs:instr_operands_t outs args) (ts_orig ts:taintState) (t_ins t_out:taint)
    (s1_orig s1 s2_orig s2:traceState)
  : Lemma
    (requires (
      let s1_state' = S.instr_write_outputs outs args vs oprs s1_orig.state s1.state in
      let s2_state' = S.instr_write_outputs outs args vs oprs s2_orig.state s2.state in
      s1_state'.S.ok /\ s2_state'.S.ok /\
      t_out == Public /\ // REVIEW: not actually needed
      Set.equal (Map.domain s1_orig.state.S.mem) (Map.domain s1.state.S.mem) /\
      Set.equal (Map.domain s2_orig.state.S.mem) (Map.domain s2.state.S.mem) /\
      check_if_consumes_fixed_time_outs outs args oprs ts_orig t_ins t_out /\
      publicValuesAreSame ts_orig s1_orig s2_orig /\
      publicValuesAreSame ts s1 s2
    ))
    (ensures (
      let memTaint1, stackTaint1 = update_taint_outputs outs args oprs t_ins s1.memTaint s1.stackTaint s1_orig.state in
      let s1' = {
        state = S.instr_write_outputs outs args vs oprs s1_orig.state s1.state;
        trace = s1.trace;
        memTaint = memTaint1;
        stackTaint = stackTaint1;
      } in
      let memTaint2, stackTaint2 = update_taint_outputs outs args oprs t_ins s2.memTaint s2.stackTaint s2_orig.state in
      let s2' = {
        state = S.instr_write_outputs outs args vs oprs s2_orig.state s2.state;
        trace = s2.trace;
        memTaint = memTaint2;
        stackTaint = stackTaint2;
      } in
      let ts' = instr_set_taints outs args oprs ts t_out in
      publicValuesAreSame ts' s1' s2'
    ))
  =
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
        let (o, oprs):instr_operand_t i & instr_operands_t outs args = coerce oprs in
        let o =
          match i with
          | IOp64 -> (match coerce o with OMem _ | OStack _ | _ -> o)
          | IOpXmm -> (match coerce o with Mov128Mem _ | Mov128Stack _ | _ -> o)
          in
        let memTaint1, stackTaint1 = update_taint_operand_explicit i o t_ins s1.memTaint s1.stackTaint s1_orig.state in
        let s1' = {
          state = S.instr_write_output_explicit i v o s1_orig.state s1.state;
          trace = s1.trace;
          memTaint = memTaint1;
          stackTaint = stackTaint1;
        } in
        let memTaint2, stackTaint2 = update_taint_operand_explicit i o t_ins s2.memTaint s2.stackTaint s2_orig.state in
        let s2' = {
          state = S.instr_write_output_explicit i v o s2_orig.state s2.state;
          trace = s2.trace;
          memTaint = memTaint2;
          stackTaint = stackTaint2;
        } in
        lemma_instr_write_outputs_ok outs args vs oprs s1_orig.state s1'.state;
        lemma_instr_write_outputs_ok outs args vs oprs s2_orig.state s2'.state;
        let ts' = instr_set_taint_explicit i o ts t_out in
        lemma_instr_set_taints_public outs args vs oprs ts_orig ts' t_ins t_out s1_orig s1' s2_orig s2'
      | IOpIm i ->
        let i = match i with IOp64One (OMem _) | IOpXmmOne (Mov128Mem _) | IOp64One (OStack _) | IOpXmmOne (Mov128Stack _) | _ -> i in
        let memTaint1, stackTaint1 = update_taint_operand_implicit i t_ins s1.memTaint s1.stackTaint s1_orig.state in
        let s1' = {
          state = S.instr_write_output_implicit i v s1_orig.state s1.state;
          trace = s1.trace;
          memTaint = memTaint1;
          stackTaint = stackTaint1;
        } in
        let memTaint2, stackTaint2 = update_taint_operand_implicit i t_ins s2.memTaint s2.stackTaint s2_orig.state in
        let s2' = {
          state = S.instr_write_output_implicit i v s2_orig.state s2.state;
          trace = s2.trace;
          memTaint = memTaint2;
          stackTaint = stackTaint2;
        } in
        lemma_instr_write_outputs_ok outs args vs (coerce oprs) s1_orig.state s1'.state;
        lemma_instr_write_outputs_ok outs args vs (coerce oprs) s2_orig.state s2'.state;
        let ts' = instr_set_taint_implicit i ts t_out in
        lemma_instr_set_taints_public outs args vs (coerce oprs) ts_orig ts' t_ins t_out s1_orig s1' s2_orig s2'
    )


let check_if_instr_consumes_fixed_time (ins:tainted_ins) (ts:taintState) : Pure (bool & taintState)
  (requires BC.Instr? ins.i)
  (ensures ins_consumes_fixed_time ins ts)
  =
  let BC.Instr (BC.InstrType outs args havoc_flags iins) oprs _ = ins.i in
  let t = inouts_taint outs args oprs ts ins.t in
  let b = check_if_consumes_fixed_time_outs outs args oprs ts ins.t t in
  let TaintState rs flags cf xmms = ts in
  let flags = match havoc_flags with | HavocFlags -> Secret | PreserveFlags -> flags in
  let cf = match havoc_flags with | HavocFlags -> Secret | PreserveFlags -> cf in
  let ts = TaintState rs flags cf xmms in
  (b, instr_set_taints outs args oprs ts t)

let check_if_alloc_consumes_fixed_time (ins:tainted_ins) (ts:taintState) : Pure (bool & taintState)
  (requires BC.Alloc? ins.i)
  (ensures ins_consumes_fixed_time ins ts)
  = true, ts

let check_if_dealloc_consumes_fixed_time (ins:tainted_ins) (ts:taintState) : Pure (bool & taintState)
  (requires BC.Dealloc? ins.i)
  (ensures ins_consumes_fixed_time ins ts)
  = true, ts
  
#reset-options "--initial_ifuel 2 --max_ifuel 2 --initial_fuel 4 --max_fuel 4 --z3rlimit 80"

let check_if_push_consumes_fixed_time (ins:tainted_ins) (ts:taintState) : Pure (bool & taintState)
  (requires BC.Push? ins.i)
  (ensures ins_consumes_fixed_time ins ts)
  = 
  let BC.Push src = ins.i in
  let t_ins = ins.t in
  let t_out = operand_taint src ts t_ins in
  Public? (ts.regTaint Rsp) && operand_does_not_use_secrets src ts && (t_out = Public || t_ins = Secret), ts

let check_if_pop_consumes_fixed_time (ins:tainted_ins) (ts:taintState) : Pure (bool & taintState)
  (requires BC.Pop? ins.i)
  (ensures ins_consumes_fixed_time ins ts)
  = 
  let BC.Pop dst = ins.i in
  Public? (ts.regTaint Rsp) && operand_does_not_use_secrets dst ts, set_taint dst ts ins.t

let check_if_ins_consumes_fixed_time ins ts =
  match ins.i with
  | BC.Instr _ _ _ -> check_if_instr_consumes_fixed_time ins ts
  | BC.Push _ -> check_if_push_consumes_fixed_time ins ts
  | BC.Pop _ -> check_if_pop_consumes_fixed_time ins ts
  | BC.Alloc _ -> check_if_alloc_consumes_fixed_time ins ts
  | BC.Dealloc _ -> check_if_dealloc_consumes_fixed_time ins ts

#reset-options "--initial_ifuel 1 --max_ifuel 1 --initial_fuel 1 --max_fuel 1 --z3rlimit 100"
let lemma_instr_leakage_free (ts:taintState) (ins:tainted_ins) : Lemma
  (requires BC.Instr? ins.i)
  (ensures (
    let (b, ts') = check_if_instr_consumes_fixed_time ins ts in
    b2t b ==> isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'
  ))
  =
  let (b, ts') = check_if_instr_consumes_fixed_time ins ts in
  if b then
  (
    let code = Ins ins in
    let lem (s1 s2:traceState) (fuel:nat) : Lemma
      (requires is_explicit_leakage_free_lhs code fuel ts ts' s1 s2)
      (ensures is_explicit_leakage_free_rhs code fuel ts ts' s1 s2)
      [SMTPat (is_explicit_leakage_free_rhs code fuel ts ts' s1 s2)]
      =
      let BC.Instr (BC.InstrType outs args havoc_flags i) oprs _ = ins.i in
      let t_ins = ins.t in
      let t_out = inouts_taint outs args oprs ts ins.t in
      let Some vs1 = S.instr_apply_eval outs args (instr_eval i) oprs s1.state in
      let Some vs2 = S.instr_apply_eval outs args (instr_eval i) oprs s2.state in
      let s1' =
        match havoc_flags with
        | HavocFlags -> {s1 with state = {s1.state with S.flags = S.havoc s1.state ins.i}}
        | PreserveFlags -> s1
        in
      let s2' =
        match havoc_flags with
        | HavocFlags -> {s2 with state = {s2.state with S.flags = S.havoc s2.state ins.i}}
        | PreserveFlags -> s2
        in
      let TaintState rs flags cf xmms = ts in
      let flags = match havoc_flags with | HavocFlags -> Secret | PreserveFlags -> flags in
      let cf = match havoc_flags with | HavocFlags -> Secret | PreserveFlags -> cf in
      let ts_havoc = TaintState rs flags cf xmms in

      if t_out = Secret then
      (
        lemma_instr_set_taints_secret outs args vs1 vs2 oprs ts ts_havoc t_ins t_out s1 s1' s2 s2';
        ()
      )
      else
      (
        let vs = vs1 in
        lemma_inouts_taint outs outs args (instr_eval i) oprs ts t_ins s1 s2;
        lemma_instr_set_taints_public outs args vs oprs ts ts_havoc t_ins t_out s1 s1' s2 s2';
        ()
      )
      in
    // assert (isExplicitLeakageFree (Ins ins) ts ts');
    ()
  )

let lemma_dealloc_leakage_free (ts:taintState) (ins:tainted_ins) : Lemma
  (requires BC.Dealloc? ins.i)
  (ensures (
    let (b, ts') = check_if_dealloc_consumes_fixed_time ins ts in
    b2t b ==> isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'
  ))
  =
  let (b, ts') = check_if_dealloc_consumes_fixed_time ins ts in
  if b then
  (
    let code = Ins ins in
    let lem (s1 s2:traceState) (fuel:nat) : Lemma
      (requires is_explicit_leakage_free_lhs code fuel ts ts' s1 s2)
      (ensures is_explicit_leakage_free_rhs code fuel ts ts' s1 s2)
      [SMTPat (is_explicit_leakage_free_rhs code fuel ts ts' s1 s2)]
      =
      let BC.Dealloc n = ins.i in
      let t_ins = ins.t in
      let s1' = Some?.v (taint_eval_code code fuel s1) in
      let s2' = Some?.v (taint_eval_code code fuel s2) in
      let S.Vale_stack _ stack1 = s1.state.S.stack in
      let S.Vale_stack _ stack2 = s2.state.S.stack in
      let S.Vale_stack _ stack1' = s1'.state.S.stack in
      let S.Vale_stack _ stack2' = s2'.state.S.stack in
      let aux (x:int) : Lemma
        (requires publicStackValueIsSame stack1 stack2 s1.stackTaint s2.stackTaint x)
        (ensures publicStackValueIsSame stack1' stack2' s1'.stackTaint s2'.stackTaint x)
        = 
        Classical.forall_intro (fun s -> Vale.Set.lemma_sel_restrict s stack1 x);
        Classical.forall_intro (fun s -> Vale.Set.lemma_sel_restrict s stack2 x)
      in Classical.forall_intro (Classical.move_requires aux)
    in
    ()
  )

let lemma_push_leakage_free (ts:taintState) (ins:tainted_ins) : Lemma
  (requires BC.Push? ins.i)
  (ensures (
    let (b, ts') = check_if_push_consumes_fixed_time ins ts in
    b2t b ==> isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'
  ))
  =
  let (b, ts') = check_if_push_consumes_fixed_time ins ts in
  if b then
  (
    let code = Ins ins in
    let lem (s1 s2:traceState) (fuel:nat) : Lemma
      (requires is_explicit_leakage_free_lhs code fuel ts ts' s1 s2)
      (ensures is_explicit_leakage_free_rhs code fuel ts ts' s1 s2)
      [SMTPat (is_explicit_leakage_free_rhs code fuel ts ts' s1 s2)]
      =
      let BC.Push src = ins.i in
      let t_ins = ins.t in
      let t_out = operand_taint src ts t_ins in
      let s1' = Some?.v (taint_eval_code code fuel s1) in
      let s2' = Some?.v (taint_eval_code code fuel s2) in
      let S.Vale_stack _ stack1 = s1.state.S.stack in
      let S.Vale_stack _ stack2 = s2.state.S.stack in
      let S.Vale_stack _ stack1' = s1'.state.S.stack in
      let S.Vale_stack _ stack2' = s2'.state.S.stack in
      let ptr1 = S.eval_reg Rsp s1.state - 8 in
      let ptr2 = S.eval_reg Rsp s2.state - 8 in
      let v1 = S.eval_operand src s1.state in
      let v2 = S.eval_operand src s2.state in
      assert (ptr1 == ptr2);
      if t_out = Secret then ()
      else (
        let aux () : Lemma  (v1 == v2)
          = match src with
          | OConst _ | OReg _ -> ()
          | OMem _ | OStack _ -> Opaque_s.reveal_opaque S.get_heap_val64_def
        in
        aux()
      )
    in
    ()
  )

let lemma_pop_leakage_free (ts:taintState) (ins:tainted_ins) : Lemma
  (requires BC.Pop? ins.i)
  (ensures (
    let (b, ts') = check_if_pop_consumes_fixed_time ins ts in
    b2t b ==> isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'
  ))
  =
  let (b, ts') = check_if_pop_consumes_fixed_time ins ts in
  if b then
  (
    let code = Ins ins in
    let lem (s1 s2:traceState) (fuel:nat) : Lemma
      (requires is_explicit_leakage_free_lhs code fuel ts ts' s1 s2)
      (ensures is_explicit_leakage_free_rhs code fuel ts ts' s1 s2)
      [SMTPat (is_explicit_leakage_free_rhs code fuel ts ts' s1 s2)]
      =
      let BC.Pop dst = ins.i in
      let t_ins = ins.t in
      let s1' = Some?.v (taint_eval_code code fuel s1) in
      let s2' = Some?.v (taint_eval_code code fuel s2) in
      let stack_op = OStack (MReg Rsp 0) in
      let v1 = S.eval_operand stack_op s1.state in
      let v2 = S.eval_operand stack_op s2.state in
      if ins.t = Secret then (
        match dst with
        | OReg _ -> ()
        | OMem m -> ()
        | OStack _ -> ()
      ) else (
        Opaque_s.reveal_opaque S.get_heap_val64_def;      
        assert (v1 == v2);
        match dst with
        | OReg _ -> ()
        | OMem m -> ()
        | OStack _ -> ()
      );
      Classical.forall_intro_3 (fun s x (stack1:S.heap) -> Vale.Set.lemma_sel_restrict s stack1 x);
      Classical.forall_intro_3 (fun s x (stack2:S.heap) -> Vale.Set.lemma_sel_restrict s stack2 x)      
      in
    ()
  )


let lemma_ins_leakage_free ts ins =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  match ins.i with
  | BC.Instr _ _ _ -> lemma_instr_leakage_free ts ins
  | BC.Alloc _ -> ()
  | BC.Dealloc _ -> lemma_dealloc_leakage_free ts ins
  | BC.Push _ -> lemma_push_leakage_free ts ins
  | BC.Pop _ -> lemma_pop_leakage_free ts ins
