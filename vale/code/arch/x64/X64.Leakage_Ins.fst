module X64.Leakage_Ins
open X64.Machine_s
open X64.Instruction_s
module S = X64.Bytes_Semantics_s
open X64.Taint_Semantics_s
open X64.Leakage_s
open X64.Leakage_Helpers
open X64.Bytes_Semantics

let rec has_mem_operand = function
  | [] -> false
  | a::q -> if OMem? a then true else has_mem_operand q

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
    (outs:list instr_out) (args:list instr_operand) (oprs:instr_operands_t outs args) (ts:taintState)
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
        operand_does_not_use_secrets o ts
      | IOpXmm ->
        let o = match coerce o with | Mov128Mem _ | Mov128Stack _ | _ -> o in
        operand128_does_not_use_secrets o ts
      in
    let b'' = check_if_consumes_fixed_time_outs outs args oprs ts in
    b' && b''
  | (_, IOpIm i)::outs ->
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
    let b'' = check_if_consumes_fixed_time_outs outs args (coerce oprs) ts in
    b' && b''

#reset-options "--z3rlimit 100"
let rec lemma_args_taint
    (outs:list instr_out) (args:list instr_operand)
    (f:instr_args_t outs args) (oprs:instr_operands_t_args args)
    (ts:taintState) (t_ins:taint) (s1 s2:traceState)
  : Lemma
    (requires
      constTimeInvariant ts s1 s2 /\
      taint_match_args args oprs t_ins s1.memTaint s1.state /\
      taint_match_args args oprs t_ins s2.memTaint s2.state /\
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
      taint_match_inouts inouts args oprs t_ins s1.memTaint s1.state /\
      taint_match_inouts inouts args oprs t_ins s2.memTaint s2.state /\
      Some? (S.instr_apply_eval_inouts outs inouts args f oprs s1.state) /\
      Some? (S.instr_apply_eval_inouts outs inouts args f oprs s2.state) /\
      check_if_consumes_fixed_time_outs inouts args oprs ts /\
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

#reset-options "--z3rlimit 200"
let rec lemma_instr_set_taints
    (outs:list instr_out) (args:list instr_operand)
    (vs:instr_ret_t outs) (oprs:instr_operands_t outs args) (ts_orig ts:taintState) (t:taint)
    (s1_orig s1 s2_orig s2:traceState)
  : Lemma
    (requires (
      let s1' = {s1 with state = S.instr_write_outputs outs args vs oprs s1_orig.state s1.state} in
      let s2' = {s1 with state = S.instr_write_outputs outs args vs oprs s2_orig.state s2.state} in
      s1'.state.S.ok /\ s2'.state.S.ok /\
      Set.equal (Map.domain s1_orig.state.S.mem) (Map.domain s1.state.S.mem) /\
      Set.equal (Map.domain s2_orig.state.S.mem) (Map.domain s2.state.S.mem) /\
      check_if_consumes_fixed_time_outs outs args oprs ts_orig /\
      publicValuesAreSame ts_orig s1_orig s2_orig /\
      publicValuesAreSame ts s1 s2
    ))
    (ensures (
      let s1' = {s1 with state = S.instr_write_outputs outs args vs oprs s1_orig.state s1.state} in
      let s2' = {s1 with state = S.instr_write_outputs outs args vs oprs s2_orig.state s2.state} in
      let ts' = instr_set_taints outs args oprs ts t in
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
          | IOp64 -> (match coerce o with OMem _ | _ -> o)
          | IOpXmm -> (match coerce o with Mov128Mem _ | _ -> o)
          in
        let s1' = {s1 with state = S.instr_write_output_explicit i v o s1_orig.state s1.state} in
        let s2' = {s2 with state = S.instr_write_output_explicit i v o s2_orig.state s2.state} in
        lemma_instr_write_outputs_ok outs args vs oprs s1_orig.state s1'.state;
        lemma_instr_write_outputs_ok outs args vs oprs s2_orig.state s2'.state;
        let ts' = instr_set_taint_explicit i o ts t in
        lemma_instr_set_taints outs args vs oprs ts_orig ts' t s1_orig s1' s2_orig s2'
      | IOpIm i ->
        let i = match i with IOp64One (OMem _) | IOpXmmOne (Mov128Mem _) | _ -> i in
        let s1' = {s1 with state = S.instr_write_output_implicit i v s1_orig.state s1.state} in
        let s2' = {s2 with state = S.instr_write_output_implicit i v s2_orig.state s2.state} in
        lemma_instr_write_outputs_ok outs args vs (coerce oprs) s1_orig.state s1'.state;
        lemma_instr_write_outputs_ok outs args vs (coerce oprs) s2_orig.state s2'.state;
        let ts' = instr_set_taint_implicit i ts t in
        lemma_instr_set_taints outs args vs (coerce oprs) ts_orig ts' t s1_orig s1' s2_orig s2'
    )

let check_if_instr_consumes_fixed_time (ins:tainted_ins) (ts:taintState) : Pure (bool & taintState)
  (requires S.Instr? ins.i)
  (ensures ins_consumes_fixed_time ins ts)
  =
  let S.Instr outs args havoc_flags iins oprs = ins.i in
  let b = check_if_consumes_fixed_time_outs outs args oprs ts in
  (b, ts)

#reset-options "--initial_ifuel 2 --max_ifuel 2 --initial_fuel 4 --max_fuel 4 --z3rlimit 80"

let check_if_ins_consumes_fixed_time ins ts =
  false, ts
  (* Verifying, but too slow. Need to refactor
  
  if S.Cpuid? ins.i then check_if_cpuid_consumes_fixed_time ins ts
  else (
  let i = ins.i in
  let dsts, srcs = extract_operands i in
  let ftSrcs = operands_do_not_use_secrets srcs ts in
  let ftDsts = operands_do_not_use_secrets dsts ts in
  let fixedTime = ftSrcs && ftDsts in

  Classical.forall_intro_2 (fun x y -> lemma_operand_obs_list ts dsts x y);
  Classical.forall_intro_2 (fun x y -> lemma_operand_obs_list ts srcs x y);
  assert (fixedTime ==> (isConstantTime (Ins ins) ts));
  if S.Mulx64? i then begin
    let S.Mulx64 dst_hi dst_lo src = i in
    let taint = sources_taint srcs ts ins.t in
    if has_mem_operand dsts && taint <> ins.t then false, ts
    else let ts' = set_taint dst_lo ts taint in
    if operand_does_not_use_secrets dst_hi ts' then fixedTime, (set_taint dst_hi ts' taint)
    else false, ts
  end
  else
  let taint = sources_taint srcs ts ins.t in
  let taint = if S.Ins_io64_64_cf? i then merge_taint taint ts.cfFlagsTaint else taint in
  if has_mem_operand dsts && taint <> ins.t then false, ts
  else
  let ts' = set_taints dsts ts taint in
  let b, ts' = match i with
    | S.Ins_64_64_preserve dst _ | S.AddLea64 dst _ _ -> begin
      match dst with
        | OConst _ -> false, ts (* Should not happen *)
        | OReg r -> fixedTime, ts'
        | OMem m -> fixedTime, ts'
        | OStack m -> false, ts
    end
     | S.Mul64 _ -> fixedTime, (TaintState ts'.regTaint Secret Secret ts'.xmmTaint)

    | S.Xor64 dst src ->
        (* Special case for Xor : xor-ing an operand with itself erases secret data *)
        if dst = src then
              let ts' = set_taint dst ts' Public in
              fixedTime, TaintState ts'.regTaint Secret Secret ts'.xmmTaint
        else
            begin match dst with
              | OConst _ -> false, (TaintState ts'.regTaint Secret Secret ts'.xmmTaint) (* Should not happen *)
              | OReg r -> fixedTime, (TaintState ts'.regTaint Secret Secret ts'.xmmTaint)
              | OMem m -> fixedTime, (TaintState ts'.regTaint Secret Secret ts'.xmmTaint)
              | OStack m -> false, ts
        end
   | S.Push src -> if Secret? (ts'.regTaint Rsp) || Secret? (operand_taint src ts' Public) then false, ts
     else fixedTime, ts'
   | S.Pop dst -> 
     // Pop should be a public instruction
     if Secret? (ts'.regTaint Rsp) || Secret? (ins.t) then false, ts 
     else fixedTime, ts'
   | S.Ins_io64_64_cf _ _ _ -> begin
          match dsts with
        | [OConst _] -> true, (TaintState ts'.regTaint Secret taint ts'.xmmTaint) (* Should not happen *)
        | [OReg r] -> fixedTime, (TaintState ts'.regTaint Secret taint ts'.xmmTaint)
        | [OMem m] -> fixedTime, (TaintState ts'.regTaint Secret taint ts'.xmmTaint)
        | [OStack m] -> false, ts
    end
    | _ ->
      match dsts with
      | [OConst _] -> false, (TaintState ts'.regTaint Secret Secret ts'.xmmTaint) (* Should not happen *)
      | [OReg r] -> fixedTime, (TaintState ts'.regTaint Secret Secret ts'.xmmTaint)
      | [OMem m] ->  fixedTime, (TaintState ts'.regTaint Secret Secret ts'.xmmTaint)
      | [OStack m] -> false, ts
      | [] -> false, ts'  (* AR: this case was missing, Unhandled yet *)
  in
  b, ts'
  )
*)
(*
let frame_update_heap_x (ptr:int) (j:int) (v:nat64) (mem:S.heap) : Lemma
  (requires j < ptr \/ j >= ptr + 8)
  (ensures (let new_mem = S.update_heap64 ptr v mem in
    mem.[j] == new_mem.[j])) = frame_update_heap ptr v mem

let lemma_mov_same_public_aux (ts:taintState) (ins:tainted_ins{S.Ins_64_64_preserve? ins.i}) (s1:traceState) (s2:traceState)
                               (fuel:nat) (b:bool) (ts':taintState)
  :Lemma (requires ((b, ts') == check_if_ins_consumes_fixed_time ins ts /\ b /\
                    is_explicit_leakage_free_lhs (Ins ins) fuel ts ts' s1 s2))
         (ensures  (is_explicit_leakage_free_rhs (Ins ins) fuel ts ts' s1 s2)) =
    let S.Ins_64_64_preserve i dst src, t = ins.i, ins.t in
    let dsts, srcs = extract_operands ins.i in

    let r1 = taint_eval_code (Ins ins) fuel s1 in
    let r2 = taint_eval_code (Ins ins) fuel s2 in

    let s1' = Some?.v r1 in
    let s2' = Some?.v r2 in

    let s1b = S.run (S.check (taint_match_list srcs t s1.memTaint)) s1.state in
    let s2b = S.run (S.check (taint_match_list srcs t s2.memTaint)) s2.state in

    let taint = sources_taint srcs ts ins.t in

    let Some v1 = instr_eval i (S.eval_operand src s1.state) in
    let Some v2 = instr_eval i (S.eval_operand src s2.state) in

    let aux_value () : Lemma 
      (requires Public? taint)
      (ensures v1 == v2) = 
      Opaque_s.reveal_opaque S.get_heap_val64_def 
    in

    match dst with
    | OConst _ -> ()
    | OReg r -> if Secret? taint then () else aux_value()
    | OMem m -> begin
      let aux (x:int) : Lemma
        (requires Public? s1'.memTaint.[x] || Public? s2'.memTaint.[x])
        (ensures s1'.state.S.mem.[x] == s2'.state.S.mem.[x]) =
        let ptr1 = S.eval_maddr m s1.state in
        let ptr2 = S.eval_maddr m s2.state in
        assert (ptr1 == ptr2);
        if x < ptr1 || x >= ptr1 + 8 then (
          // If we're outside the modified area, nothing changed, the property still holds
          frame_update_heap_x ptr1 x v1 s1b.S.mem;
          frame_update_heap_x ptr1 x v2 s2b.S.mem
        ) else (
          if Secret? taint then ()
          else (
            aux_value();
            correct_update_get ptr1 v1 s1b.S.mem;
            correct_update_get ptr1 v2 s2b.S.mem;
            // If values are identical, the bytes also are identical
            same_mem_get_heap_val ptr1 s1'.state.S.mem s2'.state.S.mem
          )
        )
      
      in Classical.forall_intro (Classical.move_requires aux)
    end

let lemma_mov_same_public (ts:taintState) (ins:tainted_ins{S.Ins_64_64_preserve? ins.i}) (s1:traceState) (s2:traceState) 
  (fuel:nat)
  :Lemma (let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))
  = let b, ts' = check_if_ins_consumes_fixed_time ins ts in
    Classical.move_requires (lemma_mov_same_public_aux ts ins s1 s2 fuel b) ts'

#set-options "--z3rlimit 400"

#set-options "--z3rlimit 80"

#set-options "--z3rlimit 400"

let lemma_addcarry_same_public_aux (ts:taintState) (ins:tainted_ins{S.Ins_io64_64_cf? ins.i}) (s1:traceState) (s2:traceState)
                               (fuel:nat) (b:bool) (ts':taintState)
  :Lemma (requires ((b, ts') == check_if_ins_consumes_fixed_time ins ts /\ b /\
                    is_explicit_leakage_free_lhs (Ins ins) fuel ts ts' s1 s2))
         (ensures  (is_explicit_leakage_free_rhs (Ins ins) fuel ts ts' s1 s2)) =
    let S.Ins_io64_64_cf i dst src, t = ins.i, ins.t in
    let dsts, srcs = extract_operands ins.i in

    let r1 = taint_eval_code (Ins ins) fuel s1 in
    let r2 = taint_eval_code (Ins ins) fuel s2 in

    let s1' = Some?.v r1 in
    let s2' = Some?.v r2 in

    let s1b = S.run (S.check (taint_match_list srcs t s1.memTaint)) s1.state in
    let s2b = S.run (S.check (taint_match_list srcs t s2.memTaint)) s2.state in

    let taint = sources_taint srcs ts ins.t in
    let taint = merge_taint taint ts.cfFlagsTaint in

    let v11 = S.eval_operand dst s1.state in
    let v12 = S.eval_operand src s1.state in
    let v21 = S.eval_operand dst s2.state in
    let v22 = S.eval_operand src s2.state in
    let c1 = S.cf s1.state.S.flags in
    let c2 = S.cf s2.state.S.flags in
    let Some (new_carry1, v1) = instr_eval i c1 v11 v12 in
    let Some (new_carry2, v2) = instr_eval i c2 v21 v22 in

    let aux_value () : Lemma 
      (requires Public? taint)
      (ensures v1 == v2) =
      Opaque_s.reveal_opaque S.get_heap_val64_def 
    in

    let aux_carry () : Lemma 
      (requires Public? taint)
      (ensures new_carry1 == new_carry2) =
      Opaque_s.reveal_opaque S.get_heap_val64_def 
    in

    match dst with
    | OConst _ -> ()
    | OReg r -> if Secret? taint then () else aux_value()
    | OMem m -> begin
      let aux_cf () : Lemma (publicCfFlagValuesAreSame ts' s1' s2') =
        if Secret? taint then () else aux_carry()    
      in let aux (x:int) : Lemma
        (requires Public? s1'.memTaint.[x] || Public? s2'.memTaint.[x])
        (ensures s1'.state.S.mem.[x] == s2'.state.S.mem.[x]) =
        let ptr1 = S.eval_maddr m s1.state in
        let ptr2 = S.eval_maddr m s2.state in
        assert (ptr1 == ptr2);
        if x < ptr1 || x >= ptr1 + 8 then (
          // If we're outside the modified area, nothing changed, the property still holds
          frame_update_heap_x ptr1 x v1 s1b.S.mem;
          frame_update_heap_x ptr1 x v2 s2b.S.mem
        ) else (
          if Secret? taint then ()
          else (
            aux_value();
            correct_update_get ptr1 v1 s1b.S.mem;
            correct_update_get ptr1 v2 s2b.S.mem;
            // If values are identical, the bytes also are identical
            same_mem_get_heap_val ptr1 s1'.state.S.mem s2'.state.S.mem
          )
        )
      
      in Classical.forall_intro (Classical.move_requires aux); aux_cf()
    end

let lemma_addcarry_same_public (ts:taintState) (ins:tainted_ins{S.Ins_io64_64_cf? ins.i}) (s1:traceState) (s2:traceState) 
  (fuel:nat)
  :Lemma (let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))
  = let b, ts' = check_if_ins_consumes_fixed_time ins ts in
    Classical.move_requires (lemma_addcarry_same_public_aux ts ins s1 s2 fuel b) ts'

#reset-options "--initial_ifuel 2 --max_ifuel 2 --initial_fuel 4 --max_fuel 4 --z3rlimit 400"

#set-options "--z3rlimit 80"

val lemma_aux_xor: (x:nat64) -> Lemma (Types_s.ixor x x = 0)

let lemma_aux_xor x =
  TypesNative_s.reveal_ixor 64 x x;
  FStar.UInt.logxor_self #64 x

let lemma_xor_same_public_aux (ts:taintState) (ins:tainted_ins{S.Xor64? ins.i}) (s1:traceState) (s2:traceState)
                               (fuel:nat) (b:bool) (ts':taintState)
  :Lemma (requires ((b, ts') == check_if_ins_consumes_fixed_time ins ts /\ b /\
                    is_explicit_leakage_free_lhs (Ins ins) fuel ts ts' s1 s2))
         (ensures  (is_explicit_leakage_free_rhs (Ins ins) fuel ts ts' s1 s2)) =
    let S.Xor64 dst src, t = ins.i, ins.t in
    let dsts, srcs = extract_operands ins.i in

    Classical.forall_intro lemma_aux_xor;

    let r1 = taint_eval_code (Ins ins) fuel s1 in
    let r2 = taint_eval_code (Ins ins) fuel s2 in

    let s1' = Some?.v r1 in
    let s2' = Some?.v r2 in

    let s1b = S.run (S.check (taint_match_list srcs t s1.memTaint)) s1.state in
    let s2b = S.run (S.check (taint_match_list srcs t s2.memTaint)) s2.state in

    let taint = sources_taint srcs ts ins.t in

    let v11 = S.eval_operand dst s1.state in
    let v12 = S.eval_operand src s1.state in
    let v21 = S.eval_operand dst s2.state in
    let v22 = S.eval_operand src s2.state in
    let v1 = Types_s.ixor v11 v12 in
    let v2 = Types_s.ixor v21 v22 in

    let aux_value () : Lemma 
      (requires Public? taint)
      (ensures v1 == v2) = 
      Opaque_s.reveal_opaque S.get_heap_val64_def 
    in

    match dst with
    | OConst _ -> ()
    | OReg r -> if Secret? taint then () else aux_value()
    | OMem m -> begin
      let aux (x:int) : Lemma
        (requires Public? s1'.memTaint.[x] || Public? s2'.memTaint.[x])
        (ensures s1'.state.S.mem.[x] == s2'.state.S.mem.[x]) =
        let ptr1 = S.eval_maddr m s1.state in
        let ptr2 = S.eval_maddr m s2.state in
        assert (ptr1 == ptr2);
         if x < ptr1 || x >= ptr1 + 8 then (
          // If we're outside the modified area, nothing changed, the property still holds
          frame_update_heap_x ptr1 x v1 s1b.S.mem;
          frame_update_heap_x ptr1 x v2 s2b.S.mem
        ) else (
          if Secret? taint then ()
          else (
            aux_value();
            correct_update_get ptr1 v1 s1b.S.mem;
            correct_update_get ptr1 v2 s2b.S.mem;
            // If values are identical, the bytes also are identical
            same_mem_get_heap_val ptr1 s1'.state.S.mem s2'.state.S.mem
          )
        )
      
      in Classical.forall_intro (Classical.move_requires aux)
    end

let lemma_xor_same_public (ts:taintState) (ins:tainted_ins{S.Xor64? ins.i}) (s1:traceState) (s2:traceState) 
  (fuel:nat)
  :Lemma (let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))
  = let b, ts' = check_if_ins_consumes_fixed_time ins ts in
    Classical.move_requires (lemma_xor_same_public_aux ts ins s1 s2 fuel b) ts'


let lemma_and_same_public_aux (ts:taintState) (ins:tainted_ins{S.Ins_io64_64? ins.i}) (s1:traceState) (s2:traceState)
                               (fuel:nat) (b:bool) (ts':taintState)
  :Lemma (requires ((b, ts') == check_if_ins_consumes_fixed_time ins ts /\ b /\
                    is_explicit_leakage_free_lhs (Ins ins) fuel ts ts' s1 s2))
         (ensures  (is_explicit_leakage_free_rhs (Ins ins) fuel ts ts' s1 s2)) =
    let S.Ins_io64_64 i dst src, t = ins.i, ins.t in
    let dsts, srcs = extract_operands ins.i in

    let r1 = taint_eval_code (Ins ins) fuel s1 in
    let r2 = taint_eval_code (Ins ins) fuel s2 in

    let s1' = Some?.v r1 in
    let s2' = Some?.v r2 in

    let s1b = S.run (S.check (taint_match_list srcs t s1.memTaint)) s1.state in
    let s2b = S.run (S.check (taint_match_list srcs t s2.memTaint)) s2.state in

    let taint = sources_taint srcs ts ins.t in

    let v11 = S.eval_operand dst s1.state in
    let v12 = S.eval_operand src s1.state in
    let v21 = S.eval_operand dst s2.state in
    let v22 = S.eval_operand src s2.state in
    let Some v1 = instr_eval i v11 v12 in
    let Some v2 = instr_eval i v21 v22 in

    let aux_value () : Lemma 
      (requires Public? taint)
      (ensures v1 == v2) = 
      Opaque_s.reveal_opaque S.get_heap_val64_def 
    in

    match dst with
    | OConst _ -> ()
    | OReg r -> if Secret? taint then () else aux_value()
    | OMem m -> begin
      let aux (x:int) : Lemma
        (requires Public? s1'.memTaint.[x] || Public? s2'.memTaint.[x])
        (ensures s1'.state.S.mem.[x] == s2'.state.S.mem.[x]) =
        let ptr1 = S.eval_maddr m s1.state in
        let ptr2 = S.eval_maddr m s2.state in
        assert (ptr1 == ptr2);
         if x < ptr1 || x >= ptr1 + 8 then (
          // If we're outside the modified area, nothing changed, the property still holds
          frame_update_heap_x ptr1 x v1 s1b.S.mem;
          frame_update_heap_x ptr1 x v2 s2b.S.mem
        ) else (
          if Secret? taint then ()
          else (
            aux_value();
            correct_update_get ptr1 v1 s1b.S.mem;
            correct_update_get ptr1 v2 s2b.S.mem;
            // If values are identical, the bytes also are identical
            same_mem_get_heap_val ptr1 s1'.state.S.mem s2'.state.S.mem
          )
        )
      
      in Classical.forall_intro (Classical.move_requires aux)
    end

let lemma_and_same_public (ts:taintState) (ins:tainted_ins{S.Ins_io64_64? ins.i}) (s1:traceState) (s2:traceState) 
  (fuel:nat)
  :Lemma (let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))
  = let b, ts' = check_if_ins_consumes_fixed_time ins ts in
    Classical.move_requires (lemma_and_same_public_aux ts ins s1 s2 fuel b) ts'

let lemma_push_same_public_aux (ts:taintState) (ins:tainted_ins{S.Push? ins.i}) (s1:traceState) (s2:traceState)
                               (fuel:nat) (b:bool) (ts':taintState)
  :Lemma (requires ((b, ts') == check_if_ins_consumes_fixed_time ins ts /\ b /\
                    is_explicit_leakage_free_lhs (Ins ins) fuel ts ts' s1 s2))
         (ensures  (is_explicit_leakage_free_rhs (Ins ins) fuel ts ts' s1 s2))
  = let S.Push src, t = ins.i, ins.t in
    let dsts, srcs = extract_operands ins.i in

    let r1 = taint_eval_code (Ins ins) fuel s1 in
    let r2 = taint_eval_code (Ins ins) fuel s2 in

    let s1' = Some?.v r1 in
    let s2' = Some?.v r2 in

    // We only need to help Z3 proving that public mem values are identical 
    // after executing this instruction

    let aux (x:int) : Lemma
      (requires Public? s1'.memTaint.[x] || Public? s2'.memTaint.[x])
      (ensures s1'.state.S.mem.[x] == s2'.state.S.mem.[x]) =
        let ptr1 = ((S.eval_reg Rsp s1.state) - 8) % pow2_64 in
        let ptr2 = ((S.eval_reg Rsp s2.state) - 8) % pow2_64 in
        // Rsp is ensured to be Public if the taint analysis is successful
        assert (ptr1 == ptr2);
        let v1 = S.eval_operand src s1.state in
        let v2 = S.eval_operand src s2.state in
        // The instruction is executed after checking the taints of sources
        let s1b = S.run (S.check (taint_match_list srcs t s1.memTaint)) s1.state in
        let s2b = S.run (S.check (taint_match_list srcs t s2.memTaint)) s2.state in
        if x < ptr1 || x >= ptr1 + 8 then (
          // If we're outside the modified area, nothing changed, the property still holds
          frame_update_heap_x ptr1 x v1 s1b.S.mem;
          frame_update_heap_x ptr1 x v2 s2b.S.mem
        ) else (
          if Secret? t then ()
          else (
            Opaque_s.reveal_opaque S.get_heap_val64_def;
            // If x is modified by Public values, values are identical            
            assert (v1 == v2);
            correct_update_get ptr1 v1 s1b.S.mem;
            correct_update_get ptr1 v2 s2b.S.mem;
            // If values are identical, the bytes also are identical
            same_mem_get_heap_val ptr1 s1'.state.S.mem s2'.state.S.mem
          )
        )
        
    in Classical.forall_intro (Classical.move_requires aux)

let lemma_push_same_public (ts:taintState) (ins:tainted_ins{S.Push? ins.i}) (s1:traceState) (s2:traceState)
                           (fuel:nat)
  :Lemma (let b, ts' = check_if_ins_consumes_fixed_time ins ts in
          (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))
  = let b, ts' = check_if_ins_consumes_fixed_time ins ts in
    Classical.move_requires (lemma_push_same_public_aux ts ins s1 s2 fuel b) ts'

let lemma_pop_same_public_aux (ts:taintState) (ins:tainted_ins{S.Pop? ins.i}) (s1:traceState) (s2:traceState)
                               (fuel:nat) (b:bool) (ts':taintState)
  :Lemma (requires ((b, ts') == check_if_ins_consumes_fixed_time ins ts /\ b /\
                    is_explicit_leakage_free_lhs (Ins ins) fuel ts ts' s1 s2))
         (ensures  (is_explicit_leakage_free_rhs (Ins ins) fuel ts ts' s1 s2)) =
    let S.Pop dst, t = ins.i, ins.t in
    let dsts, srcs = extract_operands ins.i in

    let r1 = taint_eval_code (Ins ins) fuel s1 in
    let r2 = taint_eval_code (Ins ins) fuel s2 in

    let s1' = Some?.v r1 in
    let s2' = Some?.v r2 in

    let op = OMem (MReg Rsp 0) in

    let v1 = S.eval_operand op s1.state in
    let v2 = S.eval_operand op s2.state in
    let aux_value () : Lemma (v1 == v2) = Opaque_s.reveal_opaque S.get_heap_val64_def in
    aux_value();

    // We only need to help Z3 proving that public mem values are identical 
    // after executing this instruction

    let aux (x:int) : Lemma
      (requires Public? s1'.memTaint.[x] || Public? s2'.memTaint.[x])
      (ensures s1'.state.S.mem.[x] == s2'.state.S.mem.[x]) =
        match dst with
        | OConst _ | OReg _ -> ()
        | OMem m -> begin
        let ptr1 = S.eval_maddr m s1.state in
        let ptr2 = S.eval_maddr m s2.state in
        // Rsp is ensured to be Public if the taint analysis is successful
        assert (ptr1 == ptr2);
        // The instruction is executed after checking the taints of sources
        let s1b = S.run (S.check (taint_match_list srcs t s1.memTaint)) s1.state in
        let s2b = S.run (S.check (taint_match_list srcs t s2.memTaint)) s2.state in
        if x < ptr1 || x >= ptr1 + 8 then (
          // If we're outside the modified area, nothing changed, the property still holds
          frame_update_heap_x ptr1 x v1 s1b.S.mem;
          frame_update_heap_x ptr1 x v2 s2b.S.mem
        ) else (
          if Secret? t then ()
          else (
            correct_update_get ptr1 v1 s1b.S.mem;
            correct_update_get ptr1 v2 s2b.S.mem;
            // If values are identical, the bytes also are identical
            same_mem_get_heap_val ptr1 s1'.state.S.mem s2'.state.S.mem
          )
        )
        end
        
    in Classical.forall_intro (Classical.move_requires aux)


let lemma_pop_same_public (ts:taintState) (ins:tainted_ins{S.Pop? ins.i}) (s1:traceState) (s2:traceState) 
  (fuel:nat)
  :Lemma (let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))
  = let b, ts' = check_if_ins_consumes_fixed_time ins ts in
    Classical.move_requires (lemma_pop_same_public_aux ts ins s1 s2 fuel b) ts'

#reset-options "--initial_ifuel 2 --max_ifuel 2 --initial_fuel 4 --max_fuel 4 --z3rlimit 20"
val lemma_ins_same_public: (ts:taintState) -> (ins:tainted_ins{not (is_xmm_ins ins)}) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))
*)
let lemma_ins_same_public ts ins s1 s2 fuel = ()
(*  match ins.i with
  | S.Ins_64_64_preserve _ _ _ -> lemma_mov_same_public ts ins s1 s2 fuel
  | S.Ins_io64_64 _ _ _ -> lemma_and_same_public ts ins s1 s2 fuel
  | S.Ins_io64_64_cf _ _ _ -> lemma_addcarry_same_public ts ins s1 s2 fuel
  | S.Xor64 _ _ -> lemma_xor_same_public ts ins s1 s2 fuel
  | S.Push _ -> lemma_push_same_public ts ins s1 s2 fuel
  | S.Pop _ -> lemma_pop_same_public ts ins s1 s2 fuel
  | S.Alloc _ -> ()
  | S.Dealloc _ -> ()
*)
let lemma_ins_leakage_free ts ins =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let p s1 s2 fuel = b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2 in
  let my_lemma s1 s2 fuel : Lemma(p s1 s2 fuel) = lemma_ins_same_public ts ins s1 s2 fuel in
  let open FStar.Classical in
  forall_intro_3 my_lemma
