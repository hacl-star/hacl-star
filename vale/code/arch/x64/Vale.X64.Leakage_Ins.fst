module Vale.X64.Leakage_Ins
open FStar.Mul
open Vale.Arch.MachineHeap_s
open Vale.Arch.Heap
open Vale.X64.Machine_s
open Vale.X64.Instruction_s
module BC = Vale.X64.Bytes_Code_s
module S = Vale.X64.Machine_Semantics_s
open Vale.X64.Leakage_s
open Vale.X64.Leakage_Helpers

unfold let (.[]) = Map.sel
unfold let (.[]<-) = Map.upd

unfold let obs_args = S.obs_args
unfold let obs_inouts = S.obs_inouts
unfold let machine_eval_code = S.machine_eval_code

let rec check_if_consumes_fixed_time_args
    (args:list instr_operand) (oprs:instr_operands_t_args args) (ts:analysis_taints)
  : Pure bool
    (requires True)
    (ensures fun b -> b ==> (forall (s1 s2:S.machine_state).{:pattern (constTimeInvariant ts.lts s1 s2)}
      constTimeInvariant ts.lts s1 s2 ==> obs_args args oprs s1 == obs_args args oprs s2))
  =
  allow_inversion maddr;
  allow_inversion tmaddr;
  match args with
  | [] -> true
  | (IOpEx i)::args ->
    let ((o:instr_operand_t i), (oprs:instr_operands_t_args args)) = coerce oprs in
    let b' =
      match i with
      | IOp64 -> operand_does_not_use_secrets #nat64 #reg_64 o ts
      | IOpXmm -> operand_does_not_use_secrets #quad32 #reg_xmm o ts
      in
    let b'' = check_if_consumes_fixed_time_args args oprs ts in
    b' && b''
  | (IOpIm i)::args ->
    let b' =
      match i with
      | IOp64One o -> operand_does_not_use_secrets o ts
      | IOpXmmOne o -> operand_does_not_use_secrets o ts
      | IOpFlagsCf -> true
      | IOpFlagsOf -> true
      in
    let b'' = check_if_consumes_fixed_time_args args (coerce oprs) ts in
    b' && b''

let check_if_consumes_fixed_time_outs_explicit
    (i:instr_operand_explicit) (o:instr_operand_t i)
    (ts:analysis_taints) (t_out:taint)
  : bool
  =
  match i with
  | IOp64 -> operand_does_not_use_secrets #nat64 #reg_64 o ts && operand_taint_allowed #nat64 #reg_64 o t_out
  | IOpXmm -> operand_does_not_use_secrets #quad32 #reg_xmm o ts && operand_taint_allowed #quad32 #reg_xmm o t_out

let check_if_consumes_fixed_time_outs_implicit
    (i:instr_operand_implicit) (ts:analysis_taints) (t_out:taint)
  : bool
  =
  match i with
  | IOp64One o -> operand_does_not_use_secrets o ts && operand_taint_allowed o t_out
  | IOpXmmOne o -> operand_does_not_use_secrets o ts && operand_taint_allowed o t_out
  | IOpFlagsCf -> true
  | IOpFlagsOf -> true

let rec check_if_consumes_fixed_time_outs
    (outs:list instr_out) (args:list instr_operand) (oprs:instr_operands_t outs args)
    (ts:analysis_taints) (t_out:taint)
  : Pure bool
    (requires True)
    (ensures fun b -> b ==> (forall (s1 s2:S.machine_state).{:pattern (constTimeInvariant ts.lts s1 s2)}
      constTimeInvariant ts.lts s1 s2 ==> obs_inouts outs args oprs s1 == obs_inouts outs args oprs s2))
  =
  allow_inversion maddr;
  allow_inversion tmaddr;
  allow_inversion operand64;
  allow_inversion operand128;
  match outs with
  | [] -> check_if_consumes_fixed_time_args args oprs ts
  | (_, IOpEx i)::outs ->
    let ((o:instr_operand_t i), (oprs:instr_operands_t outs args)) = coerce oprs in
    let b' = check_if_consumes_fixed_time_outs_explicit i o ts t_out in
    let b'' = check_if_consumes_fixed_time_outs outs args oprs ts t_out in
    b' && b''
  | (_, IOpIm i)::outs ->
    let b' = check_if_consumes_fixed_time_outs_implicit i ts t_out in
    let b'' = check_if_consumes_fixed_time_outs outs args (coerce oprs) ts t_out in
    b' && b''

#restart-solver
#reset-options "--z3rlimit 300"
let rec lemma_args_taint
    (outs:list instr_out) (args:list instr_operand)
    (f:instr_args_t outs args) (oprs:instr_operands_t_args args)
    (ts:analysis_taints) (s1 s2:S.machine_state)
  : Lemma
    (requires
      constTimeInvariant ts.lts s1 s2 /\
      Some? (S.instr_apply_eval_args outs args f oprs s1) /\
      Some? (S.instr_apply_eval_args outs args f oprs s2) /\
      check_if_consumes_fixed_time_args args oprs ts /\
      args_taint args oprs ts == Public)
    (ensures
      S.instr_apply_eval_args outs args f oprs s1 ==
      S.instr_apply_eval_args outs args f oprs s2)
  =
  allow_inversion maddr;
  allow_inversion tmaddr;
  allow_inversion operand64;
  allow_inversion operand128;
  match args with
  | [] -> ()
  | i::args ->
    let (v1, v2, oprs) : option (instr_val_t i) & option (instr_val_t i) & instr_operands_t_args args =
      match i with
      | IOpEx i ->
        let (o, (oprs:instr_operands_t_args args)) = coerce oprs in
        (
          S.instr_eval_operand_explicit i o s1,
          S.instr_eval_operand_explicit i o s2,
          oprs)
      | IOpIm i ->
        let oprs = coerce oprs in (
          S.instr_eval_operand_implicit i s1,
          S.instr_eval_operand_implicit i s2,
          oprs)
      in
    let f:arrow (instr_val_t i) (instr_args_t outs args) = coerce f in
    S.get_heap_val32_reveal ();
    S.get_heap_val64_reveal ();
    S.get_heap_val128_reveal ();
    assert (v1 == v2);
    let Some v = v1 in
    lemma_args_taint outs args (f v) oprs ts s1 s2

#restart-solver
let rec lemma_inouts_taint
    (outs inouts:list instr_out) (args:list instr_operand)
    (f:instr_inouts_t outs inouts args) (oprs:instr_operands_t inouts args)
    (ts:analysis_taints) (s1 s2:S.machine_state)
  : Lemma
    (requires
      constTimeInvariant ts.lts s1 s2 /\
      Some? (S.instr_apply_eval_inouts outs inouts args f oprs s1) /\
      Some? (S.instr_apply_eval_inouts outs inouts args f oprs s2) /\
      check_if_consumes_fixed_time_outs inouts args oprs ts Public /\
      inouts_taint inouts args oprs ts == Public)
    (ensures
      S.instr_apply_eval_inouts outs inouts args f oprs s1 ==
      S.instr_apply_eval_inouts outs inouts args f oprs s2)
  =
  allow_inversion maddr;
  allow_inversion tmaddr;
  allow_inversion operand64;
  allow_inversion operand128;
  match inouts with
  | [] -> lemma_args_taint outs args f oprs ts s1 s2
  | (Out, i)::inouts ->
    let oprs =
      match i with
      | IOpEx i -> snd #(instr_operand_t i) (coerce oprs)
      | IOpIm i -> coerce oprs
      in
    lemma_inouts_taint outs inouts args (coerce f) oprs ts s1 s2
  | (InOut, i)::inouts ->
    let (v1, v2, oprs) : option (instr_val_t i) & option (instr_val_t i) & instr_operands_t inouts args =
      match i with
      | IOpEx i ->
        let (o, (oprs:instr_operands_t inouts args)) = coerce oprs in
        let oprs = coerce oprs in (
          S.instr_eval_operand_explicit i o s1,
          S.instr_eval_operand_explicit i o s2,
          oprs)
      | IOpIm i ->
        let oprs = coerce oprs in (
          S.instr_eval_operand_implicit i s1,
          S.instr_eval_operand_implicit i s2,
          oprs)
      in
    let f:arrow (instr_val_t i) (instr_inouts_t outs inouts args) = coerce f in
    S.get_heap_val32_reveal ();
    S.get_heap_val64_reveal ();
    S.get_heap_val128_reveal ();
    assert (v1 == v2);
    let Some v = v1 in
    lemma_inouts_taint outs inouts args (f v) oprs ts s1 s2

let instr_set_taint_explicit
    (i:instr_operand_explicit) (o:instr_operand_t i) (ts:analysis_taints) (t:taint)
  : analysis_taints =
  match i with
  | IOp64 -> set_taint 0 (o <: operand64) ts t
  | IOpXmm -> set_taint 1 (o <: operand128) ts t

[@instr_attr]
let instr_set_taint_implicit (i:instr_operand_implicit) (ts:analysis_taints) (t:taint) : analysis_taints =
  match i with
  | IOp64One o -> set_taint 0 o ts t
  | IOpXmmOne o -> set_taint 1 o ts t
  | IOpFlagsCf -> set_taint_cf_and_flags ts t
  | IOpFlagsOf -> set_taint_of_and_flags ts t

let rec instr_set_taints
    (outs:list instr_out) (args:list instr_operand)
    (oprs:instr_operands_t outs args) (ts:analysis_taints) (t:taint)
  : analysis_taints =
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
    (vs:instr_ret_t outs) (oprs:instr_operands_t outs args) (s_orig s:S.machine_state)
  : Lemma
    (requires (S.instr_write_outputs outs args vs oprs s_orig s).S.ms_ok)
    (ensures s.S.ms_ok)
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
let update_heap32_val (ptr:int) (v:Vale.Def.Types_s.nat32) (i:int) : Vale.Def.Types_s.nat8 =
  let open Vale.Def.Words_s in
  let open Vale.Def.Words.Four_s in
  let v = nat_to_four 8 v in
  match (i - ptr) with
  | 0 -> v.lo0
  | 1 -> v.lo1
  | 2 -> v.hi2
  | 3 -> v.hi3
  | _ -> 0

let valid_addr32 (ptr:int) (mem:S.machine_heap) : bool =
  S.valid_addr (ptr + 0) mem &&
  S.valid_addr (ptr + 1) mem &&
  S.valid_addr (ptr + 2) mem &&
  S.valid_addr (ptr + 3) mem

let lemma_update_heap32_val (ptr:int) (v:Vale.Def.Types_s.nat32) (mem:S.machine_heap) (i:int) : Lemma
  (requires True)
  (ensures (S.update_heap32 ptr v mem).[i] ==
    (if ptr <= i && i < ptr + 4 then update_heap32_val ptr v i else mem.[i]))
  [SMTPat ((S.update_heap32 ptr v mem).[i])]
  =
  S.update_heap32_reveal ();
  reveal_opaque (`%update_heap32_val) update_heap32_val

let lemma_update_heap32_domain (ptr:int) (v:Vale.Def.Types_s.nat32) (mem:S.machine_heap) : Lemma
  (requires valid_addr32 ptr mem)
  (ensures Map.domain (S.update_heap32 ptr v mem) == Map.domain mem)
  [SMTPat (Map.domain (S.update_heap32 ptr v mem))]
  =
  S.update_heap32_reveal ();
  assert (Set.equal (Map.domain (S.update_heap32 ptr v mem)) (Map.domain mem))

[@"opaque_to_smt"]
let update_heap64_val (ptr:int) (v:nat64) (i:int) : Vale.Def.Types_s.nat8 =
  let open Vale.Def.Words_s in
  let open Vale.Def.Words.Two_s in
  let open Vale.Def.Words.Four_s in
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

let lemma_update_heap64_val (ptr:int) (v:nat64) (mem:S.machine_heap) (i:int) : Lemma
  (requires True)
  (ensures
    (S.update_heap64 ptr v mem).[i] ==
    (if ptr <= i && i < ptr + 8 then update_heap64_val ptr v i else mem.[i])
  )
  [SMTPat ((S.update_heap64 ptr v mem).[i])]
  =
  S.update_heap64_reveal ();
  reveal_opaque (`%update_heap64_val) update_heap64_val

let lemma_update_heap64_domain (ptr:int) (v:nat64) (mem:S.machine_heap) : Lemma
  (requires S.valid_addr64 ptr mem)
  (ensures Map.domain (S.update_heap64 ptr v mem) == Map.domain mem)
  [SMTPat (Map.domain (S.update_heap64 ptr v mem))]
  =
  reveal_opaque (`%S.valid_addr64) S.valid_addr64;
  S.update_heap64_reveal ();
  assert (Set.equal (Map.domain (S.update_heap64 ptr v mem)) (Map.domain mem))

[@"opaque_to_smt"]
let update_heap128_val (ptr:int) (v:Vale.Def.Types_s.quad32) (i:int) : Vale.Def.Types_s.nat8 =
  let open Vale.Def.Words_s in
  let j = i - ptr in
  if  0 <= j && j <  4 then update_heap32_val (ptr + 0 ) v.lo0 i else
  if  4 <= j && j <  8 then update_heap32_val (ptr + 4 ) v.lo1 i else
  if  8 <= j && j < 12 then update_heap32_val (ptr + 8 ) v.hi2 i else
  if 12 <= j && j < 16 then update_heap32_val (ptr + 12) v.hi3 i else
  0

let valid_addr128 (ptr:int) (mem:S.machine_heap) : bool =
  valid_addr32 (ptr + 0) mem &&
  valid_addr32 (ptr + 4) mem &&
  valid_addr32 (ptr + 8) mem &&
  valid_addr32 (ptr + 12) mem

let lemma_update_heap128_val (ptr:int) (v:Vale.Def.Types_s.quad32) (mem:S.machine_heap) (i:int) : Lemma
  (requires True)
  (ensures
    (S.update_heap128 ptr v mem).[i] ==
    (if ptr <= i && i < ptr + 16 then update_heap128_val ptr v i else mem.[i])
  )
  [SMTPat ((S.update_heap128 ptr v mem).[i])]
  =
  S.update_heap128_reveal ();
  reveal_opaque (`%update_heap128_val) update_heap128_val

let lemma_update_heap128_domain (ptr:int) (v:Vale.Def.Types_s.quad32) (mem:S.machine_heap) : Lemma
  (requires valid_addr128 ptr mem)
  (ensures Map.domain (S.update_heap128 ptr v mem) == Map.domain mem)
  [SMTPat (S.update_heap128 ptr v mem)]
  =
  S.update_heap128_reveal ();
  assert (Set.equal (Map.domain (S.update_heap128 ptr v mem)) (Map.domain mem))

let lemma_preserve_valid64 (m m':S.machine_heap) : Lemma
  (requires Set.equal (Map.domain m) (Map.domain m'))
  (ensures (forall (i:int).{:pattern (S.valid_addr64 i m')}
    S.valid_addr64 i m ==> S.valid_addr64 i m'))
  =
  reveal_opaque (`%S.valid_addr64) S.valid_addr64

let lemma_preserve_valid128 (m m':S.machine_heap) : Lemma
  (requires Set.equal (Map.domain m) (Map.domain m'))
  (ensures (forall (i:int).{:pattern (S.valid_addr128 i m')}
    S.valid_addr128 i m ==> S.valid_addr128 i m'))
  =
  reveal_opaque (`%S.valid_addr128) S.valid_addr128

let lemma_instr_set_taints_explicit
    (i:instr_operand_explicit) (v1 v2:instr_val_t (IOpEx i)) (o:instr_operand_t i)
    (ts_orig ts:analysis_taints) (t_out:taint)
    (s1_orig s1 s2_orig s2:S.machine_state)
  : Lemma
    (requires (
      let s1' = S.instr_write_output_explicit i v1 o s1_orig s1 in
      let s2' = S.instr_write_output_explicit i v2 o s2_orig s2 in
      s1'.S.ms_ok /\ s2'.S.ms_ok /\
      (t_out == Public ==> v1 == v2) /\
      Set.equal (Map.domain (heap_get s1_orig.S.ms_heap)) (Map.domain (heap_get s1.S.ms_heap)) /\
      Set.equal (Map.domain (heap_get s2_orig.S.ms_heap)) (Map.domain (heap_get s2.S.ms_heap)) /\
      check_if_consumes_fixed_time_outs_explicit i o ts_orig t_out /\
      publicValuesAreSame ts_orig.lts s1_orig s2_orig /\
      publicValuesAreSame ts.lts s1 s2
    ))
    (ensures (
      let s1' = S.instr_write_output_explicit i v1 o s1_orig s1 in
      let s2' = S.instr_write_output_explicit i v2 o s2_orig s2 in
      let ts' = instr_set_taint_explicit i o ts t_out in
      Set.equal (Map.domain (heap_get s1_orig.S.ms_heap)) (Map.domain (heap_get s1'.S.ms_heap)) /\
      Set.equal (Map.domain (heap_get s2_orig.S.ms_heap)) (Map.domain (heap_get s2'.S.ms_heap)) /\
      publicValuesAreSame ts'.lts s1' s2'
    ))
  =
  allow_inversion maddr;
  allow_inversion tmaddr;
  lemma_preserve_valid64 (heap_get s1_orig.S.ms_heap) (heap_get s1.S.ms_heap);
  lemma_preserve_valid64 (heap_get s2_orig.S.ms_heap) (heap_get s2.S.ms_heap);
  lemma_preserve_valid128 (heap_get s1_orig.S.ms_heap) (heap_get s1.S.ms_heap);
  lemma_preserve_valid128 (heap_get s2_orig.S.ms_heap) (heap_get s2.S.ms_heap);
  reveal_opaque (`%S.valid_addr128) S.valid_addr128;
  ()

let lemma_instr_set_taints_implicit
    (i:instr_operand_implicit) (v1 v2:instr_val_t (IOpIm i))
    (ts_orig ts:analysis_taints) (t_out:taint)
    (s1_orig s1 s2_orig s2:S.machine_state)
  : Lemma
    (requires (
      let s1' = S.instr_write_output_implicit i v1 s1_orig s1 in
      let s2' = S.instr_write_output_implicit i v2 s2_orig s2 in
      s1'.S.ms_ok /\ s2'.S.ms_ok /\
      (t_out == Public ==> v1 == v2) /\
      Set.equal (Map.domain (heap_get s1_orig.S.ms_heap)) (Map.domain (heap_get s1.S.ms_heap)) /\
      Set.equal (Map.domain (heap_get s2_orig.S.ms_heap)) (Map.domain (heap_get s2.S.ms_heap)) /\
      check_if_consumes_fixed_time_outs_implicit i ts_orig t_out /\
      publicValuesAreSame ts_orig.lts s1_orig s2_orig /\
      publicValuesAreSame ts.lts s1 s2
    ))
    (ensures (
      let s1' = S.instr_write_output_implicit i v1 s1_orig s1 in
      let s2' = S.instr_write_output_implicit i v2 s2_orig s2 in
      let ts' = instr_set_taint_implicit i ts t_out in
      Set.equal (Map.domain (heap_get s1_orig.S.ms_heap)) (Map.domain (heap_get s1'.S.ms_heap)) /\
      Set.equal (Map.domain (heap_get s2_orig.S.ms_heap)) (Map.domain (heap_get s2'.S.ms_heap)) /\
      publicValuesAreSame ts'.lts s1' s2'
    ))
  =
  allow_inversion maddr;
  allow_inversion tmaddr;
  allow_inversion operand64;
  allow_inversion operand128;
  lemma_preserve_valid64 (heap_get s1_orig.S.ms_heap) (heap_get s1.S.ms_heap);
  lemma_preserve_valid64 (heap_get s2_orig.S.ms_heap) (heap_get s2.S.ms_heap);
  lemma_preserve_valid128 (heap_get s1_orig.S.ms_heap) (heap_get s1.S.ms_heap);
  lemma_preserve_valid128 (heap_get s2_orig.S.ms_heap) (heap_get s2.S.ms_heap);
  reveal_opaque (`%S.valid_addr128) S.valid_addr128;
  ()

#reset-options "--z3rlimit 80"
let rec lemma_instr_set_taints
    (outs:list instr_out) (args:list instr_operand)
    (vs1 vs2:instr_ret_t outs) (oprs:instr_operands_t outs args)
    (ts_orig ts:analysis_taints) (t_out:taint)
    (s1_orig s1 s2_orig s2:S.machine_state)
  : Lemma
    (requires (
      let s1_state' = S.instr_write_outputs outs args vs1 oprs s1_orig s1 in
      let s2_state' = S.instr_write_outputs outs args vs2 oprs s2_orig s2 in
      s1_state'.S.ms_ok /\ s2_state'.S.ms_ok /\
      (t_out == Public ==> vs1 == vs2) /\
      Set.equal (Map.domain (heap_get s1_orig.S.ms_heap)) (Map.domain (heap_get s1.S.ms_heap)) /\
      Set.equal (Map.domain (heap_get s2_orig.S.ms_heap)) (Map.domain (heap_get s2.S.ms_heap)) /\
      check_if_consumes_fixed_time_outs outs args oprs ts_orig t_out /\
      publicValuesAreSame ts_orig.lts s1_orig s2_orig /\
      publicValuesAreSame ts.lts s1 s2
    ))
    (ensures (
      let s1' = S.instr_write_outputs outs args vs1 oprs s1_orig s1 in
      let s2' = S.instr_write_outputs outs args vs2 oprs s2_orig s2 in
      let ts' = instr_set_taints outs args oprs ts t_out in
      publicValuesAreSame ts'.lts s1' s2'
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
        let s1' = S.instr_write_output_explicit i v1 o s1_orig s1 in
        let s2' = S.instr_write_output_explicit i v2 o s2_orig s2 in
        lemma_instr_write_outputs_ok outs args vs1 oprs s1_orig s1';
        lemma_instr_write_outputs_ok outs args vs2 oprs s2_orig s2';
        let ts' = instr_set_taint_explicit i o ts t_out in
        lemma_instr_set_taints_explicit i v1 v2 o ts_orig ts t_out s1_orig s1 s2_orig s2;
        lemma_instr_set_taints outs args vs1 vs2 oprs ts_orig ts' t_out s1_orig s1' s2_orig s2'
      | IOpIm i ->
        let s1' = S.instr_write_output_implicit i v1 s1_orig s1 in
        let s2' = S.instr_write_output_implicit i v2 s2_orig s2 in
        lemma_instr_write_outputs_ok outs args vs1 (coerce oprs) s1_orig s1';
        lemma_instr_write_outputs_ok outs args vs2 (coerce oprs) s2_orig s2';
        let ts' = instr_set_taint_implicit i ts t_out in
        lemma_instr_set_taints_implicit i v1 v2 ts_orig ts t_out s1_orig s1 s2_orig s2;
        lemma_instr_set_taints outs args vs1 vs2 (coerce oprs) ts_orig ts' t_out s1_orig s1' s2_orig s2'
    )

let check_if_instr_consumes_fixed_time (ins:S.ins) (ts:analysis_taints) : Pure (bool & analysis_taints)
  (requires BC.Instr? ins)
  (ensures ins_consumes_fixed_time ins ts)
  =
  let BC.Instr (InstrTypeRecord #outs #args #havoc_flags iins) oprs _ = ins in
  let t = inouts_taint outs args oprs ts in
  let b = check_if_consumes_fixed_time_outs outs args oprs ts t in
  let AnalysisTaints (LeakageTaints rs flags cf ovf) rts = ts in
  let flags = match havoc_flags with | HavocFlags -> Secret | PreserveFlags -> flags in
  let cf = match havoc_flags with | HavocFlags -> Secret | PreserveFlags -> cf in
  let ovf = match havoc_flags with | HavocFlags -> Secret | PreserveFlags -> ovf in
  let ts = AnalysisTaints (LeakageTaints rs flags cf ovf) rts in
  (b, instr_set_taints outs args oprs ts t)

let coerce_to_normal (#a:Type0) (x:a) : y:(normal a){x == y} = x

let check_if_xor_consumes_fixed_time (ins:S.ins) (ts:analysis_taints) : Pure (bool & analysis_taints)
  (requires BC.Instr? ins /\ S.AnnotateXor64? (BC.Instr?.annotation ins))
  (ensures ins_consumes_fixed_time ins ts)
  =
  let BC.Instr (InstrTypeRecord #outs #args #havoc_flags iins) oprs (S.AnnotateXor64 eq) = ins in
  let oprs:normal (instr_operands_t [inOut op64; out opFlagsCf; out opFlagsOf] [op64]) =
    coerce_to_normal #(instr_operands_t [inOut op64; out opFlagsCf; out opFlagsOf] [op64]) oprs in
  let (o1, (o2, ())) = oprs in
  if o1 = o2 then
    let t = Public in
    let b = check_if_consumes_fixed_time_outs outs args oprs ts t in
    let AnalysisTaints (LeakageTaints rs _ _ _) rts = ts in
    let ts = AnalysisTaints (LeakageTaints rs Secret Public Public) rts in
    (b, instr_set_taints outs args oprs ts t)
  else
    check_if_instr_consumes_fixed_time ins ts

let check_if_pxor_consumes_fixed_time (ins:S.ins) (ts:analysis_taints) : Pure (bool & analysis_taints)
  (requires BC.Instr? ins /\ S.AnnotatePxor? (BC.Instr?.annotation ins))
  (ensures ins_consumes_fixed_time ins ts)
  =
  let BC.Instr (InstrTypeRecord #outs #args #havoc_flags iins) oprs (S.AnnotatePxor eq) = ins in
  let oprs:normal (instr_operands_t [inOut opXmm] [opXmm]) =
    coerce_to_normal #(instr_operands_t [inOut opXmm] [opXmm]) oprs in
  let (o1, (o2, ())) = oprs in
  if o1 = o2 then
    let t = Public in
    let b = check_if_consumes_fixed_time_outs outs args oprs ts t in
    let AnalysisTaints (LeakageTaints rs ft cft oft) rts = ts in
    let ts = AnalysisTaints (LeakageTaints rs ft cft oft) rts in
    (b, instr_set_taints outs args oprs ts t)
  else
    check_if_instr_consumes_fixed_time ins ts

let check_if_vpxor_consumes_fixed_time (ins:S.ins) (ts:analysis_taints) : Pure (bool & analysis_taints)
  (requires BC.Instr? ins /\ S.AnnotateVPxor? (BC.Instr?.annotation ins))
  (ensures ins_consumes_fixed_time ins ts)
  =
  let BC.Instr (InstrTypeRecord #outs #args #havoc_flags iins) oprs (S.AnnotateVPxor eq) = ins in
  let oprs:normal (instr_operands_t [out opXmm] [opXmm; opXmm]) =
    coerce_to_normal #(instr_operands_t [out opXmm] [opXmm; opXmm]) oprs in
  let (_, (o2, (o3, ()))) = oprs in
  if o2 = o3 then
    let t = Public in
    let b = check_if_consumes_fixed_time_outs outs args oprs ts t in
    let AnalysisTaints (LeakageTaints rs ft cft oft) rts = ts in
    let ts = AnalysisTaints (LeakageTaints rs ft cft oft) rts in
    (b, instr_set_taints outs args oprs ts t)
  else
    check_if_instr_consumes_fixed_time ins ts

let check_if_alloc_consumes_fixed_time (ins:S.ins) (ts:analysis_taints) : Pure (bool & analysis_taints)
  (requires BC.Alloc? ins)
  (ensures ins_consumes_fixed_time ins ts)
  =
  (true, ts)

let check_if_dealloc_consumes_fixed_time (ins:S.ins) (ts:analysis_taints) : Pure (bool & analysis_taints)
  (requires BC.Dealloc? ins)
  (ensures ins_consumes_fixed_time ins ts)
  =
  (true, ts)

#reset-options "--initial_ifuel 3 --max_ifuel 3 --initial_fuel 4 --max_fuel 4 --z3rlimit 80"

let check_if_push_consumes_fixed_time (ins:S.ins) (ts:analysis_taints) : Pure (bool & analysis_taints)
  (requires BC.Push? ins)
  (ensures ins_consumes_fixed_time ins ts)
  =
  let BC.Push src t_stk = ins in
  let t_out = operand_taint 0 src ts in
  (Public? (Vale.Lib.MapTree.sel ts.rts reg_Rsp) && operand_does_not_use_secrets src ts && (t_out = Public || t_stk = Secret), ts)

let check_if_pop_consumes_fixed_time (ins:S.ins) (ts:analysis_taints) : Pure (bool & analysis_taints)
  (requires BC.Pop? ins)
  (ensures ins_consumes_fixed_time ins ts)
  =
  let BC.Pop dst t_stk = ins in
  let allowed = operand_taint_allowed dst t_stk in
  (Public? (Vale.Lib.MapTree.sel ts.rts reg_Rsp) && operand_does_not_use_secrets dst ts && allowed, set_taint 0 dst ts t_stk)

let check_if_ins_consumes_fixed_time ins ts =
  match ins with
  | BC.Instr _ _ (S.AnnotateXor64 _) -> check_if_xor_consumes_fixed_time ins ts
  | BC.Instr _ _ (S.AnnotatePxor _) -> check_if_pxor_consumes_fixed_time ins ts
  | BC.Instr _ _ (S.AnnotateVPxor _) -> check_if_vpxor_consumes_fixed_time ins ts
  | BC.Instr _ _ _ -> check_if_instr_consumes_fixed_time ins ts
  | BC.Push _ _ -> check_if_push_consumes_fixed_time ins ts
  | BC.Pop _ _ -> check_if_pop_consumes_fixed_time ins ts
  | BC.Alloc _ -> check_if_alloc_consumes_fixed_time ins ts
  | BC.Dealloc _ -> check_if_dealloc_consumes_fixed_time ins ts

#reset-options "--initial_ifuel 1 --max_ifuel 1 --initial_fuel 1 --max_fuel 1 --z3rlimit 100"
let lemma_instr_leakage_free (ts:analysis_taints) (ins:S.ins) : Lemma
  (requires BC.Instr? ins)
  (ensures (
    let (b, ts') = check_if_instr_consumes_fixed_time ins ts in
    b2t b ==> isConstantTime (Ins ins) ts.lts /\ isLeakageFree (Ins ins) ts.lts ts'.lts
  ))
  =
  let (b, ts') = check_if_instr_consumes_fixed_time ins ts in
  if b then
  (
    let code = Ins ins in
    let lem (s1 s2:S.machine_state) (fuel:nat) : Lemma
      (requires is_explicit_leakage_free_lhs code fuel ts.lts ts'.lts s1 s2)
      (ensures is_explicit_leakage_free_rhs code fuel ts.lts ts'.lts s1 s2)
      [SMTPat (is_explicit_leakage_free_rhs code fuel ts.lts ts'.lts s1 s2)]
      =
      let BC.Instr (InstrTypeRecord #outs #args #havoc_flags i) oprs _ = ins in
      let t_out = inouts_taint outs args oprs ts in
      let s1 = {s1 with S.ms_trace = []} in
      let s2 = {s2 with S.ms_trace = []} in
      let Some vs1 = S.instr_apply_eval outs args (instr_eval i) oprs s1 in
      let Some vs2 = S.instr_apply_eval outs args (instr_eval i) oprs s2 in
      let s1' =
        match havoc_flags with
        | HavocFlags -> {s1 with S.ms_flags = S.havoc_flags}
        | PreserveFlags -> s1
        in
      let s2' =
        match havoc_flags with
        | HavocFlags -> {s2 with S.ms_flags = S.havoc_flags}
        | PreserveFlags -> s2
        in
      let AnalysisTaints (LeakageTaints rs flags cf ovf) rts = ts in
      let flags = match havoc_flags with | HavocFlags -> Secret | PreserveFlags -> flags in
      let cf = match havoc_flags with | HavocFlags -> Secret | PreserveFlags -> cf in
      let ovf = match havoc_flags with | HavocFlags -> Secret | PreserveFlags -> ovf in
      let ts_havoc = AnalysisTaints (LeakageTaints rs flags cf ovf) rts in

      if t_out = Secret then
      (
        lemma_instr_set_taints outs args vs1 vs2 oprs ts ts_havoc t_out s1 s1' s2 s2';
        ()
      )
      else
      (
        let vs = vs1 in
        lemma_inouts_taint outs outs args (instr_eval i) oprs ts s1 s2;
        lemma_instr_set_taints outs args vs vs oprs ts ts_havoc t_out s1 s1' s2 s2';
        ()
      )
      in
    // assert (isExplicitLeakageFree (Ins ins) ts ts');
    ()
  )

let lemma_dealloc_leakage_free (ts:analysis_taints) (ins:S.ins) : Lemma
  (requires BC.Dealloc? ins)
  (ensures (
    let (b, ts') = check_if_dealloc_consumes_fixed_time ins ts in
    b2t b ==> isConstantTime (Ins ins) ts.lts /\ isLeakageFree (Ins ins) ts.lts ts'.lts
  ))
  =
  let (b, ts') = check_if_dealloc_consumes_fixed_time ins ts in
  if b then
  (
    let code = Ins ins in
    let lem (s1 s2:S.machine_state) (fuel:nat) : Lemma
      (requires is_explicit_leakage_free_lhs code fuel ts.lts ts'.lts s1 s2)
      (ensures is_explicit_leakage_free_rhs code fuel ts.lts ts'.lts s1 s2)
      [SMTPat (is_explicit_leakage_free_rhs code fuel ts.lts ts'.lts s1 s2)]
      =
      let BC.Dealloc n = ins in
      let s1' = Some?.v (machine_eval_code code fuel s1) in
      let s2' = Some?.v (machine_eval_code code fuel s2) in
      let S.Machine_stack _ stack1 = s1.S.ms_stack in
      let S.Machine_stack _ stack2 = s2.S.ms_stack in
      let S.Machine_stack _ stack1' = s1'.S.ms_stack in
      let S.Machine_stack _ stack2' = s2'.S.ms_stack in
      let aux (x:int) : Lemma
        (requires publicStackValueIsSame stack1 stack2 s1.S.ms_stackTaint s2.S.ms_stackTaint x)
        (ensures publicStackValueIsSame stack1' stack2' s1'.S.ms_stackTaint s2'.S.ms_stackTaint x)
        =
        Classical.forall_intro (fun s -> Vale.Lib.Set.lemma_sel_restrict s stack1 x);
        Classical.forall_intro (fun s -> Vale.Lib.Set.lemma_sel_restrict s stack2 x)
      in Classical.forall_intro (Classical.move_requires aux)
    in
    ()
  )

let lemma_push_leakage_free (ts:analysis_taints) (ins:S.ins) : Lemma
  (requires BC.Push? ins)
  (ensures (
    let (b, ts') = check_if_push_consumes_fixed_time ins ts in
    b2t b ==> isConstantTime (Ins ins) ts.lts /\ isLeakageFree (Ins ins) ts.lts ts'.lts
  ))
  =
  let (b, ts') = check_if_push_consumes_fixed_time ins ts in
  if b then
  (
    let code = Ins ins in
    let lem (s1 s2:S.machine_state) (fuel:nat) : Lemma
      (requires is_explicit_leakage_free_lhs code fuel ts.lts ts'.lts s1 s2)
      (ensures is_explicit_leakage_free_rhs code fuel ts.lts ts'.lts s1 s2)
      [SMTPat (is_explicit_leakage_free_rhs code fuel ts.lts ts'.lts s1 s2)]
      =
      let BC.Push src t_stk = ins in
      let t_out = operand_taint 0 src ts in
      let s1' = Some?.v (machine_eval_code code fuel s1) in
      let s2' = Some?.v (machine_eval_code code fuel s2) in
      let S.Machine_stack _ stack1 = s1.S.ms_stack in
      let S.Machine_stack _ stack2 = s2.S.ms_stack in
      let S.Machine_stack _ stack1' = s1'.S.ms_stack in
      let S.Machine_stack _ stack2' = s2'.S.ms_stack in
      let ptr1 = S.eval_reg_64 rRsp s1 - 8 in
      let ptr2 = S.eval_reg_64 rRsp s2 - 8 in
      let v1 = S.eval_operand src s1 in
      let v2 = S.eval_operand src s2 in
      assert (ptr1 == ptr2);
      if t_out = Secret then ()
      else (
        let aux () : Lemma  (v1 == v2)
          = match src with
          | OConst _ | OReg _ -> ()
          | OMem (_, _) | OStack (_, _) -> S.get_heap_val64_reveal ()
        in
        aux()
      )
    in
    ()
  )

#reset-options "--initial_ifuel 1 --max_ifuel 1 --initial_fuel 1 --max_fuel 1 --z3rlimit 100"
let lemma_pop_leakage_free (ts:analysis_taints) (ins:S.ins) : Lemma
  (requires BC.Pop? ins)
  (ensures (
    let (b, ts') = check_if_pop_consumes_fixed_time ins ts in
    b2t b ==> isConstantTime (Ins ins) ts.lts /\ isLeakageFree (Ins ins) ts.lts ts'.lts
  ))
  =
  let (b, ts') = check_if_pop_consumes_fixed_time ins ts in
  if b then
  (
    let code = Ins ins in
    let lem (s1 s2:S.machine_state) (fuel:nat) : Lemma
      (requires is_explicit_leakage_free_lhs code fuel ts.lts ts'.lts s1 s2)
      (ensures is_explicit_leakage_free_rhs code fuel ts.lts ts'.lts s1 s2)
      [SMTPat (is_explicit_leakage_free_rhs code fuel ts.lts ts'.lts s1 s2)]
      =
      allow_inversion maddr;
      allow_inversion tmaddr;
      let BC.Pop dst t_stk = ins in
      let s1' = Some?.v (machine_eval_code code fuel s1) in
      let s2' = Some?.v (machine_eval_code code fuel s2) in
      let stack_op = OStack (MReg reg_Rsp 0, Public) in
      let v1 = S.eval_operand stack_op s1 in
      let v2 = S.eval_operand stack_op s2 in
      if t_stk = Public then (
        S.get_heap_val64_reveal ();
        assert (v1 == v2)
      );
      Classical.forall_intro_3 (fun s x (stack1:S.machine_heap) -> Vale.Lib.Set.lemma_sel_restrict s stack1 x);
      Classical.forall_intro_3 (fun s x (stack2:S.machine_heap) -> Vale.Lib.Set.lemma_sel_restrict s stack2 x)
      in
    ()
  )

#reset-options "--initial_ifuel 2 --max_ifuel 2 --initial_fuel 4 --max_fuel 4 --z3rlimit 40"
let lemma_xor_leakage_free (ts:analysis_taints) (ins:S.ins) : Lemma
  (requires BC.Instr? ins /\ S.AnnotateXor64? (BC.Instr?.annotation ins))
  (ensures (
    let (b, ts') = check_if_xor_consumes_fixed_time ins ts in
    b2t b ==> isConstantTime (Ins ins) ts.lts /\ isLeakageFree (Ins ins) ts.lts ts'.lts
  ))
  =
  let BC.Instr (InstrTypeRecord #outs #args #havoc_flags iins) oprs (S.AnnotateXor64 eq) = ins in
  let oprs:normal (instr_operands_t [inOut op64; out opFlagsCf; out opFlagsOf] [op64]) =
    coerce_to_normal #(instr_operands_t [inOut op64; out opFlagsCf; out opFlagsOf] [op64]) oprs in
  let (o1, (o2, ())) = oprs in
  if o1 = o2 then
    FStar.Classical.forall_intro_with_pat (fun n -> Vale.Def.Types_s.ixor n n) Vale.Arch.Types.lemma_BitwiseXorCancel64
  else
    lemma_instr_leakage_free ts ins

let lemma_pxor_leakage_free (ts:analysis_taints) (ins:S.ins) : Lemma
  (requires BC.Instr? ins /\ S.AnnotatePxor? (BC.Instr?.annotation ins))
  (ensures (
    let (b, ts') = check_if_pxor_consumes_fixed_time ins ts in
    b2t b ==> isConstantTime (Ins ins) ts.lts /\ isLeakageFree (Ins ins) ts.lts ts'.lts
  ))
  =
  let BC.Instr (InstrTypeRecord #outs #args #havoc_flags iins) oprs (S.AnnotatePxor eq) = ins in
  let oprs:normal (instr_operands_t [inOut opXmm] [opXmm]) =
    coerce_to_normal #(instr_operands_t [inOut opXmm] [opXmm]) oprs in
  let (o1, (o2, ())) = oprs in
  if o1 = o2 then
    Vale.Arch.Types.lemma_quad32_xor()
  else
    lemma_instr_leakage_free ts ins

let lemma_vpxor_leakage_free (ts:analysis_taints) (ins:S.ins) : Lemma
  (requires BC.Instr? ins /\ S.AnnotateVPxor? (BC.Instr?.annotation ins))
  (ensures (
    let (b, ts') = check_if_vpxor_consumes_fixed_time ins ts in
    b2t b ==> isConstantTime (Ins ins) ts.lts /\ isLeakageFree (Ins ins) ts.lts ts'.lts
  ))
  =
  let BC.Instr (InstrTypeRecord #outs #args #havoc_flags iins) oprs (S.AnnotateVPxor eq) = ins in
  let oprs:normal (instr_operands_t [out opXmm] [opXmm; opXmm]) =
    coerce_to_normal #(instr_operands_t [out opXmm] [opXmm; opXmm]) oprs in
  let (_, (o1, (o2, ()))) = oprs in
  if o1 = o2 then
    Vale.Arch.Types.lemma_quad32_xor()
  else
    lemma_instr_leakage_free ts ins

#reset-options "--initial_ifuel 1 --max_ifuel 1 --initial_fuel 1 --max_fuel 1 --z3rlimit 20"

let lemma_ins_leakage_free ts ins =
  let (b, ts') = check_if_ins_consumes_fixed_time ins ts in
  match ins with
  | BC.Instr _ _ (S.AnnotateXor64 _) -> lemma_xor_leakage_free ts ins
  | BC.Instr _ _ (S.AnnotatePxor _) -> lemma_pxor_leakage_free ts ins
  | BC.Instr _ _ (S.AnnotateVPxor _) -> lemma_vpxor_leakage_free ts ins  
  | BC.Instr _ _ _ -> lemma_instr_leakage_free ts ins
  | BC.Alloc _ -> ()
  | BC.Dealloc _ -> lemma_dealloc_leakage_free ts ins
  | BC.Push _ _ -> lemma_push_leakage_free ts ins
  | BC.Pop _ _ -> lemma_pop_leakage_free ts ins
