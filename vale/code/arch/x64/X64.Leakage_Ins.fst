module X64.Leakage_Ins
open X64.Machine_s
open X64.Memory_s
open X64.Semantics_s
module S = X64.Bytes_Semantics_s
open X64.Taint_Semantics_s
open X64.Leakage_s
open X64.Leakage_Helpers

let rec has_mem_operand = function
  | [] -> false
  | a::q -> if OMem? a then true else has_mem_operand q

#reset-options "--initial_ifuel 2 --max_ifuel 2 --initial_fuel 4 --max_fuel 4 --z3rlimit 80"

let check_if_ins_consumes_fixed_time ins ts =
  let i, dsts, srcs = ins.ops in
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
  let taint = if S.AddCarry64? i || S.Adcx64? i then merge_taint taint ts.cfFlagsTaint else taint in
  if has_mem_operand dsts && taint <> ins.t then false, ts
  else
  let ts' = set_taints dsts ts taint in
  let b, ts' = match i with
    | S.Mov64 dst _ | S.AddLea64 dst _ _ -> begin
      match dst with
        | OConst _ -> false, ts (* Should not happen *)
        | OReg r -> fixedTime, ts'
        | OMem m -> fixedTime, ts'
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
        end
   | S.Push src -> if Secret? (ts'.regTaint Rsp) || Secret? (operand_taint src ts' Public) then false, ts
     else fixedTime, ts'
   | S.Pop dst -> if Secret? (ts'.regTaint Rsp) then false, ts else fixedTime, ts'
   | S.Adox64 _ _ -> false, ts (* Unhandled yet *)
   | S.Add64 _ _ | S.AddCarry64 _ _ | S.Adcx64 _ _  -> begin
          match dsts with
        | [OConst _] -> true, (TaintState ts'.regTaint Secret taint ts'.xmmTaint) (* Should not happen *)
        | [OReg r] -> fixedTime, (TaintState ts'.regTaint Secret taint ts'.xmmTaint)
        | [OMem m] -> fixedTime, (TaintState ts'.regTaint Secret taint ts'.xmmTaint)
    end
    | _ ->
      match dsts with
            | [OConst _] -> false, (TaintState ts'.regTaint Secret Secret ts'.xmmTaint) (* Should not happen *)
            | [OReg r] -> fixedTime, (TaintState ts'.regTaint Secret Secret ts'.xmmTaint)
            | [OMem m] ->  fixedTime, (TaintState ts'.regTaint Secret Secret ts'.xmmTaint)
  in
  b, ts'

val lemma_public_flags_same: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in S.Mul64? i}) -> Lemma (forall s1 s2.
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  b2t b ==>
publicFlagValuesAreSame ts s1 s2 ==> publicFlagValuesAreSame (snd (check_if_ins_consumes_fixed_time ins ts)) (taint_eval_ins ins s1) (taint_eval_ins ins s2))

let lemma_public_flags_same ts ins = ()

val lemma_push_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in S.Push? i}) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

#reset-options "--initial_ifuel 2 --max_ifuel 2 --initial_fuel 4 --max_fuel 4 --z3rlimit 80"

let lemma_push_same_public ts ins s1 s2 fuel =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let S.Push src, _, _ = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  let ptr1 = ((eval_reg Rsp s1.state) - 8) % pow2_64 in
  let ptr2 = ((eval_reg Rsp s2.state) - 8) % pow2_64 in
  let v1 = eval_operand src s1.state in
  let v2 = eval_operand src s2.state in
  if not (valid_mem64 ptr1 s1.state.mem) || not (valid_mem64 ptr2 s2.state.mem) || Secret? (ts.regTaint Rsp) then ()
  else begin
  lemma_store_load_mem64 ptr1 v1 s1.state.mem;
  lemma_store_load_mem64 ptr2 v2 s2.state.mem;
  lemma_valid_store_mem64 ptr1 v1 s1.state.mem;
  lemma_valid_store_mem64 ptr2 v2 s2.state.mem;
  lemma_frame_store_mem64 ptr1 v1 s1.state.mem;
  lemma_frame_store_mem64 ptr2 v2 s2.state.mem
  end

val lemma_pop_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in S.Pop? i}) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

#reset-options "--initial_ifuel 2 --max_ifuel 2 --initial_fuel 4 --max_fuel 4 --z3rlimit 80"

let lemma_pop_same_public ts ins s1 s2 fuel =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let S.Pop dst, _, _ = ins.ops in
  let op = OMem (MReg Rsp 0) in
  let v1 = eval_operand op s1.state in
  let v2 = eval_operand op s2.state in
  match dst with
  | OConst _ -> ()
  | OReg _ -> ()
  | OMem m ->
    let ptr1 = eval_maddr m s1.state in
    let ptr2 = eval_maddr m s2.state in
    if not (valid_mem64 ptr1 s1.state.mem) || not (valid_mem64 ptr2 s2.state.mem) || Secret?   (ts.regTaint Rsp) then ()
    else begin
    lemma_store_load_mem64 ptr1 v1 s1.state.mem;
    lemma_store_load_mem64 ptr2 v2 s2.state.mem;
    lemma_valid_store_mem64 ptr1 v1 s1.state.mem;
    lemma_valid_store_mem64 ptr2 v2 s2.state.mem;
    lemma_frame_store_mem64 ptr1 v1 s1.state.mem;
    lemma_frame_store_mem64 ptr2 v2 s2.state.mem
    end


val lemma_mov_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in S.Mov64? i}) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

let lemma_mov_same_public ts ins s1 s2 fuel =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  match dsts with
    | [OConst _] -> ()
    | [OReg _] ->  ()
    | [OMem m] ->
      let ptr1 = eval_maddr m s1.state in
      let ptr2 = eval_maddr m s2.state in
      match srcs with
        | [src] ->
          let v1 = eval_operand src s1.state in
          let v2 = eval_operand src s2.state in
          if not (valid_mem64 ptr1 s1.state.mem) || not (valid_mem64 ptr2 s2.state.mem) then ()
          else begin
          lemma_store_load_mem64 ptr1 v1 s1.state.mem;
          lemma_store_load_mem64 ptr2 v2 s2.state.mem;
          lemma_valid_store_mem64 ptr1 v1 s1.state.mem;
          lemma_valid_store_mem64 ptr2 v2 s2.state.mem;
          lemma_frame_store_mem64 ptr1 v1 s1.state.mem;
          lemma_frame_store_mem64 ptr2 v2 s2.state.mem
          end

val lemma_add_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in S.Add64? i}) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

#reset-options "--initial_ifuel 2 --max_ifuel 2 --initial_fuel 4 --max_fuel 4 --z3rlimit 100"
let lemma_add_same_public ts ins s1 s2 fuel =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  match dsts with
    | [OConst _] -> ()
    | [OReg _] ->  ()
    | [OMem m] ->
      let ptr1 = eval_maddr m s1.state in
      let ptr2 = eval_maddr m s2.state in
      match srcs with
        | [src1; src2] ->
          let v11 = eval_operand src1 s1.state in
          let v12 = eval_operand src2 s1.state in
          let v21 = eval_operand src1 s2.state in
          let v22 = eval_operand src2 s2.state in
          let v1 = (v11 + v12) % pow2_64 in
          let v2 = (v21 + v22) % pow2_64 in
          if not (valid_mem64 ptr1 s1.state.mem) || not (valid_mem64 ptr2 s2.state.mem) then ()
          else begin
           lemma_store_load_mem64 ptr1 v1 s1.state.mem;
          lemma_store_load_mem64 ptr2 v2 s2.state.mem;
          lemma_valid_store_mem64 ptr1 v1 s1.state.mem;
          lemma_valid_store_mem64 ptr2 v2 s2.state.mem;
          lemma_frame_store_mem64 ptr1 v1 s1.state.mem;
          lemma_frame_store_mem64 ptr2 v2 s2.state.mem
          end


val lemma_mulx_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in S.Mulx64? i}) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

let lemma_mulx_same_public ts ins s1 s2 fuel =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  match dsts with
    | [OMem m1; OMem m2] ->
      let ptr1_hi = eval_maddr m1 s1.state in
      let ptr2_hi = eval_maddr m1 s2.state in
      let ptr1_lo = eval_maddr m2 s1.state in
      let ptr2_lo = eval_maddr m2 s2.state in
      begin match srcs with
      | [src1; src2] ->
      let v11 = eval_operand src1 s1.state in
      let v12 = eval_operand src2 s1.state in
      let v21 = eval_operand src1 s2.state in
      let v22 = eval_operand src2 s2.state in
      let v1_hi = FStar.UInt.mul_div #64 v11 v12 in
      let v1_lo = FStar.UInt.mul_mod #64 v11 v12 in
      let v2_hi = FStar.UInt.mul_div #64 v21 v22 in
      let v2_lo = FStar.UInt.mul_mod #64 v21 v22 in
      let s1' = update_operand_preserve_flags' (OMem m2) v1_lo s1.state in
      let s2' = update_operand_preserve_flags' (OMem m2) v2_lo s2.state in
      if not (valid_mem64 ptr1_hi s1'.mem) || not (valid_mem64 ptr2_hi s2'.mem)
        || not (valid_mem64 ptr1_lo s1.state.mem) || not (valid_mem64 ptr2_lo s2.state.mem) then ()
      else begin
      lemma_store_load_mem64 ptr1_hi v1_hi s1'.mem;
      lemma_store_load_mem64 ptr2_hi v2_hi s2'.mem;
      lemma_valid_store_mem64 ptr1_hi v1_hi s1'.mem;
      lemma_valid_store_mem64 ptr2_hi v2_hi s2'.mem;
      lemma_frame_store_mem64 ptr1_hi v1_hi s1'.mem;
      lemma_frame_store_mem64 ptr2_hi v2_hi s2'.mem;
      lemma_store_load_mem64 ptr1_lo v1_lo s1.state.mem;
      lemma_store_load_mem64 ptr2_lo v2_lo s2.state.mem;
      lemma_valid_store_mem64 ptr1_lo v1_lo s1.state.mem;
      lemma_valid_store_mem64 ptr2_lo v2_lo s2.state.mem;
      lemma_frame_store_mem64 ptr1_lo v1_lo s1.state.mem;
      lemma_frame_store_mem64 ptr2_lo v2_lo s2.state.mem;
      assert (b2t b ==> publicValuesAreSame ts s1 s2 /\ r1.state.X64.Memory_s.state.S.ok /\ r2.state.X64.Memory_s.state.S.ok /\ Public? ins.t ==> v1_hi == v2_hi);
      ()
      end
      end
    | [OMem m1; o] ->
      begin match srcs with
      | [src1; src2] ->
      let v11 = eval_operand src1 s1.state in
      let v12 = eval_operand src2 s1.state in
      let v21 = eval_operand src1 s2.state in
      let v22 = eval_operand src2 s2.state in
      let v1_hi = FStar.UInt.mul_div #64 v11 v12 in
      let v1_lo = FStar.UInt.mul_mod #64 v11 v12 in
      let v2_hi = FStar.UInt.mul_div #64 v21 v22 in
      let v2_lo = FStar.UInt.mul_mod #64 v21 v22 in
      let s1' = update_operand_preserve_flags' o v1_lo s1.state in
      let s2' = update_operand_preserve_flags' o v2_lo s2.state in
      let ptr1_hi = eval_maddr m1 s1' in
      let ptr2_hi = eval_maddr m1 s2' in
      if not (valid_mem64 ptr1_hi s1.state.mem) || not (valid_mem64 ptr2_hi s2.state.mem) then ()
      else begin
      lemma_store_load_mem64 ptr1_hi v1_hi s1'.mem;
      lemma_store_load_mem64 ptr2_hi v2_hi s2'.mem;
      lemma_valid_store_mem64 ptr1_hi v1_hi s1'.mem;
      lemma_valid_store_mem64 ptr2_hi v2_hi s2'.mem;
      lemma_frame_store_mem64 ptr1_hi v1_hi s1'.mem;
      lemma_frame_store_mem64 ptr2_hi v2_hi s2'.mem
      end
      end
    | [o; OMem m2] ->
      begin match srcs with
      | [src1; src2] ->
      let v11 = eval_operand src1 s1.state in
      let v12 = eval_operand src2 s1.state in
      let v21 = eval_operand src1 s2.state in
      let v22 = eval_operand src2 s2.state in
      let v1_hi = FStar.UInt.mul_div #64 v11 v12 in
      let v1_lo = FStar.UInt.mul_mod #64 v11 v12 in
      let v2_hi = FStar.UInt.mul_div #64 v21 v22 in
      let v2_lo = FStar.UInt.mul_mod #64 v21 v22 in
      let ptr1_lo = eval_maddr m2 s1.state in
      let ptr2_lo = eval_maddr m2 s2.state in
      if not (valid_mem64 ptr1_lo s1.state.mem) || not (valid_mem64 ptr2_lo s2.state.mem) then ()
      else begin
      lemma_store_load_mem64 ptr1_lo v1_lo s1.state.mem;
      lemma_store_load_mem64 ptr2_lo v2_lo s2.state.mem;
      lemma_valid_store_mem64 ptr1_lo v1_lo s1.state.mem;
      lemma_valid_store_mem64 ptr2_lo v2_lo s2.state.mem;
      lemma_frame_store_mem64 ptr1_lo v1_lo s1.state.mem;
      lemma_frame_store_mem64 ptr2_lo v2_lo s2.state.mem
      end
      end
    | _ -> ()

val lemma_sub_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in S.Sub64? i}) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

let lemma_sub_same_public ts ins s1 s2 fuel =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
 match dsts with
    | [OConst _] -> ()
    | [OReg _] ->  ()
    | [OMem m] ->
      let ptr1 = eval_maddr m s1.state in
      let ptr2 = eval_maddr m s2.state in
      match srcs with
        | [src1; src2] ->
          let v11 = eval_operand src1 s1.state in
          let v12 = eval_operand src2 s1.state in
          let v21 = eval_operand src1 s2.state in
          let v22 = eval_operand src2 s2.state in
          let v1 = (v11 - v12) % pow2_64 in
          let v2 = (v21 - v22) % pow2_64 in
          if not (valid_mem64 ptr1 s1.state.mem) || not (valid_mem64 ptr2 s2.state.mem) then ()
          else begin
           lemma_store_load_mem64 ptr1 v1 s1.state.mem;
          lemma_store_load_mem64 ptr2 v2 s2.state.mem;
          lemma_valid_store_mem64 ptr1 v1 s1.state.mem;
          lemma_valid_store_mem64 ptr2 v2 s2.state.mem;
          lemma_frame_store_mem64 ptr1 v1 s1.state.mem;
          lemma_frame_store_mem64 ptr2 v2 s2.state.mem
          end

val lemma_imul_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in S.IMul64? i}) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

let lemma_imul_same_public ts ins s1 s2 fuel =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
 match dsts with
    | [OConst _] -> ()
    | [OReg _] ->  ()
    | [OMem m] ->
      let ptr1 = eval_maddr m s1.state in
      let ptr2 = eval_maddr m s2.state in
      match srcs with
        | [src1; src2] ->
          let v11 = eval_operand src1 s1.state in
          let v12 = eval_operand src2 s1.state in
          let v21 = eval_operand src1 s2.state in
          let v22 = eval_operand src2 s2.state in
          let v1 = FStar.UInt.mul_mod #64 v11 v12 in
          let v2 = FStar.UInt.mul_mod #64 v21 v22 in
          if not (valid_mem64 ptr1 s1.state.mem) || not (valid_mem64 ptr2 s2.state.mem) then ()
          else begin
           lemma_store_load_mem64 ptr1 v1 s1.state.mem;
          lemma_store_load_mem64 ptr2 v2 s2.state.mem;
          lemma_valid_store_mem64 ptr1 v1 s1.state.mem;
          lemma_valid_store_mem64 ptr2 v2 s2.state.mem;
          lemma_frame_store_mem64 ptr1 v1 s1.state.mem;
          lemma_frame_store_mem64 ptr2 v2 s2.state.mem
          end

val lemma_and_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in S.And64? i}) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

let lemma_and_same_public ts ins s1 s2 fuel =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  match dsts with
    | [OConst _] -> ()
    | [OReg _] ->  ()
    | [OMem m] ->
      let ptr1 = eval_maddr m s1.state in
      let ptr2 = eval_maddr m s2.state in
      match srcs with
        | [src1; src2] ->
          let v11 = eval_operand src1 s1.state in
          let v12 = eval_operand src2 s1.state in
          let v21 = eval_operand src1 s2.state in
          let v22 = eval_operand src2 s2.state in
          let v1 = Types_s.iand v11 v12 in
          let v2 = Types_s.iand v21 v22 in
          if not (valid_mem64 ptr1 s1.state.mem) || not (valid_mem64 ptr2 s2.state.mem) then ()
          else begin
           lemma_store_load_mem64 ptr1 v1 s1.state.mem;
          lemma_store_load_mem64 ptr2 v2 s2.state.mem;
          lemma_valid_store_mem64 ptr1 v1 s1.state.mem;
          lemma_valid_store_mem64 ptr2 v2 s2.state.mem;
          lemma_frame_store_mem64 ptr1 v1 s1.state.mem;
          lemma_frame_store_mem64 ptr2 v2 s2.state.mem
          end

val lemma_addlea_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in S.AddLea64? i}) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

let lemma_addlea_same_public ts ins s1 s2 fuel =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  match dsts with
    | [OConst _] -> ()
    | [OReg _] ->  ()
    | [OMem m] ->
      let ptr1 = eval_maddr m s1.state in
      let ptr2 = eval_maddr m s2.state in
      match srcs with
        | [dst; src1; src2] ->
          let v11 = eval_operand src1 s1.state in
          let v12 = eval_operand src2 s1.state in
          let v21 = eval_operand src1 s2.state in
          let v22 = eval_operand src2 s2.state in
          let v1 = (v11 + v12) % pow2_64 in
          let v2 = (v21 + v22) % pow2_64 in
          if not (valid_mem64 ptr1 s1.state.mem) || not (valid_mem64 ptr2 s2.state.mem) then ()
          else begin
           lemma_store_load_mem64 ptr1 v1 s1.state.mem;
          lemma_store_load_mem64 ptr2 v2 s2.state.mem;
          lemma_valid_store_mem64 ptr1 v1 s1.state.mem;
          lemma_valid_store_mem64 ptr2 v2 s2.state.mem;
          lemma_frame_store_mem64 ptr1 v1 s1.state.mem;
          lemma_frame_store_mem64 ptr2 v2 s2.state.mem
          end

val lemma_addcarry_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in S.AddCarry64? i}) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

let lemma_addcarry_same_public ts ins s1 s2 fuel =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  match dsts with
    | [OConst _] -> ()
    | [OReg _] ->  ()
    | [OMem m] ->
      let ptr1 = eval_maddr m s1.state in
      let ptr2 = eval_maddr m s2.state in
      match srcs with
        | [src1; src2] ->
          let c1 = if cf(s1.state.X64.Memory_s.state.S.flags) then 1 else 0 in
          let c2 = if cf(s2.state.X64.Memory_s.state.S.flags) then 1 else 0 in
          let v11 = eval_operand src1 s1.state in
          let v12 = eval_operand src2 s1.state in
          let v21 = eval_operand src1 s2.state in
          let v22 = eval_operand src2 s2.state in
          let v1 = (v11 + v12 + c1) % pow2_64 in
          let v2 = (v21 + v22 + c2) % pow2_64 in
          if not (valid_mem64 ptr1 s1.state.mem) || not (valid_mem64 ptr2 s2.state.mem) then ()
          else begin
           lemma_store_load_mem64 ptr1 v1 s1.state.mem;
          lemma_store_load_mem64 ptr2 v2 s2.state.mem;
          lemma_valid_store_mem64 ptr1 v1 s1.state.mem;
          lemma_valid_store_mem64 ptr2 v2 s2.state.mem;
          lemma_frame_store_mem64 ptr1 v1 s1.state.mem;
          lemma_frame_store_mem64 ptr2 v2 s2.state.mem
          end

val lemma_adcx_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in S.Adcx64? i}) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

#reset-options "--initial_ifuel 2 --max_ifuel 2 --initial_fuel 4 --max_fuel 4 --z3rlimit 200"

let lemma_adcx_same_public ts ins s1 s2 fuel =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  match dsts with
    | [OConst _] -> ()
    | [OReg _] ->  ()
    | [OMem m] ->
      let ptr1 = eval_maddr m s1.state in
      let ptr2 = eval_maddr m s2.state in
      match srcs with
        | [src1; src2] ->
          let c1 = if cf(s1.state.X64.Memory_s.state.S.flags) then 1 else 0 in
          let c2 = if cf(s2.state.X64.Memory_s.state.S.flags) then 1 else 0 in
          let v11 = eval_operand src1 s1.state in
          let v12 = eval_operand src2 s1.state in
          let v21 = eval_operand src1 s2.state in
          let v22 = eval_operand src2 s2.state in
          let v1 = (v11 + v12 + c1) % pow2_64 in
          let v2 = (v21 + v22 + c2) % pow2_64 in
          if not (valid_mem64 ptr1 s1.state.mem) || not (valid_mem64 ptr2 s2.state.mem) then ()
          else begin
           lemma_store_load_mem64 ptr1 v1 s1.state.mem;
          lemma_store_load_mem64 ptr2 v2 s2.state.mem;
          lemma_valid_store_mem64 ptr1 v1 s1.state.mem;
          lemma_valid_store_mem64 ptr2 v2 s2.state.mem;
          lemma_frame_store_mem64 ptr1 v1 s1.state.mem;
          lemma_frame_store_mem64 ptr2 v2 s2.state.mem
          end

val lemma_mul_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in S.Mul64? i}) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

let lemma_mul_same_public ts ins s1 s2 fuel = lemma_public_flags_same ts ins; ()

val lemma_shr_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in S.Shr64? i}) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

let lemma_shr_same_public ts ins s1 s2 fuel =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  match dsts with
    | [OConst _] -> ()
    | [OReg _] ->  ()
    | [OMem m] ->
      let ptr1 = eval_maddr m s1.state in
      let ptr2 = eval_maddr m s2.state in
      match srcs with
        | [src1; src2] ->
          let v11 = eval_operand src1 s1.state in
          let v12 = eval_operand src2 s1.state in
          let v21 = eval_operand src1 s2.state in
          let v22 = eval_operand src2 s2.state in
          let v1 = Types_s.ishr v11 v12 in
          let v2 = Types_s.ishr v21 v22 in
          if not (valid_mem64 ptr1 s1.state.mem) || not (valid_mem64 ptr2 s2.state.mem) then ()
          else begin
           lemma_store_load_mem64 ptr1 v1 s1.state.mem;
          lemma_store_load_mem64 ptr2 v2 s2.state.mem;
          lemma_valid_store_mem64 ptr1 v1 s1.state.mem;
          lemma_valid_store_mem64 ptr2 v2 s2.state.mem;
          lemma_frame_store_mem64 ptr1 v1 s1.state.mem;
          lemma_frame_store_mem64 ptr2 v2 s2.state.mem
          end

val lemma_shl_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in S.Shl64? i}) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

let lemma_shl_same_public ts ins s1 s2 fuel =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  match dsts with
    | [OConst _] -> ()
    | [OReg _] ->  ()
    | [OMem m] ->
      let ptr1 = eval_maddr m s1.state in
      let ptr2 = eval_maddr m s2.state in
      match srcs with
        | [src1; src2] ->
          let v11 = eval_operand src1 s1.state in
          let v12 = eval_operand src2 s1.state in
          let v21 = eval_operand src1 s2.state in
          let v22 = eval_operand src2 s2.state in
          let v1 = Types_s.ishl v11 v12 in
          let v2 = Types_s.ishl v21 v22 in
          if not (valid_mem64 ptr1 s1.state.mem) || not (valid_mem64 ptr2 s2.state.mem) then ()
          else begin
           lemma_store_load_mem64 ptr1 v1 s1.state.mem;
          lemma_store_load_mem64 ptr2 v2 s2.state.mem;
          lemma_valid_store_mem64 ptr1 v1 s1.state.mem;
          lemma_valid_store_mem64 ptr2 v2 s2.state.mem;
          lemma_frame_store_mem64 ptr1 v1 s1.state.mem;
          lemma_frame_store_mem64 ptr2 v2 s2.state.mem
          end

val lemma_xor_same_public: (ts:taintState) -> (ins:tainted_ins{let i, _, _ = ins.ops in S.Xor64? i}) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

val lemma_aux_xor: (x:nat64) -> Lemma (Types_s.ixor x x = 0)

let lemma_aux_xor x =
  TypesNative_s.reveal_ixor 64 x x;
  FStar.UInt.logxor_self #64 x

let lemma_xor_same_public ts ins s1 s2 fuel =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let i, dsts, srcs = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  Classical.forall_intro lemma_aux_xor;
  match dsts with
    | [OConst _] -> ()
    | [OReg _] -> ()
    | [OMem m] ->
      let ptr1 = eval_maddr m s1.state in
      let ptr2 = eval_maddr m s2.state in
      match srcs with
        | [src1; src2] ->
          let v11 = eval_operand src1 s1.state in
          let v12 = eval_operand src2 s1.state in
          let v21 = eval_operand src1 s2.state in
          let v22 = eval_operand src2 s2.state in
          let v1 = Types_s.ixor v11 v12 in
          let v2 = Types_s.ixor v21 v22 in
          if not (valid_mem64 ptr1 s1.state.mem) || not (valid_mem64 ptr2 s2.state.mem) then ()
          else begin
           lemma_store_load_mem64 ptr1 v1 s1.state.mem;
          lemma_store_load_mem64 ptr2 v2 s2.state.mem;
          lemma_valid_store_mem64 ptr1 v1 s1.state.mem;
          lemma_valid_store_mem64 ptr2 v2 s2.state.mem;
          lemma_frame_store_mem64 ptr1 v1 s1.state.mem;
          lemma_frame_store_mem64 ptr2 v2 s2.state.mem
          end

#reset-options "--initial_ifuel 2 --max_ifuel 2 --initial_fuel 4 --max_fuel 4 --z3rlimit 20"
val lemma_ins_same_public: (ts:taintState) -> (ins:tainted_ins{not (is_xmm_ins ins)}) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))

let lemma_ins_same_public ts ins s1 s2 fuel = let i, _, _ = ins.ops in
  match i with
  | S.Mov64 _ _ -> lemma_mov_same_public ts ins s1 s2 fuel
  | S.Add64 _ _ -> lemma_add_same_public ts ins s1 s2 fuel
  | S.AddLea64 _ _ _ -> lemma_addlea_same_public ts ins s1 s2 fuel
  | S.Sub64 _ _ -> lemma_sub_same_public ts ins s1 s2 fuel
  | S.IMul64 _ _ -> lemma_imul_same_public ts ins s1 s2 fuel
  | S.And64 _ _ -> lemma_and_same_public ts ins s1 s2 fuel
  | S.Mul64 _ -> lemma_mul_same_public ts ins s1 s2 fuel
  | S.Mulx64 _ _ _ -> lemma_mulx_same_public ts ins s1 s2 fuel
  | S.Xor64 _ _ -> lemma_xor_same_public ts ins s1 s2 fuel
  | S.AddCarry64 _ _ -> lemma_addcarry_same_public ts ins s1 s2 fuel
  | S.Adcx64 _ _ -> lemma_adcx_same_public ts ins s1 s2 fuel
  | S.Shl64 _ _ -> lemma_shl_same_public ts ins s1 s2 fuel
  | S.Shr64 _ _ -> lemma_shr_same_public ts ins s1 s2 fuel
  | S.Push _ -> lemma_push_same_public ts ins s1 s2 fuel
  | S.Pop _ -> lemma_pop_same_public ts ins s1 s2 fuel
  | S.Adox64 _ _ -> ()

let lemma_ins_leakage_free ts ins =
  let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  let p s1 s2 fuel = b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2 in
  let my_lemma s1 s2 fuel : Lemma(p s1 s2 fuel) = lemma_ins_same_public ts ins s1 s2 fuel in
  let open FStar.Classical in
  forall_intro_3 my_lemma
