module X64.Leakage_Ins_Xmm
open X64.Machine_s
open X64.Memory_s
open X64.Semantics_s
open X64.Taint_Semantics_s
module S = X64.Bytes_Semantics_s
open X64.Leakage_s
open X64.Leakage_Helpers
open Types_s
open Words_s
open TypesNative_s
open FStar.FunctionalExtensionality

let xmm_taint (ts:taintState) (x:xmm) = ts.xmmTaint x

let set_xmm_taint (ts:taintState) (xmm:xmm) (taint:taint) : taintState =
  TaintState ts.regTaint ts.flagsTaint ts.cfFlagsTaint (fun x -> if x = xmm then taint else ts.xmmTaint x)

#reset-options "--initial_ifuel 2 --max_ifuel 2 --initial_fuel 4 --max_fuel 4 --z3rlimit 80"

val check_if_pxor_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.Pxor? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_pxor_leakage_free ins ts =
  let S.Pxor dst src, _, _ = ins.ops in
  if src = dst then begin
    let ts' = set_xmm_taint ts dst Public in
    Arch.Types.lemma_quad32_xor();
    true, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint
  end
  else begin
    let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
    let ts' = set_xmm_taint ts dst taint in
    true, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint
  end

val check_if_paddd_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.Paddd? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_paddd_leakage_free ins ts =
  let S.Paddd dst src, _, _ = ins.ops in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_pslld_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.Pslld? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_pslld_leakage_free ins ts =
  let S.Pslld dst amt, _, _ = ins.ops in
  let taint = xmm_taint ts dst in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint

val check_if_psrld_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.Psrld? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_psrld_leakage_free ins ts =
  let S.Psrld dst amt, _, _ = ins.ops in
  let taint = xmm_taint ts dst in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint

val check_if_psrldq_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.Psrldq? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_psrldq_leakage_free ins ts =
  let S.Psrldq dst amt, _, _ = ins.ops in
  let taint = xmm_taint ts dst in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint

val check_if_shufpd_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.Shufpd? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_shufpd_leakage_free ins ts =
  let S.Shufpd dst src _, _, _ = ins.ops in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_pshufb_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.Pshufb? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_pshufb_leakage_free ins ts =
  let S.Pshufb dst src, _, _ = ins.ops in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_pshufd_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.Pshufd? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_pshufd_leakage_free ins ts =
  let S.Pshufd dst src _, _, _ = ins.ops in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint

val check_if_pcmpeqd_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.Pcmpeqd? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_pcmpeqd_leakage_free ins ts =
  let S.Pcmpeqd dst src, _, _ = ins.ops in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint

val check_if_pextrq_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.Pextrq? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

open Words.Two_s
open Words.Four_s

let check_if_pextrq_leakage_free_aux (ins:tainted_ins{let i, _, _ = ins.ops in S.Pextrq? i}) ts =
  let S.Pextrq dst src index, _, _ = ins.ops in
  let fixedTime = operand_does_not_use_secrets dst ts in
  assert (fixedTime ==> isConstantTime (Ins ins) ts);
  let taint = merge_taint (operand_taint dst ts Public) (xmm_taint ts src) in
  let taint = merge_taint taint ins.t in
  if OMem? dst && taint <> ins.t then false, ts
  else
  let ts' = set_taint dst ts taint in
  fixedTime, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint

val lemma_if_pextrq_leakage_free_aux: (ins:tainted_ins{let i, _, _ = ins.ops in S.Pextrq? i}) -> (ts:taintState) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_pextrq_leakage_free_aux ins ts in b2t b ==>
     isConstantTime (Ins ins) ts /\ isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2)


let lemma_if_pextrq_leakage_free_aux ins ts s1 s2 fuel =
  let S.Pextrq dst src index, _, _ = ins.ops in
  match dst with
  | OConst _ -> ()
  | OReg _ -> ()
  | OMem m ->
  let ptr1 = eval_maddr m s1.state in
  let ptr2 = eval_maddr m s2.state in
  let v1 = eval_xmm src s1.state in
  let v2 = eval_xmm src s2.state in
  let v1 = four_to_two_two v1 in
  let v2 = four_to_two_two v2 in
  let v1 = two_to_nat 32 (two_select v1 (index % 2)) in
  let v2 = two_to_nat 32 (two_select v2 (index % 2)) in
  if not (valid_mem64 ptr1 s1.state.mem) || not (valid_mem64 ptr2 s2.state.mem) then ()
  else begin
  lemma_store_load_mem64 ptr1 v1 s1.state.mem;
  lemma_store_load_mem64 ptr2 v2 s2.state.mem;
  lemma_valid_store_mem64 ptr1 v1 s1.state.mem;
  lemma_valid_store_mem64 ptr2 v2 s2.state.mem;
  lemma_frame_store_mem64 ptr1 v1 s1.state.mem;
  lemma_frame_store_mem64 ptr2 v2 s2.state.mem
  end


let check_if_pextrq_leakage_free ins ts =
  Classical.forall_intro_3 (lemma_if_pextrq_leakage_free_aux ins ts);
  check_if_pextrq_leakage_free_aux ins ts

val check_if_pinsrd_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.Pinsrd? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_pinsrd_leakage_free ins ts =
  let S.Pinsrd dst src i, _, _ = ins.ops in
  let fixedTime = operand_does_not_use_secrets src ts in
  assert (fixedTime ==> isConstantTime (Ins ins) ts);
  let taint = merge_taint (xmm_taint ts dst) (operand_taint src ts Public) in
  let taint = merge_taint taint ins.t in
  let ts' = set_xmm_taint ts dst taint in
  fixedTime, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint

val check_if_pinsrq_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.Pinsrq? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_pinsrq_leakage_free ins ts =
  let S.Pinsrq dst src _, _, _ = ins.ops in
  let fixedTime = operand_does_not_use_secrets src ts in
  assert (fixedTime ==> isConstantTime (Ins ins) ts);
  let taint = merge_taint (xmm_taint ts dst) (operand_taint src ts Public) in
  let taint = merge_taint taint ins.t in
  let ts' = set_xmm_taint ts dst taint in
  fixedTime, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint

val check_if_vpslldq_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.VPSLLDQ? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_vpslldq_leakage_free ins ts =
  let S.VPSLLDQ dst src _, _, _ = ins.ops in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint

val check_if_pclmuldqd_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.Pclmulqdq? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

#set-options "--z3rlimit 40"

let check_if_pclmuldqd_leakage_free ins ts =
  let S.Pclmulqdq dst src _, _, _ = ins.ops in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_aesni_enc_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.AESNI_enc? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_aesni_enc_leakage_free ins ts =
  let S.AESNI_enc dst src, _, _ = ins.ops in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_aesni_enc_last_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.AESNI_enc_last? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_aesni_enc_last_leakage_free ins ts =
  let S.AESNI_enc_last dst src, _, _ = ins.ops in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_aesni_dec_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.AESNI_dec? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_aesni_dec_leakage_free ins ts =
  let S.AESNI_dec dst src, _, _ = ins.ops in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_aesni_dec_last_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.AESNI_dec_last? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_aesni_dec_last_leakage_free ins ts =
  let S.AESNI_dec_last dst src, _, _ = ins.ops in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_aesni_imc_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.AESNI_imc? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_aesni_imc_leakage_free ins ts =
  let S.AESNI_imc dst src, _, _ = ins.ops in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_aesni_keygen_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.AESNI_keygen_assist? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_aesni_keygen_leakage_free ins ts =
  let S.AESNI_keygen_assist dst src _, _, _ = ins.ops in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_movdqu_leakage_free: (ins:tainted_ins{let i, _, _ = ins.ops in S.MOVDQU? i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let mov128_does_not_use_secret ts = function
  | Mov128Xmm _ -> true
  | Mov128Mem m -> maddr_does_not_use_secrets m ts

let check_if_movdqu_leakage_free_aux (ins:tainted_ins{let i, _, _ = ins.ops in S.MOVDQU? i}) ts =
  let S.MOVDQU dst src, _, _ = ins.ops in
  let taint = match src with
    | Mov128Mem _ -> ins.t
    | Mov128Xmm x -> (xmm_taint ts x)
  in
  let ts' = match dst with
    | Mov128Mem _ -> ts
    | Mov128Xmm x -> set_xmm_taint ts x taint
  in
  if Mov128Mem? dst && taint <> ins.t then false, ts
  else
  (mov128_does_not_use_secret ts src && mov128_does_not_use_secret ts dst),
   TaintState ts'.regTaint ts'.flagsTaint ts'.cfFlagsTaint ts'.xmmTaint

val lemma_if_movdqu_leakage_free_aux: (ins:tainted_ins{let i, _, _ = ins.ops in S.MOVDQU? i}) -> (ts:taintState) -> (s1:traceState) -> (s2:traceState) -> (fuel:nat) -> Lemma
(let b, ts' = check_if_movdqu_leakage_free_aux ins ts in b2t b ==>
     isConstantTime (Ins ins) ts /\ isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2)

val load64_128_eq (ptr1 ptr2:int) (s1 s2:traceState) : Lemma
  (requires valid_mem128 ptr1 s1.state.mem /\ valid_mem128 ptr2 s2.state.mem)
  (ensures load_mem64 ptr1 s1.state.mem == load_mem64 ptr2 s2.state.mem /\
          load_mem64 (ptr1+8) s1.state.mem == load_mem64 (ptr2 + 8) s2.state.mem ==>
          load_mem128 ptr1 s1.state.mem == load_mem128 ptr2 s2.state.mem)

val nat32_64_inj (v1 v2:nat32) (v:nat64) : Lemma
  (requires v1 + 0x100000000 `op_Multiply` v2 == v)
  (ensures forall (v3 v4:nat32). v3 + 0x100000000 `op_Multiply` v4 == v ==> v1 == v3 /\ v2 == v4)

let nat32_64_inj v1 v2 v = ()

let load64_128_eq ptr1 ptr2 s1 s2 =
  let v_lo1 = load_mem64 ptr1 s1.state.mem in
  let v_lo2 = load_mem64 ptr2 s2.state.mem in
  let v_hi1 = load_mem64 (ptr1+8) s1.state.mem in
  let v_hi2 = load_mem64 (ptr2+8) s2.state.mem in
  let v1 = load_mem128 ptr1 s1.state.mem in
  let v2 = load_mem128 ptr2 s2.state.mem in
  load128_64 ptr1 s1.state;
  load128_64 ptr2 s2.state;
  nat32_64_inj v1.lo0 v1.lo1 v_lo1;
  nat32_64_inj v1.hi2 v1.hi3 v_hi1


#set-options "--z3rlimit 200"

let lemma_if_movdqu_leakage_free_aux ins ts s1 s2 fuel =
  let S.MOVDQU dst src, _, _ = ins.ops in
  let r1 = taint_eval_ins ins s1 in
  let r2 = taint_eval_ins ins s2 in
  match src with
  | Mov128Xmm x -> begin
    match dst with
    | Mov128Xmm _ -> ()
    | Mov128Mem m ->
      let ptr1 = eval_maddr m s1.state in
      let ptr2 = eval_maddr m s2.state in
      if not (valid_mem128 ptr1 s1.state.mem) || not (valid_mem128 ptr2 s2.state.mem) then ()
      else
      let v1 = eval_xmm x s1.state in
      let v2 = eval_xmm x s2.state in
      let v1_1 = v1.lo0 + 0x100000000 `op_Multiply` v1.lo1 in
      let v1_2 = v1.hi2 + 0x100000000 `op_Multiply` v1.hi3 in
      let v2_1 = v2.lo0 + 0x100000000 `op_Multiply` v2.lo1 in
      let v2_2 = v2.hi2 + 0x100000000 `op_Multiply` v2.hi3 in
      store128_64 ptr1 v1 s1.state;
      store128_64 ptr2 v2 s2.state;
      valid128_64 ptr1 s1.state;
      valid128_64 ptr2 s2.state;
      let mem1 = store_mem64 (ptr1+8) v1_2 s1.state.mem in
      let mem2 = store_mem64 (ptr2+8) v2_2 s2.state.mem in
      lemma_store_load_mem64 (ptr1+8) v1_2 s1.state.mem;
      lemma_store_load_mem64 (ptr2+8) v2_2 s2.state.mem;
      lemma_valid_store_mem64 (ptr1+8) v1_2 s1.state.mem;
      lemma_valid_store_mem64 (ptr2+8) v2_2 s2.state.mem;
      lemma_frame_store_mem64 (ptr1+8) v1_2 s1.state.mem;
      lemma_frame_store_mem64 (ptr2+8) v2_2 s2.state.mem;
      lemma_store_load_mem64 ptr1 v1_1 mem1;
      lemma_store_load_mem64 ptr2 v2_1 mem2;
      lemma_valid_store_mem64 ptr1 v1_1 mem1;
      lemma_valid_store_mem64 ptr2 v2_1 mem2;
      lemma_frame_store_mem64 ptr1 v1_1 mem1;
      lemma_frame_store_mem64 ptr2 v2_1 mem2
   end
 | Mov128Mem m -> begin
    let ptr1 = eval_maddr m s1.state in
    let ptr2 = eval_maddr m s2.state in
    if not (valid_mem128 ptr1 s1.state.mem) || not (valid_mem128 ptr2 s2.state.mem) then ()
    else (
    valid128_64 ptr1 s1.state;
    valid128_64 ptr2 s2.state;
    load128_64 ptr1 s1.state;
    load128_64 ptr2 s2.state;
    load64_128_eq ptr1 ptr2 s1 s2;
    match dst with
    | Mov128Xmm _ -> ()
    | Mov128Mem m -> begin
      let v1 = load_mem128 ptr1 s1.state.mem in
      let v2 = load_mem128 ptr2 s2.state.mem in
      let v1_1 = load_mem64 ptr1 s1.state.mem in
      let v1_2 = load_mem64 (ptr1+8) s1.state.mem in
      let v2_1 = load_mem64 ptr2 s2.state.mem in
      let v2_2 = load_mem64 (ptr2+8) s2.state.mem in
      (* New pointers for dest *)
      let ptr1 = eval_maddr m s1.state in
      let ptr2 = eval_maddr m s2.state in
      if not (valid_mem128 ptr1 s1.state.mem) || not (valid_mem128 ptr2 s2.state.mem) then ()
      else (
      store128_64 ptr1 v1 s1.state;
      store128_64 ptr2 v2 s2.state;
      valid128_64 ptr1 s1.state;
      valid128_64 ptr2 s2.state;
      let mem1 = store_mem64 (ptr1+8) v1_2 s1.state.mem in
      let mem2 = store_mem64 (ptr2+8) v2_2 s2.state.mem in
      lemma_store_load_mem64 (ptr1+8) v1_2 s1.state.mem;
      lemma_store_load_mem64 (ptr2+8) v2_2 s2.state.mem;
      lemma_valid_store_mem64 (ptr1+8) v1_2 s1.state.mem;
      lemma_valid_store_mem64 (ptr2+8) v2_2 s2.state.mem;
      lemma_frame_store_mem64 (ptr1+8) v1_2 s1.state.mem;
      lemma_frame_store_mem64 (ptr2+8) v2_2 s2.state.mem;
      lemma_store_load_mem64 ptr1 v1_1 mem1;
      lemma_store_load_mem64 ptr2 v2_1 mem2;
      lemma_valid_store_mem64 ptr1 v1_1 mem1;
      lemma_valid_store_mem64 ptr2 v2_1 mem2;
      lemma_frame_store_mem64 ptr1 v1_1 mem1;
      lemma_frame_store_mem64 ptr2 v2_1 mem2
      )
    end
    )
   end

let check_if_movdqu_leakage_free ins ts =
  Classical.forall_intro_3 (lemma_if_movdqu_leakage_free_aux ins ts);
  check_if_movdqu_leakage_free_aux ins ts

let check_if_xmm_ins_consumes_fixed_time ins ts =
  let i, _, _ = ins.ops in
  match i with
    | S.Paddd dst src -> check_if_paddd_leakage_free ins ts
    | S.Pxor dst src -> check_if_pxor_leakage_free ins ts
    | S.Pslld dst amt -> check_if_pslld_leakage_free ins ts
    | S.Psrld dst amt -> check_if_psrld_leakage_free ins ts
    | S.Psrldq _ _ -> check_if_psrldq_leakage_free ins ts
    | S.Shufpd _ _ _ -> check_if_shufpd_leakage_free ins ts
    | S.Pshufb dst src -> check_if_pshufb_leakage_free ins ts
    | S.Pshufd dst src permutation -> check_if_pshufd_leakage_free ins ts
    | S.Pinsrd _ _ _  -> check_if_pinsrd_leakage_free ins ts
    | S.Pinsrq _ _ _ -> check_if_pinsrq_leakage_free ins ts
    | S.Pcmpeqd _ _ -> check_if_pcmpeqd_leakage_free ins ts
    | S.Pextrq _ _ _ -> check_if_pextrq_leakage_free ins ts
    | S.VPSLLDQ dst src count -> check_if_vpslldq_leakage_free ins ts
    | S.MOVDQU dst src -> false, ts
    | S.Pclmulqdq dst src imm -> check_if_pclmuldqd_leakage_free ins ts
    | S.AESNI_enc dst src -> check_if_aesni_enc_leakage_free ins ts
    | S.AESNI_enc_last dst src -> check_if_aesni_enc_last_leakage_free ins ts
    | S.AESNI_dec dst src -> check_if_aesni_dec_leakage_free ins ts
    | S.AESNI_dec_last dst src -> check_if_aesni_dec_last_leakage_free ins ts
    | S.AESNI_imc dst src -> check_if_aesni_imc_leakage_free ins ts
    | S.AESNI_keygen_assist dst src imm -> check_if_aesni_keygen_leakage_free ins ts

