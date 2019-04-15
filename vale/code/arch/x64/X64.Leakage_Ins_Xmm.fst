module X64.Leakage_Ins_Xmm
open X64.Machine_s
open X64.Taint_Semantics_s
open X64.Bytes_Semantics_s
open X64.Leakage_s
open X64.Leakage_Helpers
open Types_s
open Words_s
open Arch.Types
open TypesNative_s
open FStar.FunctionalExtensionality
open X64.Bytes_Semantics

let xmm_taint (ts:taintState) (x:xmm) = ts.xmmTaint x

let set_xmm_taint (ts:taintState) (xmm_v:xmm) (taint:taint) : taintState =
  TaintState ts.regTaint ts.flagsTaint ts.cfFlagsTaint 
    (FunctionalExtensionality.on xmm (fun x -> if x = xmm_v then taint else ts.xmmTaint x))

#reset-options "--initial_ifuel 2 --max_ifuel 2 --initial_fuel 4 --max_fuel 4 --z3rlimit 80"

val check_if_pxor_leakage_free: (ins:tainted_ins{Pxor? ins.i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_pxor_leakage_free ins ts =
  let Pxor dst src = ins.i in
  if src = dst then begin
    let ts' = set_xmm_taint ts dst Public in
    lemma_quad32_xor ();
    true, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint
  end
  else begin
    let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
    let ts' = set_xmm_taint ts dst taint in
    true, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint
  end

val check_if_paddd_leakage_free: (ins:tainted_ins{Paddd? ins.i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_paddd_leakage_free ins ts =
  let Paddd dst src = ins.i in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_pslld_leakage_free: (ins:tainted_ins{Pslld? ins.i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_pslld_leakage_free ins ts =
  let Pslld dst amt = ins.i in
  let taint = xmm_taint ts dst in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint

val check_if_psrld_leakage_free: (ins:tainted_ins{Psrld? ins.i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_psrld_leakage_free ins ts =
  let Psrld dst amt = ins.i in
  let taint = xmm_taint ts dst in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint

val check_if_psrldq_leakage_free: (ins:tainted_ins{Psrldq? ins.i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_psrldq_leakage_free ins ts =
  let Psrldq dst _ = ins.i in
  let taint = xmm_taint ts dst in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint

val check_if_shufpd_leakage_free: (ins:tainted_ins{Shufpd? ins.i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_shufpd_leakage_free ins ts =
  let Shufpd dst src _ = ins.i in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_palignr_leakage_free: (ins:tainted_ins{Palignr? ins.i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_palignr_leakage_free ins ts =
  let Palignr dst src _ = ins.i in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_pshufb_leakage_free: (ins:tainted_ins{Pshufb? ins.i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_pshufb_leakage_free ins ts =
  let Pshufb dst src = ins.i in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_pshufd_leakage_free: (ins:tainted_ins{Pshufd? ins.i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_pshufd_leakage_free ins ts =
  let Pshufd dst src _ = ins.i in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint

val check_if_pcmpeqd_leakage_free: (ins:tainted_ins{Pcmpeqd? ins.i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_pcmpeqd_leakage_free ins ts =
  let Pcmpeqd dst src = ins.i in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint

val check_if_pextrq_leakage_free: (ins:tainted_ins{Pextrq? ins.i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

open Words.Two_s
open Words.Four_s

let check_if_pextrq_leakage_free_aux (ins:tainted_ins{Pextrq? ins.i}) ts =
  let Pextrq dst src index = ins.i in
  let fixedTime = operand_does_not_use_secrets dst ts in
  assert (fixedTime ==> isConstantTime (Ins ins) ts);
  let taint = merge_taint (operand_taint dst ts Public) (xmm_taint ts src) in
  let taint = merge_taint taint ins.t in
  if OMem? dst && taint <> ins.t then false, ts
  else
  let ts' = set_taint dst ts taint in
  fixedTime, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint

let lemma_pextrq_same_public_aux (ts:taintState) (ins:tainted_ins{Pextrq? ins.i}) (s1:traceState) (s2:traceState)
                               (fuel:nat) (b:bool) (ts':taintState)
  :Lemma (requires ((b, ts') == check_if_pextrq_leakage_free_aux ins ts /\ b /\
                    is_explicit_leakage_free_lhs (Ins ins) fuel ts ts' s1 s2))
         (ensures  (is_explicit_leakage_free_rhs (Ins ins) fuel ts ts' s1 s2)) =
    let Pextrq dst src index, t = ins.i, ins.t in
    let dsts, srcs = extract_operands ins.i in

    let r1 = taint_eval_code (Ins ins) fuel s1 in
    let r2 = taint_eval_code (Ins ins) fuel s2 in

    let s1' = Some?.v r1 in
    let s2' = Some?.v r2 in

    let s1b = run (check (taint_match_list srcs t s1.memTaint)) s1.state in
    let s2b = run (check (taint_match_list srcs t s2.memTaint)) s2.state in

    let taint = merge_taint (operand_taint dst ts Public) (xmm_taint ts src) in
    let taint = merge_taint taint ins.t in

    let v1 = eval_xmm src s1.state in
    let v2 = eval_xmm src s2.state in
    let v1 = four_to_two_two v1 in
    let v2 = four_to_two_two v2 in
    let v1 = two_to_nat 32 (two_select v1 (index % 2)) in
    let v2 = two_to_nat 32 (two_select v2 (index % 2)) in

    match dst with
    | OConst _ -> ()
    | OReg r -> ()
    | OMem m ->
      let aux (x:int) : Lemma
        (requires Public? s1'.memTaint.[x] || Public? s2'.memTaint.[x])
        (ensures s1'.state.mem.[x] == s2'.state.mem.[x]) =
        let ptr1 = eval_maddr m s1.state in
        let ptr2 = eval_maddr m s2.state in
        assert (ptr1 == ptr2);
         if x < ptr1 || x >= ptr1 + 8 then (
          // If we're outside the modified area, nothing changed, the property still holds
          frame_update_heap ptr1 v1 s1b.mem;
          frame_update_heap ptr1 v2 s2b.mem
        ) else (
          if Secret? taint then ()
          else (
            correct_update_get ptr1 v1 s1b.mem;
            correct_update_get ptr1 v2 s2b.mem;
            // If values are identical, the bytes also are identical
            same_mem_get_heap_val ptr1 s1'.state.mem s2'.state.mem
          )
        )
      
      in Classical.forall_intro (Classical.move_requires aux)
    | OStack m -> ()

let lemma_pextrq_same_public (ts:taintState) (ins:tainted_ins{Pextrq? ins.i}) (s1:traceState) (s2:traceState) 
  (fuel:nat)
  :Lemma (let b, ts' = check_if_pextrq_leakage_free_aux ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))
  = let b, ts' = check_if_pextrq_leakage_free_aux ins ts in
    Classical.move_requires (lemma_pextrq_same_public_aux ts ins s1 s2 fuel b) ts'

let check_if_pextrq_leakage_free ins ts =
  Classical.forall_intro_3 (lemma_pextrq_same_public ts ins);
  check_if_pextrq_leakage_free_aux ins ts

val check_if_pinsrd_leakage_free: (ins:tainted_ins{Pinsrd? ins.i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_pinsrd_leakage_free ins ts =
  let Pinsrd dst src i = ins.i in
  let fixedTime = operand_does_not_use_secrets src ts in
  assert (fixedTime ==> isConstantTime (Ins ins) ts);
  let taint = merge_taint (xmm_taint ts dst) (operand_taint src ts Public) in
  let taint = merge_taint taint ins.t in
  let ts' = set_xmm_taint ts dst taint in
  Opaque_s.reveal_opaque get_heap_val64_def;
  fixedTime, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint

val check_if_pinsrq_leakage_free: (ins:tainted_ins{Pinsrq? ins.i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_pinsrq_leakage_free ins ts =
  let Pinsrq dst src _ = ins.i in
  let fixedTime = operand_does_not_use_secrets src ts in
  assert (fixedTime ==> isConstantTime (Ins ins) ts);
  let taint = merge_taint (xmm_taint ts dst) (operand_taint src ts Public) in
  let taint = merge_taint taint ins.t in
  let ts' = set_xmm_taint ts dst taint in
  Opaque_s.reveal_opaque get_heap_val64_def;
  fixedTime, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint

val check_if_vpslldq_leakage_free: (ins:tainted_ins{VPSLLDQ? ins.i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_vpslldq_leakage_free ins ts =
  let VPSLLDQ dst src _ = ins.i in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint ts.flagsTaint ts.cfFlagsTaint ts'.xmmTaint

val check_if_pclmuldqd_leakage_free: (ins:tainted_ins{Pclmulqdq? ins.i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

#set-options "--z3rlimit 40"

let check_if_pclmuldqd_leakage_free ins ts =
  let Pclmulqdq dst src _ = ins.i in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_aesni_enc_leakage_free: (ins:tainted_ins{AESNI_enc? ins.i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_aesni_enc_leakage_free ins ts =
  let AESNI_enc dst src = ins.i in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_aesni_enc_last_leakage_free: (ins:tainted_ins{AESNI_enc_last? ins.i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_aesni_enc_last_leakage_free ins ts =
  let AESNI_enc_last dst src = ins.i in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_aesni_dec_leakage_free: (ins:tainted_ins{AESNI_dec? ins.i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_aesni_dec_leakage_free ins ts =
  let AESNI_dec dst src = ins.i in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_aesni_dec_last_leakage_free: (ins:tainted_ins{AESNI_dec_last? ins.i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_aesni_dec_last_leakage_free ins ts =
  let AESNI_dec_last dst src = ins.i in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_aesni_imc_leakage_free: (ins:tainted_ins{AESNI_imc? ins.i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_aesni_imc_leakage_free ins ts =
  let AESNI_imc dst src = ins.i in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_aesni_keygen_leakage_free: (ins:tainted_ins{AESNI_keygen_assist? ins.i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_aesni_keygen_leakage_free ins ts =
  let AESNI_keygen_assist dst src _ = ins.i in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_sha256_rnds2_leakage_free: (ins:tainted_ins{SHA256_rnds2? ins.i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let check_if_sha256_rnds2_leakage_free ins ts =
  let SHA256_rnds2 dst src = ins.i in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let taint = merge_taint (xmm_taint ts 0) taint in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_sha256_msg1_leakage_free: (ins:tainted_ins{SHA256_msg1? ins.i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})
     
let check_if_sha256_msg1_leakage_free ins ts =
  let SHA256_msg1 dst src = ins.i in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_sha256_msg2_leakage_free: (ins:tainted_ins{SHA256_msg2? ins.i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})
     
let check_if_sha256_msg2_leakage_free ins ts =
  let SHA256_msg2 dst src = ins.i in
  let taint = merge_taint (xmm_taint ts dst) (xmm_taint ts src) in
  let ts' = set_xmm_taint ts dst taint in
  true, TaintState ts'.regTaint Secret Secret ts'.xmmTaint

val check_if_movdqu_leakage_free: (ins:tainted_ins{MOVDQU? ins.i}) -> (ts:taintState) -> (res:(bool*taintState){let b, ts' = res in b2t b ==>
     isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'})

let mov128_does_not_use_secret ts = function
  | Mov128Xmm _ -> true
  | Mov128Mem m | Mov128Stack m-> maddr_does_not_use_secrets m ts

let check_if_movdqu_leakage_free_aux (ins:tainted_ins{MOVDQU? ins.i}) ts =
  let MOVDQU dst src = ins.i in
  let taint = match src with
    | Mov128Mem _ -> ins.t
    | Mov128Xmm x -> (xmm_taint ts x)
    | Mov128Stack m -> Secret
  in
  let ts' = match dst with
    | Mov128Mem _ -> ts
    | Mov128Xmm x -> set_xmm_taint ts x taint
    | Mov128Stack _ -> ts
  in
  if Mov128Mem? dst && taint <> ins.t then false, ts
  else
  (mov128_does_not_use_secret ts src && mov128_does_not_use_secret ts dst),
   TaintState ts'.regTaint ts'.flagsTaint ts'.cfFlagsTaint ts'.xmmTaint

#set-options "--z3rlimit 300"

let frame_update_heap128_x (ptr:int) (j:int) (v:quad32) (mem:heap) : Lemma
  (requires j < ptr \/ j >= ptr + 16)
  (ensures (let new_mem = update_heap128 ptr v mem in
    mem.[j] == new_mem.[j])) = frame_update_heap128 ptr v mem


let lemma_movdqu_same_public_aux (ts:taintState) (ins:tainted_ins{MOVDQU? ins.i}) (s1:traceState) (s2:traceState)
                               (fuel:nat) (b:bool) (ts':taintState)
  :Lemma (requires ((b, ts') == check_if_movdqu_leakage_free_aux ins ts /\ b /\
                    is_explicit_leakage_free_lhs (Ins ins) fuel ts ts' s1 s2))
         (ensures  (is_explicit_leakage_free_rhs (Ins ins) fuel ts ts' s1 s2)) =
    let MOVDQU dst src, t = ins.i, ins.t in
    let dsts, srcs = extract_operands ins.i in

    let r1 = taint_eval_code (Ins ins) fuel s1 in
    let r2 = taint_eval_code (Ins ins) fuel s2 in

    let s1' = Some?.v r1 in
    let s2' = Some?.v r2 in

    let s1b = run (check (taint_match128 src t s1.memTaint)) s1.state in
    let s2b = run (check (taint_match128 src t s1.memTaint)) s2.state in

    let v1 = eval_mov128_op src s1.state in
    let v2 = eval_mov128_op src s2.state in
 
    let taint = match src with
      | Mov128Mem _ -> ins.t
      | Mov128Xmm x -> (xmm_taint ts x)
      | Mov128Stack _ -> Secret
    in

    let aux_value() : Lemma
      (requires Public? taint)
      (ensures v1 == v2) =
        match src with
        | Mov128Xmm x -> ()
        | Mov128Mem m -> 
          let ptr1 = eval_maddr m s1b in
          let ptr2 = eval_maddr m s2b in
          assert (forall i. i >= ptr1 /\ i < ptr1 + 16 ==> s1.state.mem.[i] == s2.state.mem.[i]);
          Opaque_s.reveal_opaque get_heap_val128_def;
          Opaque_s.reveal_opaque get_heap_val32_def     
    in

    match dst with
    | Mov128Xmm x -> if Secret? taint then () else aux_value()
    | Mov128Mem m ->
      let aux (x:int) : Lemma
        (requires Public? s1'.memTaint.[x] || Public? s2'.memTaint.[x])
        (ensures s1'.state.mem.[x] == s2'.state.mem.[x]) =
        let ptr1 = eval_maddr m s1.state in
        let ptr2 = eval_maddr m s2.state in
        assert (ptr1 == ptr2);
        if x < ptr1 || x >= ptr1 + 16 then (
          // If we're outside the modified area, nothing changed, the property still holds
          frame_update_heap128_x ptr1 x v1 s1b.mem;
          frame_update_heap128_x ptr1 x v2 s2b.mem
        ) else (
          if Secret? taint then ()
          else (
            aux_value();
            correct_update_get128 ptr1 v1 s1b.mem;
            correct_update_get128 ptr1 v2 s2b.mem;
            // If values are identical, the bytes also are identical
            same_mem_get_heap_val128 ptr1 s1'.state.mem s2'.state.mem
          )
        )
      
      in Classical.forall_intro (Classical.move_requires aux)
      | Mov128Stack _ -> ()

let lemma_movdqu_same_public (ts:taintState) (ins:tainted_ins{MOVDQU? ins.i}) (s1:traceState) (s2:traceState) 
  (fuel:nat)
  :Lemma (let b, ts' = check_if_movdqu_leakage_free_aux ins ts in
  (b2t b ==> isExplicitLeakageFreeGivenStates (Ins ins) fuel ts ts' s1 s2))
  = let b, ts' = check_if_movdqu_leakage_free_aux ins ts in
    Classical.move_requires (lemma_movdqu_same_public_aux ts ins s1 s2 fuel b) ts'

let check_if_movdqu_leakage_free ins ts =
  Classical.forall_intro_3 (lemma_movdqu_same_public ts ins);
  check_if_movdqu_leakage_free_aux ins ts

let check_if_xmm_ins_consumes_fixed_time ins ts =
  match ins.i with
    | Paddd dst src -> check_if_paddd_leakage_free ins ts
    | Pxor dst src -> check_if_pxor_leakage_free ins ts
    | Pslld dst amt -> check_if_pslld_leakage_free ins ts
    | Psrld dst amt -> check_if_psrld_leakage_free ins ts
    | Psrldq _ _ -> check_if_psrldq_leakage_free ins ts
    | Palignr _ _ _ -> check_if_palignr_leakage_free ins ts
    | Shufpd _ _ _ -> check_if_shufpd_leakage_free ins ts
    | Pshufb dst src -> check_if_pshufb_leakage_free ins ts
    | Pshufd dst src permutation -> check_if_pshufd_leakage_free ins ts
    | Pinsrd _ _ _  -> check_if_pinsrd_leakage_free ins ts
    | Pinsrq _ _ _ -> check_if_pinsrq_leakage_free ins ts
    | Pcmpeqd _ _ -> check_if_pcmpeqd_leakage_free ins ts
    | Pextrq _ _ _ -> check_if_pextrq_leakage_free ins ts
    | VPSLLDQ dst src count -> check_if_vpslldq_leakage_free ins ts
    | MOVDQU dst src -> check_if_movdqu_leakage_free ins ts
    | Pclmulqdq dst src imm -> check_if_pclmuldqd_leakage_free ins ts
    | AESNI_enc dst src -> check_if_aesni_enc_leakage_free ins ts
    | AESNI_enc_last dst src -> check_if_aesni_enc_last_leakage_free ins ts
    | AESNI_dec dst src -> check_if_aesni_dec_leakage_free ins ts
    | AESNI_dec_last dst src -> check_if_aesni_dec_last_leakage_free ins ts
    | AESNI_imc dst src -> check_if_aesni_imc_leakage_free ins ts
    | AESNI_keygen_assist dst src imm -> check_if_aesni_keygen_leakage_free ins ts
    | SHA256_rnds2 _ _ -> check_if_sha256_rnds2_leakage_free ins ts
    | SHA256_msg1 _ _ -> check_if_sha256_msg1_leakage_free ins ts
    | SHA256_msg2 _ _ -> check_if_sha256_msg2_leakage_free ins ts
    | _ -> (false, ts)
