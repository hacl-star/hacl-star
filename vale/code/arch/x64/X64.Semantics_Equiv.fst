module X64.Semantics_Equiv

module S = X64.Bytes_Semantics_s
open X64.Machine_s
open X64.Memory_s
open X64.Semantics_s

val equiv_eval_operand (o:operand) (s:state) : Lemma
  (requires valid_operand o s)
  (ensures eval_operand o s == S.eval_operand o s.state)

let equiv_eval_operand o s = match o with
  | OConst _ | OReg _ -> ()
  | OMem m ->
    let addr = eval_maddr m s in
    equiv_load_mem addr s

val equiv_eval_mov128_op (o:mov128_op) (s:state) : Lemma
  (requires valid_mov128_op o s)
  (ensures eval_mov128_op o s == S.eval_mov128_op o s.state)

let equiv_eval_mov128_op o s = match o with
  | Mov128Xmm _ -> ()
  | Mov128Mem m ->
    let addr = eval_maddr m s in
    equiv_load_mem128 addr s

let equiv_eval_mov (s:state) (ins:S.ins{S.Mov64? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  let S.Mov64 dst src = ins in
  if not s.state.S.ok then ()
  else if not (valid_operand src s) then ()
  else begin
    equiv_eval_operand src s;
    ()
  end

let equiv_eval_add (s:state) (ins:S.ins{S.Add64? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  let S.Add64 dst src = ins in
  if not s.state.S.ok then ()
  else if not (valid_operand src s) || not (valid_operand dst s) then ()
  else begin
    equiv_eval_operand src s;
    equiv_eval_operand dst s;
    ()
  end

let equiv_eval_addlea (s:state) (ins:S.ins{S.AddLea64? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  let S.AddLea64 dst src1 src2 = ins in
  if not s.state.S.ok then ()
  else if not (valid_operand src1 s) || not (valid_operand src2 s) || not (valid_operand dst s) then ()
  else begin
    equiv_eval_operand src1 s;
    equiv_eval_operand src2 s;
    equiv_eval_operand dst s;
    ()
  end

let equiv_eval_addcarry (s:state) (ins:S.ins{S.AddCarry64? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  let S.AddCarry64 dst src = ins in
  if not s.state.S.ok then ()
  else if not (valid_operand src s) || not (valid_operand dst s) then ()
  else begin
    equiv_eval_operand src s;
    equiv_eval_operand dst s;
    ()
  end

let equiv_eval_adcx (s:state) (ins:S.ins{S.Adcx64? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  let S.Adcx64 dst src = ins in
  if not s.state.S.ok then ()
  else if not (valid_operand src s) || not (valid_operand dst s) then ()
  else begin
    equiv_eval_operand src s;
    equiv_eval_operand dst s;
    ()
  end

let equiv_eval_adox (s:state) (ins:S.ins{S.Adox64? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  let S.Adox64 dst src = ins in
  if not s.state.S.ok then ()
  else if not (valid_operand src s) || not (valid_operand dst s) then ()
  else begin
    equiv_eval_operand src s;
    equiv_eval_operand dst s;
    ()
  end

let equiv_eval_sub (s:state) (ins:S.ins{S.Sub64? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  let S.Sub64 dst src = ins in
  if not s.state.S.ok then ()
  else if not (valid_operand src s) || not (valid_operand dst s) then ()
  else begin
    equiv_eval_operand src s;
    equiv_eval_operand dst s;
    ()
  end

let equiv_eval_mul (s:state) (ins:S.ins{S.Mul64? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  let S.Mul64 src = ins in
  if not s.state.S.ok then ()
  else if not (valid_operand src s) then ()
  else begin
    equiv_eval_operand src s;
    ()
  end

let equiv_eval_mulx (s:state) (ins:S.ins{S.Mulx64? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  let S.Mulx64 dst_hi dst_lo src = ins in
  if not s.state.S.ok then ()
  else if not (valid_operand src s) || not (valid_operand dst_lo s) then ()
  else begin
    let lo =  FStar.UInt.mul_mod #64 (eval_reg Rdx s) (eval_operand src s) in
    let s_b = update_operand_preserve_flags' dst_lo lo s in
    if not (valid_operand dst_hi s_b) then ()
    else
    equiv_eval_operand (OReg Rdx) s;
    equiv_eval_operand src s;
    ()
  end

let equiv_eval_imul (s:state) (ins:S.ins{S.IMul64? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  let S.IMul64 dst src = ins in
  if not s.state.S.ok then ()
  else if not (valid_operand src s) || not (valid_operand dst s) then ()
  else begin
    equiv_eval_operand src s;
    equiv_eval_operand dst s;
    ()
  end

let equiv_eval_xor (s:state) (ins:S.ins{S.Xor64? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  let S.Xor64 dst src = ins in
  if not s.state.S.ok then ()
  else if not (valid_operand src s) || not (valid_operand dst s) then ()
  else begin
    equiv_eval_operand src s;
    equiv_eval_operand dst s;
    ()
  end

let equiv_eval_and (s:state) (ins:S.ins{S.And64? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  let S.And64 dst src = ins in
  if not s.state.S.ok then ()
  else if not (valid_operand src s) || not (valid_operand dst s) then ()
  else begin
    equiv_eval_operand src s;
    equiv_eval_operand dst s;
    ()
  end

let equiv_eval_shr (s:state) (ins:S.ins{S.Shr64? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  let S.Shr64 dst src = ins in
  if not s.state.S.ok then ()
  else if not (valid_operand src s) || not (valid_operand dst s) then ()
  else begin
    equiv_eval_operand src s;
    equiv_eval_operand dst s;
    ()
  end

let equiv_eval_shl (s:state) (ins:S.ins{S.Shl64? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  let S.Shl64 dst src = ins in
  if not s.state.S.ok then ()
  else if not (valid_operand src s) || not (valid_operand dst s) then ()
  else begin
    equiv_eval_operand src s;
    equiv_eval_operand dst s;
    ()
  end

let equiv_eval_push (s:state) (ins:S.ins{S.Push? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  let S.Push src = ins in
  if not s.state.S.ok then ()
  else if not (valid_operand src s) then ()
  else begin
    equiv_eval_operand src s;
    ()
  end

let equiv_eval_pop (s:state) (ins:S.ins{S.Pop? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  let S.Pop dst = ins in
  let stack_val = OMem (MReg Rsp 0) in
  if not s.state.S.ok then ()
  else if not (valid_operand dst s) || not (valid_operand stack_val s) then ()
  else begin
    equiv_eval_operand stack_val s;
    equiv_eval_operand dst s;
    ()
  end

let equiv_eval_paddd (s:state) (ins:S.ins{S.Paddd? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  ()

let equiv_eval_pxor (s:state) (ins:S.ins{S.Pxor? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  ()

let equiv_eval_pslld (s:state) (ins:S.ins{S.Pslld? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  ()

let equiv_eval_psrld (s:state) (ins:S.ins{S.Psrld? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  ()

let equiv_eval_psrldq (s:state) (ins:S.ins{S.Psrldq? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  ()

let equiv_eval_shufpd (s:state) (ins:S.ins{S.Shufpd? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  ()

let equiv_eval_pshufb (s:state) (ins:S.ins{S.Pshufb? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  ()

let equiv_eval_pshufd (s:state) (ins:S.ins{S.Pshufd? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  ()

let equiv_eval_pcmpeqd (s:state) (ins:S.ins{S.Pcmpeqd? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  ()

let equiv_eval_pextrq (s:state) (ins:S.ins{S.Pextrq? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  ()

let equiv_eval_pinsrd (s:state) (ins:S.ins{S.Pinsrd? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  let S.Pinsrd _ src _ = ins in
  if not s.state.S.ok then ()
  else if not (valid_operand src s) then ()
  else begin
    equiv_eval_operand src s;
    ()
  end

let equiv_eval_pinsrq (s:state) (ins:S.ins{S.Pinsrq? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  let S.Pinsrq _ src _ = ins in
  if not s.state.S.ok then ()
  else if not (valid_operand src s) then ()
  else begin
    equiv_eval_operand src s;
    ()
  end

let equiv_eval_vpslldq (s:state) (ins:S.ins{S.VPSLLDQ? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  ()

let equiv_eval_movdqu (s:state) (ins:S.ins{S.MOVDQU? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  let S.MOVDQU dst src = ins in
  if not s.state.S.ok then ()
  else if not (valid_mov128_op src s) then ()
  else equiv_eval_mov128_op src s

let equiv_eval_pclmulqdq (s:state) (ins:S.ins{S.Pclmulqdq? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  ()

let equiv_eval_aesni_enc (s:state) (ins:S.ins{S.AESNI_enc? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  ()

let equiv_eval_aesni_enc_last (s:state) (ins:S.ins{S.AESNI_enc_last? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  ()

let equiv_eval_aesni_dec (s:state) (ins:S.ins{S.AESNI_dec? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  ()

let equiv_eval_aesni_dec_last (s:state) (ins:S.ins{S.AESNI_dec_last? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  ()

let equiv_eval_aesni_imc (s:state) (ins:S.ins{S.AESNI_imc? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  ()

let equiv_eval_aesni_keygen (s:state) (ins:S.ins{S.AESNI_keygen_assist? ins}) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  s_hi.state.S.ok ==> s_hi.state == s_bytes) =
  ()

let equiv_eval_ins s ins = match ins with
  | S.Mov64 _ _ -> equiv_eval_mov s ins
  | S.Add64 _ _ -> equiv_eval_add s ins
  | S.AddLea64 _ _ _-> equiv_eval_addlea s ins
  | S.AddCarry64 _ _ -> equiv_eval_addcarry s ins
  | S.Adcx64 _ _ -> equiv_eval_adcx s ins
  | S.Adox64 _ _ -> equiv_eval_adox s ins
  | S.Sub64 _ _ -> equiv_eval_sub s ins
  | S.Mul64 _ -> equiv_eval_mul s ins
  | S.Mulx64 _ _ _ -> equiv_eval_mulx s ins
  | S.IMul64 _ _ -> equiv_eval_imul s ins
  | S.Xor64 _ _ -> equiv_eval_xor s ins
  | S.And64 _ _ -> equiv_eval_and s ins
  | S.Shr64 _ _ -> equiv_eval_shr s ins
  | S.Shl64 _ _ -> equiv_eval_shl s ins
  | S.Push _ -> equiv_eval_push s ins
  | S.Pop _ -> equiv_eval_pop s ins
  | S.Paddd _ _ -> equiv_eval_paddd s ins
  | S.Pxor _ _ -> equiv_eval_pxor s ins
  | S.Pslld _ _ -> equiv_eval_pslld s ins
  | S.Psrld _ _ -> equiv_eval_psrld s ins
  | S.Psrldq _ _ -> equiv_eval_psrldq s ins
  | S.Shufpd _ _ _ -> equiv_eval_shufpd s ins
  | S.Pshufb _ _ -> equiv_eval_pshufb s ins
  | S.Pshufd _ _ _ -> equiv_eval_pshufd s ins
  | S.Pcmpeqd _ _ -> equiv_eval_pcmpeqd s ins
  | S.Pextrq _ _ _ -> equiv_eval_pextrq s ins
  | S.Pinsrd _ _ _ -> equiv_eval_pinsrd s ins
  | S.Pinsrq _ _ _ -> equiv_eval_pinsrq s ins
  | S.VPSLLDQ _ _ _ -> equiv_eval_vpslldq s ins
  | S.MOVDQU _ _ -> equiv_eval_movdqu s ins
  | S.Pclmulqdq _ _ _ -> equiv_eval_pclmulqdq s ins
  | S.AESNI_enc _ _ -> equiv_eval_aesni_enc s ins
  | S.AESNI_enc_last _ _ -> equiv_eval_aesni_enc_last s ins
  | S.AESNI_dec _ _ -> equiv_eval_aesni_dec s ins
  | S.AESNI_dec_last _ _ -> equiv_eval_aesni_dec_last s ins
  | S.AESNI_imc _ _ -> equiv_eval_aesni_imc s ins
  | S.AESNI_keygen_assist _ _ _ -> equiv_eval_aesni_keygen s ins

val monotone_ok_ins (ins:S.ins) (s:state) : Lemma (
  let s_hi = run (eval_ins ins) s in
  let s_bytes = S.run (S.eval_ins ins) s.state in
  (s_hi.state.S.ok ==> s.state.S.ok) /\
  (s_bytes.S.ok ==> s.state.S.ok))

val monotone_ok_code (code:code) (fuel:nat) (s:state) : Lemma
  (requires True)
  (ensures (
  let s_hi = eval_code code fuel s in
  (Some? s_hi /\ (Some?.v s_hi).state.S.ok ==> s.state.S.ok)))
  (decreases %[fuel; code])

val monotone_ok_codes (l:codes) (fuel:nat) (s:state) : Lemma
  (requires True)
  (ensures (
  let s_hi = eval_codes l fuel s in
  (Some? s_hi /\ (Some?.v s_hi).state.S.ok ==> s.state.S.ok)))
  (decreases %[fuel; l])

val monotone_ok_while (b:ocmp) (code:code) (fuel:nat) (s:state) : Lemma
  (requires True)
  (ensures (
  let s_hi = eval_while b code fuel s in
  (Some? s_hi /\ (Some?.v s_hi).state.S.ok ==> s.state.S.ok)))
  (decreases %[fuel; code])


val monotone_ok_code_bytes (code:code) (fuel:nat) (s:S.state) : Lemma
  (requires True)
  (ensures (
  let s_bytes = S.eval_code code fuel s in
  (Some? s_bytes /\ (Some?.v s_bytes).S.ok ==> s.S.ok)))
  (decreases %[fuel; code])

val monotone_ok_codes_bytes (l:codes) (fuel:nat) (s:S.state) : Lemma
  (requires True)
  (ensures
    (let s_bytes = S.eval_codes l fuel s in
  (Some? s_bytes /\ (Some?.v s_bytes).S.ok ==> s.S.ok)))
  (decreases %[fuel; l])

val monotone_ok_while_bytes (b:ocmp) (code:code) (fuel:nat) (s:S.state) : Lemma
  (requires True)
  (ensures
  (let s_bytes = S.eval_while b code fuel s in
  (Some? s_bytes /\ (Some?.v s_bytes).S.ok ==> s.S.ok)))
  (decreases %[fuel; code])

let monotone_ok_ins ins s = ()

let rec monotone_ok_code code fuel s = match code with
  | Ins ins -> monotone_ok_ins ins s
  | Block l -> monotone_ok_codes l fuel s
  | IfElse ifCond ifTrue ifFalse ->
    let s_hi = run (check (valid_ocmp ifCond)) s in
    monotone_ok_code ifTrue fuel s_hi;
    monotone_ok_code ifFalse fuel s_hi
  | While b c -> monotone_ok_while b c fuel s

and monotone_ok_codes l fuel s = match l with
  | [] -> ()
  | c::tl ->
    let s_opt = eval_code c fuel s in
    monotone_ok_code c fuel s;
    if None? s_opt then () else monotone_ok_codes tl fuel (Some?.v s_opt)

and monotone_ok_while b c fuel s =
  if fuel = 0 then () else
  let s = run (check (valid_ocmp b)) s in
  if not (eval_ocmp s b) then ()
  else (
  monotone_ok_code c (fuel-1) s;
  match eval_code c (fuel-1) s with
    | None -> ()
    | Some s1 -> monotone_ok_while b c (fuel-1) s1
  )

let rec monotone_ok_code_bytes code fuel s = match code with
  | Ins ins -> ()
  | Block l -> monotone_ok_codes_bytes l fuel s
  | IfElse ifCond ifTrue ifFalse ->
    let s_bytes = S.run (S.check (S.valid_ocmp ifCond)) s in
    monotone_ok_code_bytes ifTrue fuel s_bytes;
    monotone_ok_code_bytes ifFalse fuel s_bytes
  | While b c -> monotone_ok_while_bytes b c fuel s

and monotone_ok_codes_bytes l fuel s = match l with
  | [] -> ()
  | c::tl ->
    let s_opt = S.eval_code c fuel s in
    monotone_ok_code_bytes c fuel s;
    if None? s_opt then () else monotone_ok_codes_bytes tl fuel (Some?.v s_opt)

and monotone_ok_while_bytes b c fuel s =
  if fuel = 0 then () else
  let s = S.run (S.check (S.valid_ocmp b)) s in
  if not (S.eval_ocmp s b) then ()
  else (
  monotone_ok_code_bytes c (fuel-1) s;
  match S.eval_code c (fuel-1) s with
    | None -> ()
    | Some s1 -> monotone_ok_while_bytes b c (fuel-1) s1
  )

#set-options "--z3rlimit 20"

let rec equiv_eval_code code fuel s = match code with
  | Ins ins -> equiv_eval_ins s ins
  | Block l -> equiv_eval_codes l fuel s
  | IfElse ifCond ifTrue ifFalse ->
    let s = run (check (valid_ocmp ifCond)) s in
    equiv_eval_code ifTrue fuel s;
    equiv_eval_code ifFalse fuel s
  | While b c -> equiv_eval_while b c fuel s

and equiv_eval_codes l fuel s = match l with
  | [] -> ()
  | c::tl -> let s_opt = eval_code c fuel s in
    let s_bytes = S.eval_code c fuel s.state in
    if None? s_opt then ()
    else if not (Some?.v s_opt).state.S.ok then monotone_ok_codes tl fuel (Some?.v s_opt)
    else begin
      equiv_eval_code c fuel s;
      equiv_eval_codes tl fuel (Some?.v s_opt)
    end

and equiv_eval_while b c fuel s =
  if fuel = 0 then () else
  let s0 = run (check (valid_ocmp b)) s in
  if not (eval_ocmp s0 b) then ()
  else (
    match eval_code c (fuel-1) s0 with
    | None -> ()
    | Some s1 ->
      if s1.state.S.ok then (
        equiv_eval_code c (fuel-1) s0;
        equiv_eval_while b c (fuel-1) s1;
        ()
      )
      else ()
 )

