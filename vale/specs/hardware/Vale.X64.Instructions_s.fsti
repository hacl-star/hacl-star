module Vale.X64.Instructions_s
open FStar.Mul
open Vale.Def.Words_s
open Vale.Def.Words.Two_s
open Vale.Def.Words.Four_s
open Vale.Def.Types_s
open Vale.X64.Machine_s
open Vale.X64.Instruction_s
open Vale.X64.CPU_Features_s
open Vale.X64.CryptoInstructions_s
open FStar.Seq.Base

let eval_Mov64 (src:nat64) : option nat64 = Some src
val ins_Mov64 : instr_dep [out op64] [op64] PreserveFlags eval_Mov64

let eval_MovBe64 (src:nat64) : option nat64 = if movbe_enabled then Some (reverse_bytes_nat64 src) else None
val ins_MovBe64 : instr_dep [out op64] [op64] PreserveFlags eval_MovBe64

let eval_Cmovc64 (dst src:nat64) (carry:bool) : option nat64 = Some (if carry then src else dst)
val ins_Cmovc64 : instr_dep [inOut op64] [op64; opFlagsCf] PreserveFlags eval_Cmovc64

let eval_Add64 (dst src:nat64) : option (bool & nat64) =
  let sum = dst + src in Some (sum >= pow2_64, sum % pow2_64)
val ins_Add64 : instr_dep [out opFlagsCf; inOut op64] [op64] HavocFlags eval_Add64

let eval_AddLea64 (src1 src2:nat64) : option nat64 = Some ((src1 + src2) % pow2_64)
val ins_AddLea64 :instr_dep [out op64] [op64; op64] PreserveFlags eval_AddLea64

let eval_AddCarry64 (old_carry:bool) (dst src:nat64) : option (bool & nat64) =
  let sum = dst + src + (if old_carry then 1 else 0) in
  Some (sum >= pow2_64, sum % pow2_64)
val ins_AddCarry64 : instr_dep [inOut opFlagsCf; inOut op64] [op64] HavocFlags eval_AddCarry64

let eval_Adcx64_Adox64 (old_flag:bool) (dst src:nat64) : option (bool & nat64) =
  let sum = dst + src + (if old_flag then 1 else 0) in
  if adx_enabled then Some (sum >= pow2_64, sum % pow2_64) else None
val ins_Adcx64 : instr_dep [inOut opFlagsCf; inOut op64] [op64] PreserveFlags eval_Adcx64_Adox64
val ins_Adox64 : instr_dep [inOut opFlagsOf; inOut op64] [op64] PreserveFlags eval_Adcx64_Adox64

let eval_Sub64 (dst src:nat64) : option (bool & nat64) =
  let diff = dst - src in Some (diff < 0, diff % pow2_64)
val ins_Sub64 : instr_dep [out opFlagsCf; inOut op64] [op64] HavocFlags eval_Sub64

let eval_Sbb64 (old_carry:bool) (dst src:nat64) : option (bool & nat64) =
  let diff = dst - (src + (if old_carry then 1 else 0)) in
  Some (diff < 0, diff % pow2_64) // We specify cf, but underspecify everything else (via HavocFlags)
val ins_Sbb64 : instr_dep [inOut opFlagsCf; inOut op64] [op64] HavocFlags eval_Sbb64

let eval_Mul64 (rax src:nat64) : option (nat64 & nat64) =
  Some (FStar.UInt.mul_div #64 rax src, FStar.UInt.mul_mod #64 rax src)
val ins_Mul64 : instr_dep [out (one64Reg rRdx); inOut (one64Reg rRax)] [op64] HavocFlags eval_Mul64

let eval_Mulx64 (rdx src:nat64) : option (nat64 & nat64) =
  let hi = FStar.UInt.mul_div #64 rdx src in
  let lo = FStar.UInt.mul_mod #64 rdx src in
  if bmi2_enabled then Some (hi, lo) else None
val ins_Mulx64 : instr_dep [out op64; out op64] [one64Reg rRdx; op64] PreserveFlags eval_Mulx64

let eval_IMul64 (dst src:nat64) : option nat64 =
  Some (FStar.UInt.mul_mod #64 dst src)
val ins_IMul64 : instr_dep [inOut op64] [op64] HavocFlags eval_IMul64

let eval_And64 (dst src:nat64) : option nat64 = Some (iand dst src)
val ins_And64 : instr_dep [inOut op64] [op64] HavocFlags eval_And64

let eval_Xor64 (dst src:nat64) : option (nat64 & (bool & bool)) =
  Some (Vale.Def.Types_s.ixor dst src, (false, false))
val ins_Xor64 : instr_dep [inOut op64; out opFlagsCf; out opFlagsOf] [op64] HavocFlags eval_Xor64

let eval_Shr64 (dst amt:nat64) : option nat64 =
  if amt < 64 then Some (Vale.Def.Types_s.ishr dst amt) else None
val ins_Shr64 : instr_dep [inOut op64] [op64] HavocFlags eval_Shr64

let eval_Shl64 (dst amt:nat64) : option nat64 =
  if amt < 64 then Some (Vale.Def.Types_s.ishl dst amt) else None
val ins_Shl64 : instr_dep [inOut op64] [op64] HavocFlags eval_Shl64

let eval_Cpuid (rax rcx:nat64) : option (nat64 & (nat64 & (nat64 & nat64))) =
  Some (cpuid rRax rax rcx, (cpuid rRbx rax rcx, (cpuid rRcx rax rcx, cpuid rRdx rax rcx)))
val ins_Cpuid :
  instr_dep
    [inOut (one64Reg rRax); out (one64Reg rRbx); inOut (one64Reg rRcx); out (one64Reg rRdx)]
    [] PreserveFlags eval_Cpuid

let check_avx (#a:Type0) (x:option a) : option a =
  if avx_enabled then x else None

let check_sse2 (#a:Type0) (x:option a) : option a =
  if sse2_enabled then x else None

let check_ssse3 (#a:Type0) (x:option a) : option a =
  if ssse3_enabled then x else None

let check_sse4_1 (#a:Type0) (x:option a) : option a =
  if sse4_1_enabled then x else None

let eval_Movdqu (src:quad32) : option quad32 = check_sse2 (Some src)
val ins_Movdqu : instr_dep [out opXmm] [opXmm] PreserveFlags eval_Movdqu

let eval_Pxor (dst src:quad32) : option quad32 = check_sse2 (Some (quad32_xor dst src))
val ins_Pxor : instr_dep [inOut opXmm] [opXmm] PreserveFlags eval_Pxor

let eval_VPxor (src1 src2:quad32) : option quad32 = check_avx (Some (quad32_xor src1 src2))
val ins_VPxor : instr_dep [out opXmm] [opXmm; opXmm] PreserveFlags eval_VPxor

let eval_Pand (dst src:quad32) : option quad32 = check_sse2 (Some (four_map2 (fun di si -> iand di si) dst src))
val ins_Pand : instr_dep [inOut opXmm] [opXmm] PreserveFlags eval_Pand

let eval_Paddd_raw (src1 src2:quad32) : option quad32 =
  Some (Mkfour
    ((src1.lo0 + src2.lo0) % pow2_32)
    ((src1.lo1 + src2.lo1) % pow2_32)
    ((src1.hi2 + src2.hi2) % pow2_32)
    ((src1.hi3 + src2.hi3) % pow2_32))

let eval_Paddd (src1 src2:quad32) : option quad32 = check_sse2 (eval_Paddd_raw src1 src2)
val ins_Paddd : instr_dep [inOut opXmm] [opXmm] PreserveFlags eval_Paddd

let eval_VPaddd (src1 src2:quad32) : option quad32 = check_avx (eval_Paddd_raw src1 src2)
val ins_VPaddd : instr_dep [out opXmm] [opXmm; opXmm] PreserveFlags eval_VPaddd

let eval_Pslld (amt:int) (dst:quad32) : option quad32 =
  check_sse2 (if 0 <= amt && amt < 32 then Some (four_map (fun i -> ishl i amt) dst) else None)
val ins_Pslld (amt:int) : instr_dep [inOut opXmm] [] PreserveFlags (eval_Pslld amt)

let eval_Psrld (amt:int) (dst:quad32) : option quad32 =
  check_sse2 (if 0 <= amt && amt < 32 then Some (four_map (fun i -> ishr i amt) dst) else None)
val ins_Psrld (amt:int) : instr_dep [inOut opXmm] [] PreserveFlags (eval_Psrld amt)

let eval_Psrldq (amt:int) (dst:quad32) : option quad32 = check_sse2 (
  if 0 <= amt && amt < 16 then
    let src_bytes = le_quad32_to_bytes dst in
    let zero_pad = Seq.create amt 0 in
    let remaining_bytes = slice src_bytes amt (length src_bytes) in
    Some (le_bytes_to_quad32 (append zero_pad remaining_bytes))
  else None)
val ins_Psrldq (amt:int) : instr_dep [inOut opXmm] [] PreserveFlags (eval_Psrldq amt)

let eval_Palignr_raw (amount:nat8) (src1 src2:quad32) : option quad32 =
  // We only spec a restricted version sufficient for a handful of standard patterns
  if amount = 4 then
    Some (Mkfour src2.lo1 src2.hi2 src2.hi3 src1.lo0)
  else if amount = 8 then
    Some (Mkfour src2.hi2 src2.hi3 src1.lo0 src1.lo1)
  else None

let eval_Palignr (amount:nat8) (src1 src2:quad32) : option quad32 =
  check_ssse3 (eval_Palignr_raw amount src1 src2)
val ins_Palignr (amount:nat8) :
  instr_dep [inOut opXmm] [opXmm] PreserveFlags (eval_Palignr amount)

let eval_VPalignr (amount:nat8) (src1 src2:quad32) : option quad32 =
  check_avx (eval_Palignr_raw amount src1 src2)
val ins_VPalignr (amount:nat8) :
  instr_dep [out opXmm] [opXmm; opXmm] PreserveFlags (eval_VPalignr amount)

let eval_Shufpd_raw (permutation:int) (src1 src2:quad32) : option quad32 =
  if 0 <= permutation && permutation < 4 then
    Some (Mkfour
      (if permutation % 2 = 0 then src1.lo0 else src1.hi2)
      (if permutation % 2 = 0 then src1.lo1 else src1.hi3)
      (if (permutation / 2) % 2 = 0 then src2.lo0 else src2.hi2)
      (if (permutation / 2) % 2 = 0 then src2.lo1 else src2.hi3))
  else None

let eval_Shufpd (permutation:int) (src1 src2:quad32) : option quad32 =
  check_sse2 (eval_Shufpd_raw permutation src1 src2)
val ins_Shufpd (permutation:int) :
  instr_dep [inOut opXmm] [opXmm] PreserveFlags (eval_Shufpd permutation)

let eval_VShufpd (permutation:int) (src1 src2:quad32) : option quad32 =
  check_avx (eval_Shufpd_raw permutation src1 src2)
val ins_VShufpd (permutation:int) :
  instr_dep [out opXmm] [opXmm; opXmm] PreserveFlags (eval_VShufpd permutation)

let is_full_byte_reversal_mask (q:quad32) : bool =
  q.lo0 = 0x0C0D0E0F &&
  q.lo1 = 0x08090A0B &&
  q.hi2 = 0x04050607 &&
  q.hi3 = 0x00010203

let is_byte_reversal_mask (q:quad32) : bool =
  q.lo0 = 0x00010203 &&
  q.lo1 = 0x04050607 &&
  q.hi2 = 0x08090A0B &&
  q.hi3 = 0x0C0D0E0F

let is_high_dup_reversal_mask (q:quad32) : bool =
  q.lo0 = 0x0C0D0E0F &&
  q.lo1 = 0x08090A0B &&
  q.hi2 = 0x0C0D0E0F &&
  q.hi3 = 0x08090A0B

let is_lower_upper_byte_reversal_mask (q:quad32) : bool =
  q.lo0 = 0x04050607 &&
  q.lo1 = 0x00010203 &&
  q.hi2 = 0x0C0D0E0F &&
  q.hi3 = 0x08090A0B

let eval_Pshufb_raw (src1 src2:quad32) : option quad32 =
  // We only spec a restricted version sufficient for a handful of standard patterns
  if is_full_byte_reversal_mask src2 then
    Some (reverse_bytes_quad32 src1)
  else if is_byte_reversal_mask src2 then
    Some (Mkfour
      (reverse_bytes_nat32 src1.lo0)
      (reverse_bytes_nat32 src1.lo1)
      (reverse_bytes_nat32 src1.hi2)
      (reverse_bytes_nat32 src1.hi3))
  else if is_high_dup_reversal_mask src2 then
    Some (Mkfour
      (reverse_bytes_nat32 src1.hi3)
      (reverse_bytes_nat32 src1.hi2)
      (reverse_bytes_nat32 src1.hi3)
      (reverse_bytes_nat32 src1.hi2))
  else if is_lower_upper_byte_reversal_mask src2 then
    Some (Mkfour
      (reverse_bytes_nat32 src1.lo1)
      (reverse_bytes_nat32 src1.lo0)
      (reverse_bytes_nat32 src1.hi3)
      (reverse_bytes_nat32 src1.hi2))
  else None

let eval_Pshufb (src1 src2:quad32) : option quad32 = check_ssse3 (eval_Pshufb_raw src1 src2)
val ins_Pshufb : instr_dep [inOut opXmm] [opXmm] PreserveFlags eval_Pshufb

let eval_VPshufb (src1 src2:quad32) : option quad32 = check_avx (eval_Pshufb_raw src1 src2)
val ins_VPshufb : instr_dep [out opXmm] [opXmm; opXmm] PreserveFlags eval_VPshufb

let eval_Pshufd (permutation:nat8) (src:quad32) : option quad32 = check_sse2 (
  let bits:bits_of_byte = byte_to_twobits permutation in
  Some (Mkfour
    (select_word src bits.lo0)
    (select_word src bits.lo1)
    (select_word src bits.hi2)
    (select_word src bits.hi3)))
val ins_Pshufd (permutation:nat8) :
  instr_dep [out opXmm] [opXmm] PreserveFlags (eval_Pshufd permutation)

let eval_Pcmpeqd (dst src:quad32) : option quad32 = check_sse2 (
  let eq_result (b:bool):nat32 = if b then 0xFFFFFFFF else 0 in
  Some (Mkfour
    (eq_result (src.lo0 = dst.lo0))
    (eq_result (src.lo1 = dst.lo1))
    (eq_result (src.hi2 = dst.hi2))
    (eq_result (src.hi3 = dst.hi3))))
val ins_Pcmpeqd : instr_dep [inOut opXmm] [opXmm] PreserveFlags eval_Pcmpeqd

let eval_Pextrq (index:nat8) (src:quad32) : option nat64 = check_sse4_1 (
  let src_two = four_to_two_two src in
  Some (two_to_nat 32 (two_select src_two (index % 2))))
val ins_Pextrq (index:nat8) : instr_dep [out op64] [opXmm] PreserveFlags (eval_Pextrq index)

let eval_Pinsrd (index:nat8) (dst:quad32) (src:nat64) : option quad32 =
  check_sse4_1 (Some (insert_nat32 dst (src % pow2_32) (index % 4)))
val ins_Pinsrd (index:nat8) : instr_dep [inOut opXmm] [op64] PreserveFlags (eval_Pinsrd index)

let eval_Pinsrq (index:nat8) (dst:quad32) (src:nat64) : option quad32 =
  check_sse4_1 (Some (insert_nat64_def dst src (index % 2)))
val ins_Pinsrq (index:nat8) : instr_dep [inOut opXmm] [op64] PreserveFlags (eval_Pinsrq index)

let eval_Pslldq_raw (count:nat8) (src:quad32) : option quad32 =
  // We only spec the two very special cases we need
  if count = 4 then Some (Mkfour 0 src.lo0 src.lo1 src.hi2)
  else if count = 8 then Some (Mkfour 0 0 src.lo0 src.lo1)
  else None
let eval_VPslldq (count:nat8) (src:quad32) : option quad32 = check_avx (eval_Pslldq_raw count src)
val ins_VPslldq (count:nat8) : instr_dep [out opXmm] [opXmm] PreserveFlags (eval_VPslldq count)

let eval_Psrldq_8_raw (count:nat8) (src:quad32) : option quad32 =
  // We only spec the one very special case we need
  if count = 8 then Some (Mkfour src.hi2 src.hi3 0 0)
  else None
let eval_VPsrldq (count:nat8) (src:quad32) : option quad32 = check_avx (eval_Psrldq_8_raw count src)
val ins_VPsrldq (count:nat8) : instr_dep [out opXmm] [opXmm] PreserveFlags (eval_VPsrldq count)

let eval_Pclmulqdq (imm:int) (src1 src2:quad32) : option quad32 =
  let Mkfour a0 a1 a2 a3 = src1 in
  let Mkfour b0 b1 b2 b3 = src2 in
  let f x0 x1 y0 y1 =
    let x = Vale.Math.Poly2.Bits_s.of_double32 (Mktwo x0 x1) in
    let y = Vale.Math.Poly2.Bits_s.of_double32 (Mktwo y0 y1) in
    Vale.Math.Poly2.Bits_s.to_quad32 (Vale.Math.Poly2_s.mul x y)
    in
  if pclmulqdq_enabled then
    match imm with
    | 0 -> Some (f a0 a1 b0 b1)
    | 1 -> Some (f a2 a3 b0 b1)
    | 16 -> Some (f a0 a1 b2 b3)
    | 17 -> Some (f a2 a3 b2 b3)
    | _ -> None
  else None
val ins_Pclmulqdq (imm:int) : instr_dep [inOut opXmm] [opXmm] PreserveFlags (eval_Pclmulqdq imm)

let eval_VPclmulqdq (imm:int) (src1 src2:quad32) : option quad32 =
  check_avx (eval_Pclmulqdq imm src1 src2)
val ins_VPclmulqdq (imm:int) : instr_dep [out opXmm] [opXmm; opXmm] PreserveFlags (eval_VPclmulqdq imm)

let eval_AESNI_enc (src1 src2:quad32) : option quad32 =
  if aesni_enabled then
    Some (quad32_xor (Vale.AES.AES_s.mix_columns_LE (Vale.AES.AES_s.sub_bytes (Vale.AES.AES_s.shift_rows_LE src1))) src2)
  else None
val ins_AESNI_enc : instr_dep [inOut opXmm] [opXmm] PreserveFlags eval_AESNI_enc

let eval_VAESNI_enc (src1 src2:quad32) : option quad32 = check_avx (eval_AESNI_enc src1 src2)
val ins_VAESNI_enc : instr_dep [out opXmm] [opXmm; opXmm] PreserveFlags eval_VAESNI_enc

let eval_AESNI_enc_last (src1 src2:quad32) : option quad32 =
  if aesni_enabled then
    Some (quad32_xor (Vale.AES.AES_s.sub_bytes (Vale.AES.AES_s.shift_rows_LE src1)) src2)
  else None
val ins_AESNI_enc_last : instr_dep [inOut opXmm] [opXmm] PreserveFlags eval_AESNI_enc_last

let eval_VAESNI_enc_last (src1 src2:quad32) : option quad32 = check_avx (eval_AESNI_enc_last src1 src2)
val ins_VAESNI_enc_last : instr_dep [out opXmm] [opXmm; opXmm] PreserveFlags eval_VAESNI_enc_last

let eval_AESNI_dec (dst src:quad32) : option quad32 =
  if aesni_enabled then
    Some (quad32_xor (Vale.AES.AES_s.inv_mix_columns_LE (Vale.AES.AES_s.inv_sub_bytes (Vale.AES.AES_s.inv_shift_rows_LE dst))) src)
  else None
val ins_AESNI_dec : instr_dep [inOut opXmm] [opXmm] PreserveFlags eval_AESNI_dec

let eval_AESNI_dec_last (dst src:quad32) : option quad32 =
  if aesni_enabled then
    Some (quad32_xor (Vale.AES.AES_s.inv_sub_bytes (Vale.AES.AES_s.inv_shift_rows_LE dst)) src)
  else None
val ins_AESNI_dec_last : instr_dep [inOut opXmm] [opXmm] PreserveFlags eval_AESNI_dec_last

let eval_AESNI_imc (src:quad32) : option quad32 =
  if aesni_enabled then Some (Vale.AES.AES_s.inv_mix_columns_LE src) else None
val ins_AESNI_imc : instr_dep [out opXmm] [opXmm] PreserveFlags eval_AESNI_imc

let eval_AESNI_keygen_assist (imm:nat8) (src:quad32) : option quad32 =
  if aesni_enabled then
    Some (Mkfour
      (Vale.AES.AES_s.sub_word src.lo1)
      (ixor (Vale.AES.AES_s.rot_word_LE (Vale.AES.AES_s.sub_word src.lo1)) imm)
      (Vale.AES.AES_s.sub_word src.hi3)
      (ixor (Vale.AES.AES_s.rot_word_LE (Vale.AES.AES_s.sub_word src.hi3)) imm))
  else None
val ins_AESNI_keygen_assist (imm:nat8) :
  instr_dep [out opXmm] [opXmm] PreserveFlags (eval_AESNI_keygen_assist imm)

let eval_SHA256_rnds2 (src1 src2 wk:quad32) : option quad32 =
  if sha_enabled then Some (sha256_rnds2_spec src1 src2 wk) else None
val ins_SHA256_rnds2 :
  instr_dep [inOut opXmm] [opXmm; oneXmm (OReg 0)] PreserveFlags eval_SHA256_rnds2

let eval_SHA256_msg1 (src1 src2:quad32) : option quad32 =
  if sha_enabled then Some (sha256_msg1_spec src1 src2) else None
val ins_SHA256_msg1 : instr_dep [inOut opXmm] [opXmm] PreserveFlags eval_SHA256_msg1

let eval_SHA256_msg2 (src1 src2:quad32) : option quad32 =
  if sha_enabled then Some (sha256_msg2_spec src1 src2) else None
val ins_SHA256_msg2 : instr_dep [inOut opXmm] [opXmm] PreserveFlags eval_SHA256_msg2

let eval_Ghost : option unit = Some ()
val ins_Ghost : instr_dep [] [] PreserveFlags eval_Ghost

let eval_Comment : option unit = Some ()
val ins_Comment (_:string) : instr_dep [] [] PreserveFlags eval_Comment

let eval_LargeComment : option unit = Some ()
val ins_LargeComment (_:string) : instr_dep [] [] PreserveFlags eval_LargeComment

let eval_Newline : option unit = Some ()
val ins_Newline : instr_dep [] [] PreserveFlags eval_Newline

let eval_Space : option unit = Some ()
val ins_Space (_:nat) : instr_dep [] [] PreserveFlags eval_Space
