module X64.Instructions_s
friend X64.Instruction_s // We're part of the trusted specification, so we can friend Instruction_s

let ins_Mov64 = make_ins (fun dst src -> print_s "mov" [P64 dst; P64 src])

let ins_MovBe64 = make_ins (fun dst src -> print_s "movbe" [P64 dst; P64 src])

let ins_Cmovc64 = make_ins (fun dst src -> print_s "cmovc" [P64 dst; P64 src])

let ins_Add64 = make_ins (fun dst src -> print_s "add" [P64 dst; P64 src])

let ins_AddLea64 =
  make_ins (fun dst src1 src2 ->
    let m =
      match (src1, src2) with
      | (OReg r1, OConst i2) -> MReg r1 i2
      | (OReg r1, OReg r2) -> MIndex r1 1 r2 0
      | _ -> MConst pow2_128 // Shouldn't hit this, but if we do, assembler will complain
      in
    // TODO: what's the right suffix here?
    // print_s "lea" [P64 dst; P64 (OMem m)])
    print "lea" [P64 dst; P64 (OMem m)])

let ins_AddCarry64 = make_ins (fun dst src -> print_s "adc" [P64 dst; P64 src])

let ins_Adcx64 = make_ins (fun dst src -> print_s "adcx" [P64 dst; P64 src])

let ins_Adox64 = make_ins (fun dst src -> print_s "adox" [P64 dst; P64 src])

let ins_Sub64 = make_ins (fun dst src -> print_s "sub" [P64 dst; P64 src])

let ins_Sbb64 = make_ins (fun dst src -> print_s "sbb" [P64 dst; P64 src])

let ins_Mul64 = make_ins (fun src -> print_s "mul" [P64 src])

let ins_Mulx64 =
  make_ins (fun dst_hi dst_lo src -> print_s "mulx" [P64 dst_hi; P64 dst_lo; P64 src])

let ins_IMul64 = make_ins (fun dst src -> print_s "imul" [P64 dst; P64 src])

let ins_And64 = make_ins (fun dst src -> print_s "and" [P64 dst; P64 src])

let ins_Xor64 = make_ins (fun dst src -> print_s "xor" [P64 dst; P64 src])

let ins_Shr64 = make_ins (fun dst amt -> print_s "shr" [P64 dst; PShift amt])

let ins_Shl64 = make_ins (fun dst amt -> print_s "shl" [P64 dst; PShift amt])

let ins_Cpuid = make_ins (print "cpuid" [])

let ins_Pxor = make_ins (fun dst src -> print "pxor" [PXmm dst; PXmm src])

let ins_Pand = make_ins (fun dst src -> print "pand" [PXmm dst; PXmm src])

let ins_Paddd = make_ins (fun dst src -> print "paddd" [PXmm dst; PXmm src])
let ins_VPaddd = make_ins (fun dst src1 src2 -> print "vpaddd" [PXmm dst; PXmm src1; PXmm src2])

let ins_Pslld amt = make_ins (fun dst -> print "pslld" [PXmm dst; PImm amt])

let ins_Psrld amt = make_ins (fun dst -> print "psrld" [PXmm dst; PImm amt])

let ins_Psrldq amt = make_ins (fun dst -> print "psrldq" [PXmm dst; PImm amt])

let ins_Palignr amount =
  make_ins (fun dst src -> print "palignr" [PXmm dst; PXmm src; PImm amount])
let ins_VPalignr amount =
  make_ins (fun dst src1 src2 -> print "vpalignr" [PXmm dst; PXmm src1; PXmm src2; PImm amount])

let ins_Shufpd permutation =
  make_ins (fun dst src -> print "shufpd" [PXmm dst; PXmm src; PImm permutation])
let ins_VShufpd permutation =
  make_ins (fun dst src1 src2 -> print "vshufpd" [PXmm dst; PXmm src1; PXmm src2; PImm permutation])

let ins_Pshufb = make_ins (fun dst src -> print "pshufb" [PXmm dst; PXmm src])
let ins_VPshufb = make_ins (fun dst src1 src2 -> print "vpshufb" [PXmm dst; PXmm src1; PXmm src2])

let ins_Pshufd permutation =
  make_ins (fun dst src -> print "pshufd" [PXmm dst; PXmm src; PImm permutation])

let ins_Pcmpeqd = make_ins (fun dst src -> print "pcmpeqd" [PXmm dst; PXmm src])

let ins_Pextrq index = make_ins (fun dst src -> print "pextrq" [P64 dst; PXmm src; PImm index])

let ins_Pinsrd index = make_ins (fun dst src -> print "pinsrd" [PXmm dst; P32 src; PImm index])

let ins_Pinsrq index = make_ins (fun dst src -> print "pinsrq" [PXmm dst; P64 src; PImm index])

let ins_VPslldq count = make_ins (fun dst src -> print "vpslldq" [PXmm dst; PXmm src; PImm count])

let ins_VPsrldq count = make_ins (fun dst src -> print "vpsrldq" [PXmm dst; PXmm src; PImm count])

let ins_Pclmulqdq imm = make_ins (fun dst src -> print "pclmulqdq" [PXmm dst; PXmm src; PImm imm])
let ins_VPclmulqdq imm =
  make_ins (fun dst src1 src2 -> print "vpclmulqdq" [PXmm dst; PXmm src1; PXmm src2; PImm imm])  

let ins_AESNI_enc = make_ins (fun dst src -> print "aesenc" [PXmm dst; PXmm src])
let ins_VAESNI_enc =
  make_ins (fun dst src1 src2 -> print "vaesenc" [PXmm dst; PXmm src1; PXmm src2])

let ins_AESNI_enc_last = make_ins (fun dst src -> print "aesenclast" [PXmm dst; PXmm src])
let ins_VAESNI_enc_last =
  make_ins (fun dst src1 src2 -> print "vaesenclast"[PXmm dst; PXmm src1; PXmm src2])

let ins_AESNI_dec = make_ins (fun dst src -> print "aesdec" [PXmm dst; PXmm src])

let ins_AESNI_dec_last = make_ins (fun dst src -> print "aesdeclast" [PXmm dst; PXmm src])

let ins_AESNI_imc = make_ins (fun dst src -> print "aesimc" [PXmm dst; PXmm src])

let ins_AESNI_keygen_assist imm =
  make_ins (fun dst src -> print "aeskeygenassist" [PXmm dst; PXmm src; PImm imm])

let ins_SHA256_rnds2 =
  make_ins (fun dst src -> Print "sha256rnds2" PrintPSha256rnds2 [PXmm dst; PXmm src])

let ins_SHA256_msg1 = make_ins (fun dst src -> print "sha256msg1" [PXmm dst; PXmm src])

let ins_SHA256_msg2 = make_ins (fun dst src -> print "sha256msg2" [PXmm dst; PXmm src])
