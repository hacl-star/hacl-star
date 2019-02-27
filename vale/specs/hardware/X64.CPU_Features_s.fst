module X64.CPU_Features_s

open X64.Machine_s
open Words_s

assume val aesni_enabled : bool      // CPUID.01H:ECX.AESNI[bit 25] 
assume val avx_enabled : bool        // CPUID.01H:ECX.AESNI[bit 28] 
assume val pclmulqdq_enabled : bool  // CPUID.01H:ECX.PCLMULQDQ[bit 1]
assume val avx2_enabled : bool       // CPUID.7.0.EBX[5]
assume val bmi2_enabled : bool       // CPUID.7.0.EBX[8]
assume val adx_enabled : bool        // CPUID.7.0.EBX[19]
assume val sha_enabled : bool        // CPUID.7.0.EBX[29]


assume val cpuid (r:reg) (rax:nat64) (rcx:nat64) : nat64

assume val cpuid_features (u:unit) :
  Lemma ((forall rcx . {:pattern (cpuid Rcx 1 rcx)} (Types_s.iand (cpuid Rcx 1 rcx) (pow2_norm 25) > 0) = aesni_enabled) /\
         (forall rcx . {:pattern (cpuid Rcx 1 rcx)} (Types_s.iand (cpuid Rcx 1 rcx) (pow2_norm 28) > 0) = avx_enabled) /\
         (forall rcx . {:pattern (cpuid Rcx 1 rcx)} (Types_s.iand (cpuid Rcx 1 rcx) (pow2_norm 1)  > 0) = pclmulqdq_enabled) /\
         (Types_s.iand (cpuid Rbx 7 0) (pow2_norm  5) > 0) = avx2_enabled /\
         (Types_s.iand (cpuid Rbx 7 0) (pow2_norm  8) > 0) = bmi2_enabled /\
         (Types_s.iand (cpuid Rbx 7 0) (pow2_norm 19) > 0) = adx_enabled /\         
         (Types_s.iand (cpuid Rbx 7 0) (pow2_norm 29) > 0) = sha_enabled
         )
