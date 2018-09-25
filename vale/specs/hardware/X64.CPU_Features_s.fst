module X64.CPU_Features_s

open X64.Machine_s
open Words_s

assume val aesni_enabled : bool      // CPUID.01H:ECX.AESNI[bit 25] 
assume val pclmulqdq_enabled : bool  // CPUID.01H:ECX.PCLMULQDQ[bit 1]
assume val sha_enabled : bool        // CPUID.7.0.EBX[29]


assume val cpuid (r:reg) (rax:nat64) (rcx:nat64) : nat64

assume val cpuid_features (u:unit) :
  Lemma ((forall rcx . {:pattern (cpuid Rcx 1 rcx)} (Types_s.iand (cpuid Rcx 1 rcx) (pow2_norm 25) = 1) = aesni_enabled) /\
         (forall rcx . {:pattern (cpuid Rcx 1 rcx)} (Types_s.iand (cpuid Rcx 1 rcx) (pow2_norm 1)  = 1) = pclmulqdq_enabled) /\
         (Types_s.iand (cpuid Rbx 7 0) (pow2_norm 29) = 1) = sha_enabled)
