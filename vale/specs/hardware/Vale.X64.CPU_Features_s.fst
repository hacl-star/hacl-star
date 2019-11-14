module Vale.X64.CPU_Features_s

open FStar.Mul
open Vale.X64.Machine_s
open Vale.Def.Words_s

assume val aesni_enabled : bool      // CPUID.01H:ECX.AESNI[bit 25]
assume val avx_enabled : bool        // CPUID.01H:ECX.AVX[bit 28]
assume val pclmulqdq_enabled : bool  // CPUID.01H:ECX.PCLMULQDQ[bit 1]
assume val avx2_enabled : bool       // CPUID.7.0.EBX[5]
assume val bmi2_enabled : bool       // CPUID.7.0.EBX[8]
assume val adx_enabled : bool        // CPUID.7.0.EBX[19]
assume val sha_enabled : bool        // CPUID.7.0.EBX[29]
assume val sse2_enabled : bool       // CPUID.01H:EDX.SSE2[bit 26]
assume val ssse3_enabled : bool      // CPUID.01H:ECX.SSSE3[bit 9]
assume val sse4_1_enabled : bool     // CPUID.01H:ECX.SSE4.1[bit 19]
assume val movbe_enabled : bool      // CPUID.01H.ECX.MOVBE[bit 22]
assume val rdrand_enabled : bool     // CPUID.01H.ECX.RDRAND[bit 30] = 0

let sse_enabled : bool = sse2_enabled && ssse3_enabled && sse4_1_enabled

assume val cpuid (r:reg_64) (rax:nat64) (rcx:nat64) : nat64

assume val cpuid_features (u:unit) :
  Lemma ((forall rcx . {:pattern (cpuid rRcx 1 rcx)} (Vale.Def.Types_s.iand (cpuid rRcx 1 rcx) (pow2_norm 25) > 0) = aesni_enabled) /\
         (forall rcx . {:pattern (cpuid rRcx 1 rcx)} (Vale.Def.Types_s.iand (cpuid rRcx 1 rcx) (pow2_norm 28) > 0) = avx_enabled) /\
         (forall rcx . {:pattern (cpuid rRcx 1 rcx)} (Vale.Def.Types_s.iand (cpuid rRcx 1 rcx) (pow2_norm 1)  > 0) = pclmulqdq_enabled) /\
         (forall rcx . {:pattern (cpuid rRdx 1 rcx)} (Vale.Def.Types_s.iand (cpuid rRdx 1 rcx) (pow2_norm 26)  > 0) = sse2_enabled) /\
         (forall rcx . {:pattern (cpuid rRcx 1 rcx)} (Vale.Def.Types_s.iand (cpuid rRcx 1 rcx) (pow2_norm 9)  > 0) = ssse3_enabled) /\
         (forall rcx . {:pattern (cpuid rRcx 1 rcx)} (Vale.Def.Types_s.iand (cpuid rRcx 1 rcx) (pow2_norm 19)  > 0) = sse4_1_enabled) /\
         (forall rcx . {:pattern (cpuid rRcx 1 rcx)} (Vale.Def.Types_s.iand (cpuid rRcx 1 rcx) (pow2_norm 22)  > 0) = movbe_enabled) /\
         (forall rcx . {:pattern (cpuid rRcx 1 rcx)} (Vale.Def.Types_s.iand (cpuid rRcx 1 rcx) (pow2_norm 30)  > 0) = rdrand_enabled) /\
         (Vale.Def.Types_s.iand (cpuid rRbx 7 0) (pow2_norm  5) > 0) = avx2_enabled /\
         (Vale.Def.Types_s.iand (cpuid rRbx 7 0) (pow2_norm  8) > 0) = bmi2_enabled /\
         (Vale.Def.Types_s.iand (cpuid rRbx 7 0) (pow2_norm 19) > 0) = adx_enabled /\
         (Vale.Def.Types_s.iand (cpuid rRbx 7 0) (pow2_norm 29) > 0) = sha_enabled
         )
