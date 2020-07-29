module Vale.X64.CPU_Features_s

open FStar.Mul
open Vale.X64.Machine_s
open Vale.Def.Words_s

(* CPUID *)

assume val aesni_enabled : bool      // CPUID.01H:ECX.AESNI[bit 25]
assume val avx_cpuid_enabled : bool        // CPUID.01H:ECX.AVX[bit 28]
assume val pclmulqdq_enabled : bool  // CPUID.01H:ECX.PCLMULQDQ[bit 1]
assume val avx2_cpuid_enabled : bool       // CPUID.7.0.EBX[5]
assume val bmi2_enabled : bool       // CPUID.7.0.EBX[8]
assume val avx512f_enabled : bool    // CPUID.7.0.EBX[16]
assume val avx512dq_enabled : bool   // CPUID.7.0.EBX[17]
assume val adx_enabled : bool        // CPUID.7.0.EBX[19]
assume val sha_enabled : bool        // CPUID.7.0.EBX[29]
assume val avx512bw_enabled : bool   // CPUID.7.0.EBX[30]
assume val avx512vl_enabled : bool   // CPUID.7.0.EBX[31]
assume val sse2_enabled : bool       // CPUID.01H:EDX.SSE2[bit 26]
assume val ssse3_enabled : bool      // CPUID.01H:ECX.SSSE3[bit 9]
assume val sse4_1_enabled : bool     // CPUID.01H:ECX.SSE4.1[bit 19]
assume val movbe_enabled : bool      // CPUID.01H.ECX.MOVBE[bit 22]
assume val osxsave_enabled : bool    // CPUID.01H.ECX.OSXSAVE[bit 27]
assume val rdrand_enabled : bool     // CPUID.01H.ECX.RDRAND[bit 30] = 0


let sse_enabled : bool = sse2_enabled && ssse3_enabled && sse4_1_enabled

let avx512_cpuid_enabled : bool =
  avx512f_enabled && avx512dq_enabled && avx512bw_enabled && avx512vl_enabled

assume val cpuid (r:reg_64) (rax:nat64) (rcx:nat64) : nat64

assume val cpuid_features (u:unit) :
  Lemma ((forall rcx . {:pattern (cpuid rRcx 1 rcx)} (Vale.Def.Types_s.iand (cpuid rRcx 1 rcx) (pow2_norm 25) > 0) = aesni_enabled) /\
         (forall rcx . {:pattern (cpuid rRcx 1 rcx)} (Vale.Def.Types_s.iand (cpuid rRcx 1 rcx) (pow2_norm 28) > 0) = avx_cpuid_enabled) /\
         (forall rcx . {:pattern (cpuid rRcx 1 rcx)} (Vale.Def.Types_s.iand (cpuid rRcx 1 rcx) (pow2_norm 1)  > 0) = pclmulqdq_enabled) /\
         (forall rcx . {:pattern (cpuid rRdx 1 rcx)} (Vale.Def.Types_s.iand (cpuid rRdx 1 rcx) (pow2_norm 26)  > 0) = sse2_enabled) /\
         (forall rcx . {:pattern (cpuid rRcx 1 rcx)} (Vale.Def.Types_s.iand (cpuid rRcx 1 rcx) (pow2_norm 9)  > 0) = ssse3_enabled) /\
         (forall rcx . {:pattern (cpuid rRcx 1 rcx)} (Vale.Def.Types_s.iand (cpuid rRcx 1 rcx) (pow2_norm 19)  > 0) = sse4_1_enabled) /\
         (forall rcx . {:pattern (cpuid rRcx 1 rcx)} (Vale.Def.Types_s.iand (cpuid rRcx 1 rcx) (pow2_norm 22)  > 0) = movbe_enabled) /\
         (forall rcx . {:pattern (cpuid rRcx 1 rcx)} (Vale.Def.Types_s.iand (cpuid rRcx 1 rcx) (pow2_norm 27)  > 0) = osxsave_enabled) /\
         (forall rcx . {:pattern (cpuid rRcx 1 rcx)} (Vale.Def.Types_s.iand (cpuid rRcx 1 rcx) (pow2_norm 30)  > 0) = rdrand_enabled) /\
         (Vale.Def.Types_s.iand (cpuid rRbx 7 0) (pow2_norm  5) > 0) = avx2_cpuid_enabled /\
         (Vale.Def.Types_s.iand (cpuid rRbx 7 0) (pow2_norm  8) > 0) = bmi2_enabled /\
         (Vale.Def.Types_s.iand (cpuid rRbx 7 0) (pow2_norm 16) > 0) = avx512f_enabled /\
         (Vale.Def.Types_s.iand (cpuid rRbx 7 0) (pow2_norm 17) > 0) = avx512dq_enabled /\
         (Vale.Def.Types_s.iand (cpuid rRbx 7 0) (pow2_norm 19) > 0) = adx_enabled /\
         (Vale.Def.Types_s.iand (cpuid rRbx 7 0) (pow2_norm 29) > 0) = sha_enabled /\
         (Vale.Def.Types_s.iand (cpuid rRbx 7 0) (pow2_norm 30) > 0) = avx512bw_enabled /\
         (Vale.Def.Types_s.iand (cpuid rRbx 7 0) (pow2_norm 31) > 0) = avx512vl_enabled
       )

(* Extended Control Registers *)

assume val sse_xcr0_enabled : bool       // Bit 1
assume val avx_xcr0_enabled : bool       // Bit 2
assume val opmask_xcr0_enabled : bool    // Bit 5
assume val zmm_hi256_xcr0_enabled : bool // Bit 6
assume val hi16_zmm_xcr0_enabled : bool  // Bit 7

assume val xgetbv (r:reg_64) (rcx:nat64) : nat64

assume val xgetbv_features (u:unit) :
  Lemma ((Vale.Def.Types_s.iand (xgetbv rRax 0) (pow2_norm 1) > 0) = sse_xcr0_enabled /\
         (Vale.Def.Types_s.iand (xgetbv rRax 0) (pow2_norm 2) > 0) = avx_xcr0_enabled /\ 
         (Vale.Def.Types_s.iand (xgetbv rRax 0) (pow2_norm 5) > 0) = opmask_xcr0_enabled /\ 
         (Vale.Def.Types_s.iand (xgetbv rRax 0) (pow2_norm 6) > 0) = zmm_hi256_xcr0_enabled /\ 
         (Vale.Def.Types_s.iand (xgetbv rRax 0) (pow2_norm 7) > 0) = hi16_zmm_xcr0_enabled
        ) 

let avx_xcr0 : bool = sse_xcr0_enabled && avx_xcr0_enabled

let avx512_xcr0 : bool =
  avx_xcr0_enabled && opmask_xcr0_enabled && zmm_hi256_xcr0_enabled && hi16_zmm_xcr0_enabled


(* Full AVX detection *)

let avx_enabled : bool = avx_cpuid_enabled && avx_xcr0
let avx2_enabled : bool = avx2_cpuid_enabled && avx_xcr0
let avx512_enabled : bool = avx512_cpuid_enabled && avx512_xcr0

