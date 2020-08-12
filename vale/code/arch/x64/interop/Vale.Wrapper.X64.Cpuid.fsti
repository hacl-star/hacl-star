module Vale.Wrapper.X64.Cpuid

open FStar.Mul
open Vale.X64.CPU_Features_s
open FStar.HyperStack.ST
module B = LowStar.Buffer

inline_for_extraction
val check_aesni: unit -> Stack UInt64.t
    (requires fun h0 -> True)
    (ensures fun h0 ret_val h1 ->
      ((UInt64.v ret_val) =!= 0 ==> aesni_enabled /\ pclmulqdq_enabled) /\
      B.modifies B.loc_none h0 h1)

inline_for_extraction
val check_sha: unit -> Stack UInt64.t
    (requires fun h0 -> True)
    (ensures fun h0 ret_val h1 ->
      ((UInt64.v ret_val) =!= 0 ==> sha_enabled) /\
      B.modifies B.loc_none h0 h1)

inline_for_extraction
val check_adx_bmi2: unit -> Stack UInt64.t
    (requires fun h0 -> True)
    (ensures fun h0 ret_val h1 ->
      ((UInt64.v ret_val) =!= 0 ==> adx_enabled /\ bmi2_enabled) /\
      B.modifies B.loc_none h0 h1)

inline_for_extraction
val check_avx: unit -> Stack UInt64.t
    (requires fun h0 -> True)
    (ensures fun h0 ret_val h1 ->
      ((UInt64.v ret_val) =!= 0 ==> avx_cpuid_enabled) /\
      B.modifies B.loc_none h0 h1)

inline_for_extraction
val check_avx2: unit -> Stack UInt64.t
    (requires fun h0 -> True)
    (ensures fun h0 ret_val h1 ->
      ((UInt64.v ret_val) =!= 0 ==> avx2_cpuid_enabled) /\
      B.modifies B.loc_none h0 h1)

inline_for_extraction
val check_movbe: unit -> Stack UInt64.t
    (requires fun h0 -> True)
    (ensures fun h0 ret_val h1 ->
      ((UInt64.v ret_val) =!= 0 ==> movbe_enabled) /\
      B.modifies B.loc_none h0 h1)

inline_for_extraction
val check_sse: unit -> Stack UInt64.t
    (requires fun h0 -> True)
    (ensures fun h0 ret_val h1 ->
      ((UInt64.v ret_val) =!= 0 ==> sse_enabled) /\
      B.modifies B.loc_none h0 h1)

inline_for_extraction
val check_rdrand: unit -> Stack UInt64.t
    (requires fun h0 -> True)
    (ensures fun h0 ret_val h1 ->
      ((UInt64.v ret_val) =!= 0 ==> rdrand_enabled) /\
      B.modifies B.loc_none h0 h1)

inline_for_extraction
val check_avx512: unit -> Stack UInt64.t
    (requires fun h0 -> True)
    (ensures fun h0 ret_val h1 ->
      ((UInt64.v ret_val) =!= 0 ==> avx512_cpuid_enabled) /\
      B.modifies B.loc_none h0 h1)

inline_for_extraction
val check_osxsave: unit -> Stack UInt64.t
    (requires fun h0 -> True)
    (ensures fun h0 ret_val h1 ->
      ((UInt64.v ret_val) =!= 0 ==> osxsave_enabled) /\
      B.modifies B.loc_none h0 h1)

inline_for_extraction
val check_avx_xcr0: unit -> Stack UInt64.t
    (requires fun h0 -> osxsave_enabled)
    (ensures fun h0 ret_val h1 ->
      ((UInt64.v ret_val) =!= 0 ==> avx_xcr0) /\
      B.modifies B.loc_none h0 h1)

inline_for_extraction
val check_avx512_xcr0: unit -> Stack UInt64.t
    (requires fun h0 -> osxsave_enabled /\ avx_xcr0)
    (ensures fun h0 ret_val h1 ->
      ((UInt64.v ret_val) =!= 0 ==> avx512_xcr0) /\
      B.modifies B.loc_none h0 h1)
