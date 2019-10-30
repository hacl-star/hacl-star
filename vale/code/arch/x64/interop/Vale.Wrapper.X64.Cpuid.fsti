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
      ((UInt64.v ret_val) =!= 0 ==> avx_enabled) /\
      B.modifies B.loc_none h0 h1)

inline_for_extraction
val check_avx2: unit -> Stack UInt64.t
    (requires fun h0 -> True)
    (ensures fun h0 ret_val h1 ->
      ((UInt64.v ret_val) =!= 0 ==> avx2_enabled) /\
      B.modifies B.loc_none h0 h1)
