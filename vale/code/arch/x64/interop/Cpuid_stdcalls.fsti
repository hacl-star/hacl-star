module Cpuid_stdcalls

open X64.CPU_Features_s
open FStar.HyperStack.ST
module B = LowStar.Buffer

[@ (CCConv "stdcall") ]
val check_aesni: unit -> Stack UInt64.t
    (requires fun h0 -> True)
    (ensures fun h0 ret_val h1 -> 
      ((UInt64.v ret_val) =!= 0 ==> aesni_enabled /\ pclmulqdq_enabled) /\
      B.modifies B.loc_none h0 h1)

[@ (CCConv "stdcall") ]
val check_sha: unit -> Stack UInt64.t
    (requires fun h0 -> True)
    (ensures fun h0 ret_val h1 ->
      ((UInt64.v ret_val) =!= 0 ==> sha_enabled) /\
      B.modifies B.loc_none h0 h1)

[@ (CCConv "stdcall") ]
val check_adx_bmi2: unit -> Stack UInt64.t
    (requires fun h0 -> True)
    (ensures fun h0 ret_val h1 -> 
      ((UInt64.v ret_val) =!= 0 ==> adx_enabled /\ bmi2_enabled) /\ 
      B.modifies B.loc_none h0 h1)

[@ (CCConv "stdcall") ]
val check_avx2: unit -> Stack UInt64.t
    (requires fun h0 -> True)
    (ensures fun h0 ret_val h1 -> 
      ((UInt64.v ret_val) =!= 0 ==> avx2_enabled) /\ 
      B.modifies B.loc_none h0 h1)
