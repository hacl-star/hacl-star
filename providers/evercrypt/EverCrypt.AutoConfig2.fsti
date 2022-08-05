(** This module, unlike the previous attempt at autoconfig, is entirely written
  in Low* + Vale, and does not play dirty tricks with global variables. As such,
  there is no C implementation for it, only an .fst file.

  This module revolves around individual feature flags, which can be selectively
  disabled. *)
module EverCrypt.AutoConfig2

open FStar.HyperStack.ST
open EverCrypt.TargetConfig

module B = LowStar.Buffer

(** Each flag can be queried; we cache the results in mutable global variables,
  hidden behind an abstract footprint. Calling a getter requires no reasoning
  about the abstract footprint from the client. *)

unfold
inline_for_extraction noextract
let getter (flag: bool) = unit -> Stack bool
  (requires (fun _ -> true))
  (ensures (fun h0 b h1 ->
    B.(modifies loc_none h0 h1) /\
    (b ==> flag)))

val has_shaext: getter Vale.X64.CPU_Features_s.sha_enabled
val has_aesni: getter Vale.X64.CPU_Features_s.aesni_enabled
val has_pclmulqdq: getter Vale.X64.CPU_Features_s.pclmulqdq_enabled
val has_avx2: getter Vale.X64.CPU_Features_s.avx2_enabled
val has_avx: getter Vale.X64.CPU_Features_s.avx_enabled
val has_bmi2: getter Vale.X64.CPU_Features_s.bmi2_enabled
val has_adx: getter Vale.X64.CPU_Features_s.adx_enabled
val has_sse: getter Vale.X64.CPU_Features_s.sse_enabled
val has_movbe: getter Vale.X64.CPU_Features_s.movbe_enabled
val has_rdrand: getter Vale.X64.CPU_Features_s.rdrand_enabled
(** At the moment, has_avx512 contains the AVX512_F, AVX512_DQ, AVX512_BW and AVX512_VL flags
    See Vale.X64.CPU_Features_s for more details. **)
val has_avx512: getter Vale.X64.CPU_Features_s.avx512_enabled

(** A set of functions that modify the global cached results. For this, the
  client needs to reason about the abstract footprint. *)

val fp: unit -> GTot B.loc

(* A client that needs to allocate first then call init should use recall before
  anything else; this way, the client will be able to derive disjointness of their
  allocations and of fp. *)
val recall: unit -> Stack unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 ->
    B.(loc_not_unused_in h1 `loc_includes` (fp ())) /\ h0 == h1))

(* By default, all feature flags are disabled. A client must call init to get
  meaningful results from the various has_* functions. *)
val init: unit -> Stack unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 ->
    B.modifies (fp ()) h0 h1))

inline_for_extraction
let disabler = unit -> Stack unit
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> B.(modifies (fp ()) h0 h1)))

(* In order to selectively take codepaths, a client might disable either feature
  flags, to, say, pick one Vale implementation over another. Alternatively, if the
  codepath taken does not depend on a particular feature flag (e.g. OpenSSL vs.
  BCrypt) the client can disable a provider entirely. *)
val disable_avx2: disabler
val disable_avx: disabler
val disable_bmi2: disabler
val disable_adx: disabler
val disable_shaext: disabler
val disable_aesni: disabler
val disable_pclmulqdq: disabler
val disable_sse: disabler
val disable_movbe: disabler
val disable_rdrand: disabler
val disable_avx512: disabler

(** Some predicates to dynamically guard the vectorized code *)
(* Note that those predicates don't check [EverCrypt.TargetConfig.hacl_can_compile_vec128],
 * [EverCrypt.TargetConfig.hacl_can_compile_vale], etc.
 * The reason is that the above booleans are static preconditions, checked at
 * compilation time. The F* code must thus be guard the following way (note that
 * the order of the arguments is important for syntactic reasons):
 * [> if EverCrypt.TargetConfig.hacl_can_compile_vec128 && has_vec128 ... then
 * Leading to the following C code:
 * [> #if defined(COMPILE_128)
 * [>   if has_vec128 ... { ... }
 * [> #endif
 * Note that if one forgets to guard the code with flags like
 * [EverCrypt.TargetConfig.hacl_can_compile_vec128], the code will not compile on platforms
 * not satisfying the requirements.
 *)

noextract
let vec128_enabled = Vale.X64.CPU_Features_s.avx_enabled || vec128_not_avx_enabled
noextract
let vec256_enabled = Vale.X64.CPU_Features_s.avx2_enabled || vec256_not_avx2_enabled

val has_vec128: getter vec128_enabled
val has_vec256: getter vec256_enabled
