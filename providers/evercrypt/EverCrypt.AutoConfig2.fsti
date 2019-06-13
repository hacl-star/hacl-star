(** This module, unlike the previous attempt at autoconfig, is entirely written
  in Low* + Vale, and does not play dirty tricks with global variables. As such,
  there is no C implementation for it, only an .fst file.

  This module revolves around individual feature flags, which can be selectively
  disabled. *)
module EverCrypt.AutoConfig2

open FStar.HyperStack.ST

module B = LowStar.Buffer

(** Each flag can be queried; we cache the results in mutable global variables,
  hidden behind an abstract footprint. Calling a getter requires no reasoning
  about the abstract footprint from the client. *)

unfold
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

val wants_vale: unit ->
  Stack bool (requires fun _ -> True) (ensures fun h0 _ h1 -> B.(modifies loc_none h0 h1))
val wants_hacl: unit ->
  Stack bool (requires fun _ -> True) (ensures fun h0 _ h1 -> B.(modifies loc_none h0 h1))
val wants_openssl: unit ->
  Stack bool (requires fun _ -> True) (ensures fun h0 _ h1 -> B.(modifies loc_none h0 h1))
val wants_bcrypt: unit ->
  Stack bool (requires fun _ -> True) (ensures fun h0 _ h1 -> B.(modifies loc_none h0 h1))

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
val disable_vale: disabler
val disable_hacl: disabler
val disable_openssl: disabler
val disable_bcrypt: disabler
