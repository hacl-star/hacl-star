module EverCrypt.TargetConfig

open FStar.HyperStack.ST
module B = LowStar.Buffer

// Those functions are called on non-x64 platforms for which the feature detection
// is not covered by vale's CPUID support; therefore, we hand-write in C ourselves.
// See the hand-written evercrypt_targetconfig.h for more explanations.
val vec128_not_avx_enabled : bool
val vec256_not_avx2_enabled : bool

val has_vec128_not_avx : unit ->
  Stack bool (requires fun _ -> True)
  (ensures (fun h0 b h1 ->
    B.(modifies loc_none h0 h1) /\
    (b ==> vec128_not_avx_enabled)))

val has_vec256_not_avx2 : unit ->
  Stack bool (requires fun _ -> True)
  (ensures (fun h0 b h1 ->
    B.(modifies loc_none h0 h1) /\
    (b ==> vec256_not_avx2_enabled)))

/// A set of flags that are compiled in C as #if preprocessor statements. Branch
/// on these flags to avoid generating a reference at link-time. For instance,
/// calling CPUID is guarded by ``x64``, otherwise, compiling for an ARM
/// target, we would get a reference in the C code to a function for which we have
/// no implementation at link-time.

[@@ CIfDef ]
val compile_vale : bool

[@@ CIfDef ]
val compile_128 : bool

[@@ CIfDef ]
val compile_256 : bool

// Only for Curve25519 64
[@@ CIfDef ]
val compile_intrinsics : bool
