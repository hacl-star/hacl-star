module EverCrypt.TargetConfig

/// A set of flags that are compiled in C as #if preprocessor statements. Branch
/// on these flags to avoid generating a reference at link-time. For instance,
/// calling CPUID is guarded by ``x64``, otherwise, compiling for an ARM
/// target, we would get a reference in the C code to a function for which we have
/// no implementation at link-time.

let x64 = false

let x86 = true

let aarch32 = false

let aarch64 = false

let gcc = false
