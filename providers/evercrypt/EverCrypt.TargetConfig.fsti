module EverCrypt.TargetConfig

/// A set of constants to describe the potential target architectures.
/// We don't define an enumeration to take advantage of the [ @CMacro]
/// attribute, and so that we can write evercrypt_targetconfig.h
/// completely by hand. Also note that we don't need any of the properties
/// which would be provided by an enum in our proofs (we don't need to
/// know that, say, [target_archi_name_x86 <> target_archi_name_z]).
/// Finally, we use the prefix "target_archi_name" to make sure the generated C
/// macros don't clash with any other names, and that there is no ambiguity
/// on their meaning - e.g. without the prefix, one may think [X86] is a flag
/// and not a constant, and thus use it to guard some code working only on x86
/// with [#if defined(X86)].

[@ CMacro ]
inline_for_extraction
val target_archi_name_x86 : FStar.UInt32.t

[@ CMacro ]
inline_for_extraction
val target_archi_name_x64 : FStar.UInt32.t

[@ CMacro ]
inline_for_extraction
val target_archi_name_arm7 : FStar.UInt32.t

[@ CMacro ]
inline_for_extraction
val target_archi_name_arm8 : FStar.UInt32.t

[@ CMacro ]
inline_for_extraction
val target_archi_name_systemz : FStar.UInt32.t

[@ CMacro ]
inline_for_extraction
val target_archi_name_powerpc64 : FStar.UInt32.t

[@ CMacro ]
inline_for_extraction
val target_archi_name_unknown : FStar.UInt32.t

/// The below macro will take the value of one of the above constants,
/// and is the value used in the code. Note: in the proofs, we don't need
/// to know it takes only one of the above values (we actually never check
/// [target_archi_name_unknown].
[@ CMacro ]
inline_for_extraction
val target_archi : FStar.UInt32.t

/// A set of flags that are compiled in C as #if preprocessor statements. Branch
/// on these flags to avoid generating a reference at link-time. For instance,
/// calling CPUID is guarded by ``x64``, otherwise, compiling for an ARM
/// target, we would get a reference in the C code to a function for which we have
/// no implementation at link-time.

[@ CIfDef ]
inline_for_extraction
val compile_vale : bool

[@ CIfDef ]
inline_for_extraction
val compile_128 : bool

[@ CIfDef ]
inline_for_extraction
val compile_256 : bool

// Only for Curve25519 64
[@ CIfDef ]
inline_for_extraction
val compile_intrinsics : bool
