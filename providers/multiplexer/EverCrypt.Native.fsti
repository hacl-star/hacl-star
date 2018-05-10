module EverCrypt.Native

open FStar.HyperStack.ST

/// Multiplexing support
type impl = | Hacl | Vale | OpenSSL

val sha256_impl: impl
val sha384_impl: impl
val sha512_impl: impl
val x25519_impl: impl
val aes_gcm_impl: impl

/// By default, EverCrypt calls into Hacl whenever available, and defaults to
/// OpenSSL for the algorithms that are not yet implement by HACL.
///
/// This function allows overriding this default choice.
///
/// - If no preferred implementation is passed, then `init` performs run-time
///   CPU detection, and picks the most efficient implementation. For instance, if
///   the processor supports the Intel AESNI instruction, then this will choose
///   Vale as the default provider for AES.
/// - If a preferred implementation is passed, then when use that implementation
///   whenever possible.
///
/// This function is implemented in C for CPU detection and mutation of the
/// assumed val's right above.
val init: option impl -> Stack unit (fun _ -> True) (fun h0 _ h1 -> h0 == h1)
