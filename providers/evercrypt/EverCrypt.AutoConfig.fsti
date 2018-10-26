(* This module is to be phased out; please use EverCrypt.AutoConfig2. *)
module EverCrypt.AutoConfig

open EverCrypt.Helpers
open FStar.HyperStack.ST

module M = LowStar.Modifies

(** Old multiplexing support, to be phased out. *)

/// Multiplexing support
type impl = | Hacl | Vale | OpenSSL | BCrypt

type cfg =
| Default
| Prefer: preferred:impl -> cfg

val sha256_impl: getter impl
val sha384_impl: getter impl
val sha512_impl: getter impl
val x25519_impl: getter impl
val random_impl: getter impl
val aes128_impl: getter impl
val aes256_impl: getter impl
val chacha20_impl: getter impl
val aes128_gcm_impl: getter impl
val aes256_gcm_impl: getter impl
val chacha20_poly1305_impl: getter impl
val dh_impl: getter impl

/// By default, EverCrypt calls into Hacl whenever available, and defaults to
/// OpenSSL for the algorithms that are not yet implemented by HACL.
///
/// This function allows overriding this default choice.
///
/// - If no preferred implementation is passed, then `init` performs run-time
///   CPU detection, and picks the most efficient implementation. For instance, if
///   the processor supports the Intel AESNI instruction, then this will choose
///   Vale as the default provider for AES.
/// - If a preferred implementation is passed, then we use that implementation
///   whenever possible.
///
/// This function is implemented in C for CPU detection and mutation of the
/// assumed val's right above.
val init: cfg -> Stack unit (fun _ -> True) (fun h0 _ h1 -> h0 == h1)
