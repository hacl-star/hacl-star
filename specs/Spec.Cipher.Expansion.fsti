module Spec.Cipher.Expansion

open Spec.Agile.Cipher

/// This module gathers key expansion details shared between the CTR and AEAD
/// constructions.
///
/// From the perspective of Spec.Agile.CTR (and EverCrypt.CTR) and Spec.Agile.AEAD
/// (and EverCrypt.AEAD), none of the following appear in the interface:
///
/// - expanded keys, considered to be an implementation detail
/// - concrete representation of expanded keys used by Vale, which has more
///   precomputed things stored beyond the expanded key.
///
/// The interface remains until we get rid of ``friend Lib.IntTypes``.

/// This type is used at run-time by both ``EverCrypt.CTR`` and
/// ``EverCrypt.AEAD`` -- we assume that an implementation covers both CTR and
/// AEAD. It lists valid combinations, and serves as an index for concrete
/// expanded keys, which include provider-specific representation choices. This
/// type serves several purposes.
type impl =
| Hacl_CHACHA20
| Vale_AES128
| Vale_AES256

let cipher_alg_of_impl (i: impl): cipher_alg =
  match i with
  | Hacl_CHACHA20 -> CHACHA20
  | Vale_AES128 -> AES128
  | Vale_AES256 -> AES256

/// Length of an expanded key per the AES specification.
val xkey_length (a: cipher_alg): Lib.IntTypes.size_nat

let xkey a = Lib.ByteSequence.lbytes (xkey_length a)

/// Length of the concrete representation of an expanded key, for a given implementation.
val concrete_xkey_length (i: impl): Lib.IntTypes.size_nat

let concrete_xkey (i: impl) = Lib.ByteSequence.lbytes (concrete_xkey_length i)

/// Concrete key expansion, implementation-specific
val concrete_expand: i:impl -> key (cipher_alg_of_impl i) -> concrete_xkey i
