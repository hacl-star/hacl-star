module Spec.AES.Vale

open Spec.Agile.Cipher

let vale_cipher_alg = a: cipher_alg { a == AES128 \/ a == AES256 }

/// Vale-specific AES key expansion precomputed with powers of H. Shared between
/// CTR and GCM, hence in a separate module.
val vale_aes_expansion (a: vale_cipher_alg) (key: key a):
  Lib.ByteSequence.bytes

/// Vale-specific extended key length in the concrete representation with space
/// for other precomputer things.
val vale_xkey_length (a: vale_cipher_alg): nat
