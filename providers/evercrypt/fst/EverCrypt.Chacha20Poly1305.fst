module EverCrypt.Chacha20Poly1305

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
module Seq = Lib.Sequence
open FStar.Mul

module Spec = Spec.Chacha20Poly1305

let aead_encrypt k n aadlen aad mlen m cipher tag =
  Hacl.Impl.Chacha20Poly1305.aead_encrypt_chacha_poly k n aadlen aad mlen m cipher tag

let aead_decrypt k n aadlen aad mlen m cipher tag =
  Hacl.Impl.Chacha20Poly1305.aead_decrypt_chacha_poly k n aadlen aad mlen m cipher tag
