module Hacl.HPKE.Interface.AEAD

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

module S = Spec.Agile.HPKE
module AEAD = Spec.Agile.AEAD

include Hacl.HPKE.Interface.AEAD_core

(** Instantiations of Chacha20Poly1305 **)
inline_for_extraction noextract
val aead_encrypt_cp32 : aead_encrypt_st (S.Seal AEAD.CHACHA20_POLY1305)
inline_for_extraction noextract
val aead_decrypt_cp32 : aead_decrypt_st (S.Seal AEAD.CHACHA20_POLY1305)

inline_for_extraction noextract
val aead_encrypt_cp128 : aead_encrypt_st (S.Seal AEAD.CHACHA20_POLY1305)
inline_for_extraction noextract
val aead_decrypt_cp128 : aead_decrypt_st (S.Seal AEAD.CHACHA20_POLY1305)

inline_for_extraction noextract
val aead_encrypt_cp256 : aead_encrypt_st (S.Seal AEAD.CHACHA20_POLY1305)
inline_for_extraction noextract
val aead_decrypt_cp256 : aead_decrypt_st (S.Seal AEAD.CHACHA20_POLY1305)
