module Hacl.Impl.Instantiate.AEAD

module GAE = Hacl.Impl.Generic.AEAD

(** Instantiations of Chacha20Poly1305 **)
inline_for_extraction noextract
val aead_encrypt_cp32 : GAE.aead_encrypt_st Spec.Agile.AEAD.CHACHA20_POLY1305
inline_for_extraction noextract
val aead_decrypt_cp32 : GAE.aead_decrypt_st Spec.Agile.AEAD.CHACHA20_POLY1305

inline_for_extraction noextract
val aead_encrypt_cp128 : GAE.aead_encrypt_st Spec.Agile.AEAD.CHACHA20_POLY1305
inline_for_extraction noextract
val aead_decrypt_cp128 : GAE.aead_decrypt_st Spec.Agile.AEAD.CHACHA20_POLY1305

inline_for_extraction noextract
val aead_encrypt_cp256 : GAE.aead_encrypt_st Spec.Agile.AEAD.CHACHA20_POLY1305
inline_for_extraction noextract
val aead_decrypt_cp256 : GAE.aead_decrypt_st Spec.Agile.AEAD.CHACHA20_POLY1305
