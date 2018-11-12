module Spec.AEAD


let aead_encrypt (a:algorithm) k n m aad =
  match a with
  | AEAD_AES128_GCM -> Spec.AES128_GCM.aead_encrypt k n m aad
  | AEAD_Chacha20_Poly1305 -> Spec.Chacha20Poly1305.aead_encrypt k n m aad

let aead_decrypt (a:algorithm) k n c aad =
  match a with
  | AEAD_AES128_GCM -> Spec.AES128_GCM.aead_decrypt k n c aad
  | AEAD_Chacha20_Poly1305 -> Spec.Chacha20Poly1305.aead_decrypt k n c aad
