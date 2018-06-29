module EverCrypt.Hacl

let x25519 dst secret base = Hacl.Curve25519.crypto_scalarmult dst secret base

let chacha20_poly1305_encode_length lb aad_len m_len =
  Hacl.Chacha20Poly1305.encode_length lb aad_len m_len
let chacha20_poly1305_encrypt c mac m m_len aad aad_len k n =
  Hacl.Chacha20Poly1305.aead_encrypt c mac m m_len aad aad_len k n
let chacha20_poly1305_decrypt m c m_len mac aad aad_len k n =
  Hacl.Chacha20Poly1305.aead_decrypt m c m_len mac aad aad_len k n
