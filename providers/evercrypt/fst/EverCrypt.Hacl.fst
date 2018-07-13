module EverCrypt.Hacl

module T = LowStar.ToFStarBuffer

inline_for_extraction noextract
let (!!) = T.new_to_old_st

let x25519 dst secret base =
  Hacl.Curve25519.crypto_scalarmult !!dst !!secret !!base

/// AES block function

let aes128_keyExpansion k w sb =
  push_frame ();
  Crypto.Symmetric.AES128.mk_sbox sb;
  Crypto.Symmetric.AES128.keyExpansion k w sb;
  pop_frame()

let aes128_cipher cipher plain w sb = Crypto.Symmetric.AES128.cipher cipher plain w sb

let aes256_keyExpansion k w sb =
  push_frame ();
  Crypto.Symmetric.AES.mk_sbox sb;
  Crypto.Symmetric.AES.keyExpansion k w sb;
  pop_frame ()

let aes256_cipher cipher plain w sb = Crypto.Symmetric.AES.cipher cipher plain w sb

let chacha20 key iv ctr plain len cipher =
  Hacl.Chacha20.chacha20 cipher plain len key iv ctr

/// Chacha20-Poly1305

let chacha20_poly1305_encrypt c mac m m_len aad aad_len k n =
  let c: FStar.Buffer.buffer UInt8.t = !!c in
  let mac: FStar.Buffer.buffer UInt8.t = !!mac in
  let m: FStar.Buffer.buffer UInt8.t = !!m in
  let aad: FStar.Buffer.buffer UInt8.t = !!aad in
  let k: FStar.Buffer.buffer UInt8.t = !!k in
  let n: FStar.Buffer.buffer UInt8.t = !!n in
  Hacl.Chacha20Poly1305.aead_encrypt c mac m m_len aad aad_len k n

let chacha20_poly1305_decrypt m c m_len mac aad aad_len k n =
  let c: FStar.Buffer.buffer UInt8.t = !!c in
  let mac: FStar.Buffer.buffer UInt8.t = !!mac in
  let m: FStar.Buffer.buffer UInt8.t = !!m in
  let aad: FStar.Buffer.buffer UInt8.t = !!aad in
  let k: FStar.Buffer.buffer UInt8.t = !!k in
  let n: FStar.Buffer.buffer UInt8.t = !!n in
  Hacl.Chacha20Poly1305.aead_decrypt m c m_len mac aad aad_len k n
