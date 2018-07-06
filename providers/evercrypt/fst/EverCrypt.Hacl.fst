module EverCrypt.Hacl

module T = LowStar.ToFStarBuffer

inline_for_extraction noextract
let (!!) = T.new_to_old_st

let x25519 dst secret base =
  Hacl.Curve25519.crypto_scalarmult !!dst !!secret !!base

let chacha20_poly1305_encode_length lb aad_len m_len =
  Hacl.Chacha20Poly1305.encode_length !!lb aad_len m_len

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
