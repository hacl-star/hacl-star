module EverCrypt.Bytes

let lbytes = FStar.Bytes.lbytes

/// TODO: bring this to be on-par with EverCrypt.fsti

val x25519: secret:lbytes 32 -> base:lbytes 32 -> lbytes 32

val chacha20_poly1305_encrypt: m:lbytes 32 -> aad:lbytes 32 -> k:lbytes 32 -> n:lbytes 32 ->
  lbytes 32 * lbytes 32
