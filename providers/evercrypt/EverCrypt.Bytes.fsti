module EverCrypt.Bytes

let lbytes = FStar.Bytes.lbytes
let bytes  = FStar.Bytes.bytes

/// TODO: bring this to be on-par with EverCrypt.fsti

val x25519: secret:lbytes 32 -> base:lbytes 32 -> lbytes 32

/// 2018.05.24 SZ: Defining a bespoke type so that its definition doesn't conflict
/// with a monomorphized definition in any other module
type cipher_tag = {
  cipher: bytes;
  tag:    lbytes 16
}

val chacha20_poly1305_encrypt: m:bytes -> aad:bytes -> k:lbytes 32 -> n:lbytes 12
  -> cipher_tag

type maybe_plaintext =
| Error
| Correct of bytes

val chacha20_poly1305_decrypt: c:bytes -> tag:lbytes 16 -> aad:bytes
  -> k:lbytes 32 -> n:lbytes 12 -> maybe_plaintext
