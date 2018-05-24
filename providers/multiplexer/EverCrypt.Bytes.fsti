module EverCrypt.Bytes

let lbytes = FStar.Bytes.lbytes

/// TODO: bring this to be on-par with EverCrypt.fsti

val x25519: secret:lbytes 32 -> base:lbytes 32 -> lbytes 32

/// 2018.05.24 SZ: Defining a bespoke type so that its definition doesn't conflict
/// with a monomorphized definition in any other module
type cipher_tag = {
  cipher: lbytes 32;
  tag:    lbytes 32
}

val chacha20_poly1305_encrypt: m:lbytes 32 -> aad:lbytes 32 -> k:lbytes 32 -> n:lbytes 32 ->
  cipher_tag
