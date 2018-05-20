module EverCrypt.Bytes

let lbytes = FStar.Bytes.lbytes

/// TODO: bring this to be on-par with EverCrypt.fsti

val x25519: secret:lbytes 32 -> base:lbytes 32 -> lbytes 32
