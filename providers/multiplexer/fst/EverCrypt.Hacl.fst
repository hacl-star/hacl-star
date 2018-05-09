module EverCrypt.Hacl

let sha256_init state = Hacl.SHA2_256.init state
let sha256_update state data = Hacl.SHA2_256.update state data
let sha256_update_multi state data n = Hacl.SHA2_256.update_multi state data n
let sha256_update_last state data n = Hacl.SHA2_256.update_last state data n
let sha256_finish state data = Hacl.SHA2_256.finish state data
let sha256_hash dst src len = Hacl.SHA2_256.hash dst src len

let sha384_init state = Hacl.SHA2_384.init state
let sha384_update state data = Hacl.SHA2_384.update state data
let sha384_update_multi state data n = Hacl.SHA2_384.update_multi state data n
let sha384_update_last state data n = Hacl.SHA2_384.update_last state data n
let sha384_finish state data = Hacl.SHA2_384.finish state data
let sha384_hash dst src len = Hacl.SHA2_384.hash dst src len

let sha512_init state = Hacl.SHA2_512.init state
let sha512_update state data = Hacl.SHA2_512.update state data
let sha512_update_multi state data n = Hacl.SHA2_512.update_multi state data n
let sha512_update_last state data n = Hacl.SHA2_512.update_last state data n
let sha512_finish state data = Hacl.SHA2_512.finish state data
let sha512_hash dst src len = Hacl.SHA2_512.hash dst src len

let x25519 dst secret base = Hacl.Curve25519.crypto_scalarmult dst secret base
