module HACL

///
/// Curve25519
///

let hacl_curve25519_scalarmult mypublic secret basepoint =  Hacl.EC.crypto_scalarmult mypublic secret basepoint

///
/// Chacha20
///

let hacl_chacha20_init st k n = Hacl.Impl.Chacha20.init st k n
let hacl_chacha20_update output plain log st ctr = Hacl.Impl.Chacha20.update output plain log st ctr
let hacl_chacha20_update_last output plain len log st ctr = Hacl.Impl.Chacha20.update_last output plain len log st ctr
let hacl_chacha20 output plain len k n ctr = Hacl.Impl.Chacha20.chacha20 output plain len k n ctr

///
/// SHA2
///

let hacl_sha2_256_size_hash = Hacl.Hash.SHA2_256.size_hash
let hacl_sha2_384_size_hash = Hacl.Hash.SHA2_384.size_hash
let hacl_sha2_512_size_hash = Hacl.Hash.SHA2_512.size_hash

let hacl_sha2_256_size_block = Hacl.Hash.SHA2_256.size_block
let hacl_sha2_384_size_block = Hacl.Hash.SHA2_384.size_block
let hacl_sha2_512_size_block = Hacl.Hash.SHA2_512.size_block

let hacl_sha2_256_alloc () = Hacl.Hash.SHA2_256.alloc ()
let hacl_sha2_384_alloc () = Hacl.Hash.SHA2_384.alloc ()
let hacl_sha2_512_alloc () = Hacl.Hash.SHA2_512.alloc ()

let hacl_sha2_256_init state = Hacl.Hash.SHA2_256.init state
let hacl_sha2_384_init state = Hacl.Hash.SHA2_384.init state
let hacl_sha2_512_init state = Hacl.Hash.SHA2_512.init state

let hacl_sha2_256_update state data = Hacl.Hash.SHA2_256.update state data
let hacl_sha2_384_update state data = Hacl.Hash.SHA2_384.update state data
let hacl_sha2_512_update state data = Hacl.Hash.SHA2_512.update state data

let hacl_sha2_256_update_multi state data n = Hacl.Hash.SHA2_256.update_multi state data n
let hacl_sha2_384_update_multi state data n = Hacl.Hash.SHA2_384.update_multi state data n
let hacl_sha2_512_update_multi state data n = Hacl.Hash.SHA2_512.update_multi state data n

let hacl_sha2_256_update_last state data len = Hacl.Hash.SHA2_256.update_last state data len
let hacl_sha2_384_update_last state data len = Hacl.Hash.SHA2_384.update_last state data len
let hacl_sha2_512_update_last state data len = Hacl.Hash.SHA2_512.update_last state data len

let hacl_sha2_256_finish state hash = Hacl.Hash.SHA2_256.finish state hash
let hacl_sha2_384_finish state hash = Hacl.Hash.SHA2_384.finish state hash
let hacl_sha2_512_finish state hash = Hacl.Hash.SHA2_512.finish state hash

let hacl_sha2_256 output input len = Hacl.Hash.SHA2_256.hash output input len
let hacl_sha2_384 output input len = Hacl.Hash.SHA2_384.hash output input len
let hacl_sha2_512 output input len = Hacl.Hash.SHA2_512.hash output input len

///
/// HMAC
///

let hacl_hmac_sha2_256_wrap_key output key len = Hacl.HMAC.SHA2_256.wrap_key output key len
// let hacl_hmac_sha2_384_wrap_key output key len = Hacl.HMAC.SHA2_384.wrap_key output key len
// let hacl_hmac_sha2_512_wrap_key output key len = Hacl.HMAC.SHA2_512.wrap_key output key len

let hacl_hmac_sha2_256_hmac_core mac key data len = Hacl.HMAC.SHA2_256.hmac_core mac key data len
// let hacl_hmac_sha2_384_hmac_core mac key data len = Hacl.HMAC.SHA2_384.hmac_core mac key data len
// let hacl_hmac_sha2_512_hmac_core mac key data len = Hacl.HMAC.SHA2_512.hmac_core mac key data len

let hacl_hmac_sha2_256_hmac mac key keylen data datalen = Hacl.HMAC.SHA2_256.hmac mac key keylen data datalen
// let hacl_hmac_sha2_384_hmac mac key keylen data datalen = Hacl.HMAC.SHA2_384.hmac mac key keylen data datalen
// let hacl_hmac_sha2_512_hmac mac key keylen data datalen = Hacl.HMAC.SHA2_512.hmac mac key keylen data datalen

///
/// Ed25519
///

let hacl_ed25519_sign signature secret msg len = Hacl.Impl.Ed25519.Sign.sign signature secret msg len
let hacl_ed25519_verify public msg len signature = Hacl.Impl.Ed25519.Verify.verify public msg len signature
let hacl_ed25519_secret_to_public out secret = Hacl.Impl.Ed25519.SecretToPublic.secret_to_public out secret
