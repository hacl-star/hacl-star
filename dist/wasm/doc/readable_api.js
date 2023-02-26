var HaclWasm = require('../api.js');
/**
 * Hacl bindings for Javascript using WebAssembly.
 * @module Hacl
 */

/**
 * @namespace Curve25519_51
 */
var  Curve25519_51 = {


/**
 * @param {buffer} scalar - size 32
 * @param {buffer} input - size 32
 * @return {bool}
 * @return {buffer} result - size 32
 */
ecdh: function(scalar,input,) { ecdh: HaclWasm.Curve25519_51.ecdh.apply(null, arguments) },


/**
 * @param {buffer} scalar - size 32
 * @return {buffer} result - size 32
 */
secret_to_public: function(scalar,) { secret_to_public: HaclWasm.Curve25519_51.secret_to_public.apply(null, arguments) },


/**
 * @param {buffer} scalar - size 32
 * @param {buffer} input - size 32
 * @return {buffer} result - size 32
 */
scalarmult: function(scalar,input,) { scalarmult: HaclWasm.Curve25519_51.scalarmult.apply(null, arguments) },
}
module.exports.Curve25519_51 = Curve25519_51


/**
 * @namespace Chacha20Poly1305
 */
var  Chacha20Poly1305 = {


/**
 * @param {buffer} key - size 32
 * @param {buffer} nonce - size 12
 * @param {buffer} aad - size alen
 * @param {buffer} plaintext - size len
 * @return {buffer} ciphertext - size len
 * @return {buffer} mac - size 16
 */
aead_encrypt: function(key,nonce,aad,plaintext,) { aead_encrypt: HaclWasm.Chacha20Poly1305.aead_encrypt.apply(null, arguments) },


/**
 * @param {buffer} key - size 32
 * @param {buffer} nonce - size 12
 * @param {buffer} aad - size alen
 * @param {buffer} ciphertext - size len
 * @param {buffer} mac - size 16
 * @return {uint32}
 * @return {buffer} plaintext - size len
 */
aead_decrypt: function(key,nonce,aad,ciphertext,mac,) { aead_decrypt: HaclWasm.Chacha20Poly1305.aead_decrypt.apply(null, arguments) },
}
module.exports.Chacha20Poly1305 = Chacha20Poly1305


/**
 * @namespace Ed25519
 */
var  Ed25519 = {


/**
 * @param {buffer} priv - size 32
 * @return {buffer} pub - size 32
 */
secret_to_public: function(priv,) { secret_to_public: HaclWasm.Ed25519.secret_to_public.apply(null, arguments) },


/**
 * @param {buffer} priv - size 32
 * @param {buffer} message - size len
 * @return {buffer} signature - size 64
 */
sign: function(priv,message,) { sign: HaclWasm.Ed25519.sign.apply(null, arguments) },


/**
 * @param {buffer} pub - size 32
 * @param {buffer} message - size len
 * @param {buffer} signature - size 64
 * @return {bool}
 */
verify: function(pub,message,signature,) { verify: HaclWasm.Ed25519.verify.apply(null, arguments) },
}
module.exports.Ed25519 = Ed25519


/**
 * @namespace SHA2
 */
var  SHA2 = {


/**
 * @param {buffer} input - size input_len
 * @return {buffer} hash - size 64
 */
hash_512: function(input,) { hash_512: HaclWasm.SHA2.hash_512.apply(null, arguments) },


/**
 * @param {buffer} input - size input_len
 * @return {buffer} hash - size 48
 */
hash_384: function(input,) { hash_384: HaclWasm.SHA2.hash_384.apply(null, arguments) },


/**
 * @param {buffer} input - size input_len
 * @return {buffer} hash - size 32
 */
hash_256: function(input,) { hash_256: HaclWasm.SHA2.hash_256.apply(null, arguments) },
}
module.exports.SHA2 = SHA2


/**
 * @namespace Blake2
 */
var  Blake2 = {


/**
 * @param {uint32} output_len
 * @param {buffer} data - size data_len
 * @param {buffer} key - size key_len
 * @return {buffer} output - size output_len
 */
blake2b: function(output_len,data,key,) { blake2b: HaclWasm.Blake2.blake2b.apply(null, arguments) },


/**
 * @param {uint32} output_len
 * @param {buffer} data - size data_len
 * @param {buffer} key - size key_len
 * @return {buffer} output - size output_len
 */
blake2s: function(output_len,data,key,) { blake2s: HaclWasm.Blake2.blake2s.apply(null, arguments) },
}
module.exports.Blake2 = Blake2


/**
 * @namespace SHA3
 */
var  SHA3 = {


/**
 * @param {buffer} input - size input_len
 * @return {buffer} hash - size 64
 */
hash_512: function(input,) { hash_512: HaclWasm.SHA3.hash_512.apply(null, arguments) },


/**
 * @param {buffer} input - size input_len
 * @return {buffer} hash - size 48
 */
hash_384: function(input,) { hash_384: HaclWasm.SHA3.hash_384.apply(null, arguments) },


/**
 * @param {buffer} input - size input_len
 * @return {buffer} hash - size 32
 */
hash_256: function(input,) { hash_256: HaclWasm.SHA3.hash_256.apply(null, arguments) },


/**
 * @param {buffer} input - size input_len
 * @return {buffer} hash - size 28
 */
hash_224: function(input,) { hash_224: HaclWasm.SHA3.hash_224.apply(null, arguments) },


/**
 * @param {uint32} rate
 * @param {uint32} capacity
 * @param {buffer} input - size input_len
 * @param {uint32} suffix
 * @param {uint32} output_len
 * @return {buffer} digest - size output_len
 */
keccak: function(rate,capacity,input,suffix,output_len,) { keccak: HaclWasm.SHA3.keccak.apply(null, arguments) },
}
module.exports.SHA3 = SHA3


/**
 * @namespace HMAC
 */
var  HMAC = {


/**
 * @param {buffer} key - size key_len
 * @param {buffer} data - size data_len
 * @return {buffer} tag - size 32
 */
sha256: function(key,data,) { sha256: HaclWasm.HMAC.sha256.apply(null, arguments) },


/**
 * @param {buffer} key - size key_len
 * @param {buffer} data - size data_len
 * @return {buffer} tag - size 64
 */
sha512: function(key,data,) { sha512: HaclWasm.HMAC.sha512.apply(null, arguments) },
}
module.exports.HMAC = HMAC


/**
 * @namespace HKDF
 */
var  HKDF = {


/**
 * @param {buffer} salt - size salt_len
 * @param {buffer} ikm - size ikm_len
 * @return {buffer} prk - size 32
 */
extract_sha2_256: function(salt,ikm,) { extract_sha2_256: HaclWasm.HKDF.extract_sha2_256.apply(null, arguments) },


/**
 * @param {buffer} prk - size prk_len
 * @param {buffer} info - size infolen
 * @param {uint32} len
 * @return {buffer} okm - size len
 */
expand_sha2_256: function(prk,info,len,) { expand_sha2_256: HaclWasm.HKDF.expand_sha2_256.apply(null, arguments) },
}
module.exports.HKDF = HKDF


/**
 * @namespace NaCl
 */
var  NaCl = {


/**
 * @param {buffer} m - size mlen
 * @param {buffer} n - size 24
 * @param {buffer} k - size 32
 * @return {uint32}
 * @return {buffer} c - size mlen+16
 */
secretbox_easy: function(m,n,k,) { secretbox_easy: HaclWasm.NaCl.secretbox_easy.apply(null, arguments) },


/**
 * @param {buffer} c - size clen
 * @param {buffer} n - size 24
 * @param {buffer} k - size 32
 * @return {uint32}
 * @return {buffer} m - size clen-16
 */
secretbox_open_easy: function(c,n,k,) { secretbox_open_easy: HaclWasm.NaCl.secretbox_open_easy.apply(null, arguments) },


/**
 * @param {buffer} pk - size 32
 * @param {buffer} sk - size 32
 * @return {uint32}
 * @return {buffer} k - size 32
 */
box_beforenm: function(pk,sk,) { box_beforenm: HaclWasm.NaCl.box_beforenm.apply(null, arguments) },


/**
 * @param {buffer} m - size mlen
 * @param {buffer} n - size 24
 * @param {buffer} k - size 32
 * @return {uint32}
 * @return {buffer} c - size mlen+16
 */
box_easy_afternm: function(m,n,k,) { box_easy_afternm: HaclWasm.NaCl.box_easy_afternm.apply(null, arguments) },


/**
 * @param {buffer} c - size clen
 * @param {buffer} n - size 24
 * @param {buffer} k - size 32
 * @return {uint32}
 * @return {buffer} m - size clen-16
 */
box_open_easy_afternm: function(c,n,k,) { box_open_easy_afternm: HaclWasm.NaCl.box_open_easy_afternm.apply(null, arguments) },


/**
 * @param {buffer} m - size mlen
 * @param {buffer} n - size 24
 * @param {buffer} k - size 32
 * @return {uint32}
 * @return {buffer} c - size mlen
 * @return {buffer} tag - size 16
 */
box_detached_afternm: function(m,n,k,) { box_detached_afternm: HaclWasm.NaCl.box_detached_afternm.apply(null, arguments) },


/**
 * @param {buffer} c - size mlen
 * @param {buffer} tag - size 16
 * @param {buffer} n - size 24
 * @param {buffer} k - size 32
 * @return {uint32}
 * @return {buffer} m - size mlen
 */
box_open_detached_afternm: function(c,tag,n,k,) { box_open_detached_afternm: HaclWasm.NaCl.box_open_detached_afternm.apply(null, arguments) },
}
module.exports.NaCl = NaCl


/**
 * @namespace K256
 */
var  K256 = {


/**
 * @param {buffer} msgHash - size 32
 * @param {buffer} private_key - size 32
 * @param {buffer} nonce - size 32
 * @return {bool}
 * @return {buffer} signature - size 64
 */
ecdsa_sign_hashed_msg: function(msgHash,private_key,nonce,) { ecdsa_sign_hashed_msg: HaclWasm.K256.ecdsa_sign_hashed_msg.apply(null, arguments) },


/**
 * @param {buffer} m - size 32
 * @param {buffer} public_key - size 64
 * @param {buffer} signature - size 64
 * @return {bool}
 */
ecdsa_verify_hashed_msg: function(m,public_key,signature,) { ecdsa_verify_hashed_msg: HaclWasm.K256.ecdsa_verify_hashed_msg.apply(null, arguments) },


/**
 * @param {buffer} msgHash - size 32
 * @param {buffer} private_key - size 32
 * @param {buffer} nonce - size 32
 * @return {bool}
 * @return {buffer} signature - size 64
 */
secp256k1_ecdsa_sign_hashed_msg: function(msgHash,private_key,nonce,) { secp256k1_ecdsa_sign_hashed_msg: HaclWasm.K256.secp256k1_ecdsa_sign_hashed_msg.apply(null, arguments) },


/**
 * @param {buffer} m - size 32
 * @param {buffer} public_key - size 64
 * @param {buffer} signature - size 64
 * @return {bool}
 */
secp256k1_ecdsa_verify_hashed_msg: function(m,public_key,signature,) { secp256k1_ecdsa_verify_hashed_msg: HaclWasm.K256.secp256k1_ecdsa_verify_hashed_msg.apply(null, arguments) },


/**
 * @param {buffer} signature - size 64
 * @return {bool}
 */
secp256k1_ecdsa_signature_normalize: function(signature,) { secp256k1_ecdsa_signature_normalize: HaclWasm.K256.secp256k1_ecdsa_signature_normalize.apply(null, arguments) },


/**
 * @param {buffer} signature - size 64
 * @return {bool}
 */
secp256k1_ecdsa_is_signature_normalized: function(signature,) { secp256k1_ecdsa_is_signature_normalized: HaclWasm.K256.secp256k1_ecdsa_is_signature_normalized.apply(null, arguments) },


/**
 * @param {buffer} pk - size 65
 * @return {bool}
 * @return {buffer} pk_raw - size 64
 */
uncompressed_to_raw: function(pk,) { uncompressed_to_raw: HaclWasm.K256.uncompressed_to_raw.apply(null, arguments) },


/**
 * @param {buffer} pk_raw - size 64
 * @return {buffer} pk - size 65
 */
uncompressed_from_raw: function(pk_raw,) { uncompressed_from_raw: HaclWasm.K256.uncompressed_from_raw.apply(null, arguments) },


/**
 * @param {buffer} pk - size 33
 * @return {bool}
 * @return {buffer} pk_raw - size 64
 */
compressed_to_raw: function(pk,) { compressed_to_raw: HaclWasm.K256.compressed_to_raw.apply(null, arguments) },


/**
 * @param {buffer} pk_raw - size 64
 * @return {buffer} pk - size 33
 */
compressed_from_raw: function(pk_raw,) { compressed_from_raw: HaclWasm.K256.compressed_from_raw.apply(null, arguments) },


/**
 * @param {buffer} pk - size 64
 * @return {bool}
 */
is_public_key_valid: function(pk,) { is_public_key_valid: HaclWasm.K256.is_public_key_valid.apply(null, arguments) },


/**
 * @param {buffer} private_key - size 32
 * @return {bool}
 * @return {buffer} public_key - size 64
 */
secret_to_public: function(private_key,) { secret_to_public: HaclWasm.K256.secret_to_public.apply(null, arguments) },
}
module.exports.K256 = K256


/**
 * @namespace P256
 */
var  P256 = {


/**
 * @param {buffer} m - size mlen
 * @param {buffer} privkey - size 32
 * @param {buffer} k - size 32
 * @return {bool}
 * @return {buffer} result - size 64
 */
ecdsa_sign_without_hash: function(m,privkey,k,) { ecdsa_sign_without_hash: HaclWasm.P256.ecdsa_sign_without_hash.apply(null, arguments) },


/**
 * @param {buffer} m - size mlen
 * @param {buffer} pubkey - size 64
 * @param {buffer} r - size 32
 * @param {buffer} s - size 32
 * @return {bool}
 */
ecdsa_verif_without_hash: function(m,pubkey,r,s,) { ecdsa_verif_without_hash: HaclWasm.P256.ecdsa_verif_without_hash.apply(null, arguments) },


/**
 * @param {buffer} m - size mlen
 * @param {buffer} privkey - size 32
 * @param {buffer} k - size 32
 * @return {bool}
 * @return {buffer} result - size 64
 */
ecdsa_sign_sha2: function(m,privkey,k,) { ecdsa_sign_sha2: HaclWasm.P256.ecdsa_sign_sha2.apply(null, arguments) },


/**
 * @param {buffer} m - size mlen
 * @param {buffer} pubkey - size 64
 * @param {buffer} r - size 32
 * @param {buffer} s - size 32
 * @return {bool}
 */
ecdsa_verif_sha2: function(m,pubkey,r,s,) { ecdsa_verif_sha2: HaclWasm.P256.ecdsa_verif_sha2.apply(null, arguments) },


/**
 * @param {buffer} pubKey - size 64
 * @return {bool}
 */
validate_public_key: function(pubKey,) { validate_public_key: HaclWasm.P256.validate_public_key.apply(null, arguments) },


/**
 * @param {buffer} b - size 65
 * @return {bool}
 * @return {buffer} result - size 64
 */
uncompressed_to_raw: function(b,) { uncompressed_to_raw: HaclWasm.P256.uncompressed_to_raw.apply(null, arguments) },


/**
 * @param {buffer} b - size 33
 * @return {bool}
 * @return {buffer} result - size 64
 */
compressed_to_raw: function(b,) { compressed_to_raw: HaclWasm.P256.compressed_to_raw.apply(null, arguments) },


/**
 * @param {buffer} b - size 64
 * @return {buffer} result - size 65
 */
raw_to_uncompressed: function(b,) { raw_to_uncompressed: HaclWasm.P256.raw_to_uncompressed.apply(null, arguments) },


/**
 * @param {buffer} b - size 64
 * @return {buffer} result - size 33
 */
raw_to_compressed: function(b,) { raw_to_compressed: HaclWasm.P256.raw_to_compressed.apply(null, arguments) },


/**
 * @param {buffer} scalar - size 32
 * @return {bool}
 * @return {buffer} result - size 64
 */
dh_initiator: function(scalar,) { dh_initiator: HaclWasm.P256.dh_initiator.apply(null, arguments) },


/**
 * @param {buffer} pubKey - size 64
 * @param {buffer} scalar - size 32
 * @return {bool}
 * @return {buffer} result - size 64
 */
dh_responder: function(pubKey,scalar,) { dh_responder: HaclWasm.P256.dh_responder.apply(null, arguments) },


/**
 * @param {buffer} pubKey - size 32
 * @return {bool}
 */
validate_private_key: function(pubKey,) { validate_private_key: HaclWasm.P256.validate_private_key.apply(null, arguments) },
}
module.exports.P256 = P256


/**
 * @namespace Bignum_64
 */
var  Bignum_64 = {


/**
 * @param {buffer(uint64)} a
 * @param {buffer(uint64)} b
 * @return {uint64}
 * @return {buffer(uint64)} out
 */
add: function(a,b,) { add: HaclWasm.Bignum_64.add.apply(null, arguments) },


/**
 * @param {buffer(uint64)} n
 * @param {buffer(uint64)} a
 * @param {buffer(uint64)} b
 * @return {buffer(uint64)} out
 */
add_mod: function(n,a,b,) { add_mod: HaclWasm.Bignum_64.add_mod.apply(null, arguments) },


/**
 * @param {buffer(uint64)} a
 * @param {buffer(uint64)} b
 * @return {uint64}
 * @return {buffer(uint64)} out
 */
sub: function(a,b,) { sub: HaclWasm.Bignum_64.sub.apply(null, arguments) },


/**
 * @param {buffer(uint64)} n
 * @param {buffer(uint64)} a
 * @param {buffer(uint64)} b
 * @return {buffer(uint64)} out
 */
sub_mod: function(n,a,b,) { sub_mod: HaclWasm.Bignum_64.sub_mod.apply(null, arguments) },


/**
 * @param {buffer(uint64)} a
 * @param {buffer(uint64)} b
 * @return {buffer(uint64)} out
 */
mul: function(a,b,) { mul: HaclWasm.Bignum_64.mul.apply(null, arguments) },


/**
 * @param {buffer(uint64)} a
 * @return {buffer(uint64)} out
 */
sqr: function(a,) { sqr: HaclWasm.Bignum_64.sqr.apply(null, arguments) },


/**
 * @param {buffer(uint64)} n
 * @param {buffer(uint64)} a
 * @return {buffer(uint64)} out
 */
mod: function(n,a,) { mod: HaclWasm.Bignum_64.mod.apply(null, arguments) },


/**
 * @param {buffer(uint64)} n
 * @param {buffer(uint64)} a
 * @param {buffer(uint64)} b
 * @return {buffer(uint64)} out
 */
mod_exp_consttime: function(n,a,b,) { mod_exp_consttime: HaclWasm.Bignum_64.mod_exp_consttime.apply(null, arguments) },


/**
 * @param {buffer(uint64)} n
 * @param {buffer(uint64)} a
 * @param {buffer(uint64)} b
 * @return {buffer(uint64)} out
 */
mod_exp_vartime: function(n,a,b,) { mod_exp_vartime: HaclWasm.Bignum_64.mod_exp_vartime.apply(null, arguments) },


/**
 * @param {buffer(uint64)} n
 * @param {buffer(uint64)} a
 * @return {buffer(uint64)} out
 */
mod_inv_prime_vartime: function(n,a,) { mod_inv_prime_vartime: HaclWasm.Bignum_64.mod_inv_prime_vartime.apply(null, arguments) },


/**
 * @param {buffer(uint64)} limbs
 * @return {Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64}
 */
mont_ctx_init: function(limbs,) { mont_ctx_init: HaclWasm.Bignum_64.mont_ctx_init.apply(null, arguments) },


/**
 * @param {Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64} ctx
 * @param {buffer(uint64)} a
 * @return {buffer(uint64)} out
 */
mod_precomp: function(ctx,a,) { mod_precomp: HaclWasm.Bignum_64.mod_precomp.apply(null, arguments) },


/**
 * @param {Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64} ctx
 * @param {buffer(uint64)} a
 * @param {buffer(uint64)} b
 * @return {buffer(uint64)} out
 */
mod_exp_vartime_precomp: function(ctx,a,b,) { mod_exp_vartime_precomp: HaclWasm.Bignum_64.mod_exp_vartime_precomp.apply(null, arguments) },


/**
 * @param {Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64} ctx
 * @param {buffer(uint64)} a
 * @param {buffer(uint64)} b
 * @return {buffer(uint64)} out
 */
mod_exp_consttime_precomp: function(ctx,a,b,) { mod_exp_consttime_precomp: HaclWasm.Bignum_64.mod_exp_consttime_precomp.apply(null, arguments) },


/**
 * @param {Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64} ctx
 * @param {buffer(uint64)} a
 * @return {buffer(uint64)} out
 */
mod_inv_prime_vartime_precomp: function(ctx,a,) { mod_inv_prime_vartime_precomp: HaclWasm.Bignum_64.mod_inv_prime_vartime_precomp.apply(null, arguments) },


/**
 * @param {buffer} bytes - size len
 * @return {buffer(uint64)}
 */
new_bn_from_bytes_le: function(bytes,) { new_bn_from_bytes_le: HaclWasm.Bignum_64.new_bn_from_bytes_le.apply(null, arguments) },


/**
 * @param {buffer(uint64)} b
 * @return {buffer} out - size len
 */
bn_to_bytes_le: function(b,) { bn_to_bytes_le: HaclWasm.Bignum_64.bn_to_bytes_le.apply(null, arguments) },


/**
 * @param {buffer} bytes - size len
 * @return {buffer(uint64)}
 */
new_bn_from_bytes_be: function(bytes,) { new_bn_from_bytes_be: HaclWasm.Bignum_64.new_bn_from_bytes_be.apply(null, arguments) },


/**
 * @param {buffer(uint64)} b
 * @return {buffer} out - size len
 */
bn_to_bytes_be: function(b,) { bn_to_bytes_be: HaclWasm.Bignum_64.bn_to_bytes_be.apply(null, arguments) },


/**
 * @param {buffer(uint64)} a
 * @param {buffer(uint64)} b
 * @return {uint64}
 */
lt_mask: function(a,b,) { lt_mask: HaclWasm.Bignum_64.lt_mask.apply(null, arguments) },


/**
 * @param {buffer(uint64)} a
 * @param {buffer(uint64)} b
 * @return {uint64}
 */
eq_mask: function(a,b,) { eq_mask: HaclWasm.Bignum_64.eq_mask.apply(null, arguments) },
}
module.exports.Bignum_64 = Bignum_64


/**
 * @namespace Bignum_Montgomery_64
 */
var  Bignum_Montgomery_64 = {


/**
 * @param {buffer(uint64)} limbs
 * @return {bool}
 */
field_modulus_check: function(limbs,) { field_modulus_check: HaclWasm.Bignum_Montgomery_64.field_modulus_check.apply(null, arguments) },


/**
 * @param {Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64} ctx
 * @return {uint32}
 */
field_get_len: function(ctx,) { field_get_len: HaclWasm.Bignum_Montgomery_64.field_get_len.apply(null, arguments) },


/**
 * @param {buffer(uint64)} limbs
 * @return {Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64}
 */
field_init: function(limbs,) { field_init: HaclWasm.Bignum_Montgomery_64.field_init.apply(null, arguments) },


/**
 * @param {Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64} ctx
 * @param {buffer(uint64)} a
 * @return {buffer(uint64)} aM
 */
to_field: function(ctx,a,) { to_field: HaclWasm.Bignum_Montgomery_64.to_field.apply(null, arguments) },


/**
 * @param {Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64} ctx
 * @param {buffer(uint64)} aM
 * @return {buffer(uint64)} a
 */
from_field: function(ctx,aM,) { from_field: HaclWasm.Bignum_Montgomery_64.from_field.apply(null, arguments) },


/**
 * @param {Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64} ctx
 * @param {buffer(uint64)} a
 * @param {buffer(uint64)} b
 * @return {buffer(uint64)} out
 */
mul: function(ctx,a,b,) { mul: HaclWasm.Bignum_Montgomery_64.mul.apply(null, arguments) },


/**
 * @param {Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64} ctx
 * @param {buffer(uint64)} a
 * @param {buffer(uint64)} b
 * @return {buffer(uint64)} out
 */
add: function(ctx,a,b,) { add: HaclWasm.Bignum_Montgomery_64.add.apply(null, arguments) },


/**
 * @param {Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64} ctx
 * @param {buffer(uint64)} a
 * @param {buffer(uint64)} b
 * @return {buffer(uint64)} out
 */
sub: function(ctx,a,b,) { sub: HaclWasm.Bignum_Montgomery_64.sub.apply(null, arguments) },


/**
 * @param {Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64} ctx
 * @param {buffer(uint64)} a
 * @return {buffer(uint64)} out
 */
sqr: function(ctx,a,) { sqr: HaclWasm.Bignum_Montgomery_64.sqr.apply(null, arguments) },


/**
 * @param {Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64} ctx
 * @param {buffer(uint64)} a
 * @return {buffer(uint64)} out
 */
inverse: function(ctx,a,) { inverse: HaclWasm.Bignum_Montgomery_64.inverse.apply(null, arguments) },


/**
 * @param {Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64} ctx
 * @param {buffer(uint64)} a
 * @param {buffer(uint64)} b
 * @return {buffer(uint64)} out
 */
exp_consttime: function(ctx,a,b,) { exp_consttime: HaclWasm.Bignum_Montgomery_64.exp_consttime.apply(null, arguments) },


/**
 * @param {Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64} ctx
 * @param {buffer(uint64)} a
 * @param {buffer(uint64)} b
 * @return {buffer(uint64)} out
 */
exp_vartime: function(ctx,a,b,) { exp_vartime: HaclWasm.Bignum_Montgomery_64.exp_vartime.apply(null, arguments) },
}
module.exports.Bignum_Montgomery_64 = Bignum_Montgomery_64


/**
 * @namespace EverCrypt_Hash
 */
var  EverCrypt_Hash = {


/**
 * @param {uint32} hash_alg
 * @return {uint32}
 */
hash_len: function(hash_alg,) { hash_len: HaclWasm.EverCrypt_Hash.hash_len.apply(null, arguments) },


/**
 * @param {uint32} hash_alg
 * @param {buffer} input - size input_len
 * @return {buffer} hash - size EverCrypt_Hash.hash_len(hash_alg)
 */
hash: function(hash_alg,input,) { hash: HaclWasm.EverCrypt_Hash.hash.apply(null, arguments) },


/**
 * @param {EverCrypt_Hash_Incremental_hash_state} state
 * @return {uint32}
 */
alg_of_state: function(state,) { alg_of_state: HaclWasm.EverCrypt_Hash.alg_of_state.apply(null, arguments) },


/**
 * @param {uint32} hash_alg
 * @return {EverCrypt_Hash_Incremental_hash_state}
 */
create: function(hash_alg,) { create: HaclWasm.EverCrypt_Hash.create.apply(null, arguments) },


/**
 * @param {EverCrypt_Hash_Incremental_hash_state} state
 * @param {buffer} data - size len
 * @return {uint32}
 * @return {EverCrypt_Hash_Incremental_hash_state} state
 */
update: function(state,data,) { update: HaclWasm.EverCrypt_Hash.update.apply(null, arguments) },


/**
 * @param {EverCrypt_Hash_Incremental_hash_state} state
 * @return {buffer} hash - size EverCrypt_Hash.hash_len(EverCrypt_Hash.alg_of_state(state))
 */
finish: function(state,) { finish: HaclWasm.EverCrypt_Hash.finish.apply(null, arguments) },
}
module.exports.EverCrypt_Hash = EverCrypt_Hash
