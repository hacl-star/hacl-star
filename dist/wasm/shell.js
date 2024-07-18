
// To be loaded by main.js
var my_js_files = ["./test.js"];
var my_modules = ["WasmSupport", "FStar", "LowStar_Endianness", "Hacl_Impl_Blake2_Constants", "Hacl_Lib", "Hacl_Hash_Blake2b", "Hacl_Hash_Blake2s", "Hacl_Hash_Blake2b_Simd256", "Hacl_Hash_Blake2s_Simd128", "Hacl_Hash_Base", "Hacl_Hash_SHA1", "Hacl_Hash_SHA2", "Hacl_HMAC", "Hacl_HMAC_Blake2s_128", "Hacl_HMAC_Blake2b_256", "Hacl_Hash_SHA3", "Hacl_Hash_SHA3_Simd256", "Hacl_Hash_MD5", "EverCrypt_TargetConfig", "EverCrypt", "Vale", "EverCrypt_Hash", "Hacl_Chacha20", "Hacl_Chacha20_Vec128_Hacl_Chacha20_Vec256", "Hacl_Salsa20", "Hacl_IntTypes_Intrinsics", "Hacl_Bignum_Base", "Hacl_Bignum", "Hacl_Bignum25519_51", "Hacl_Curve25519_51", "Hacl_MAC_Poly1305", "Hacl_AEAD_Chacha20Poly1305", "Hacl_Poly1305_128_Hacl_Poly1305_256_Hacl_Impl_Poly1305", "Hacl_AEAD_Chacha20Poly1305_Simd128", "Hacl_AEAD_Chacha20Poly1305_Simd256", "Hacl_Ed25519_PrecompTable", "Hacl_Ed25519", "Hacl_NaCl", "Hacl_P256_PrecompTable", "Hacl_P256", "Hacl_Bignum_K256", "Hacl_K256_PrecompTable", "Hacl_K256_ECDSA", "Hacl_HKDF", "Hacl_HPKE_Curve51_CP32_SHA256", "Hacl_HPKE_Curve51_CP32_SHA512", "Hacl_GenericField32", "Hacl_SHA2_Vec256", "Hacl_EC_K256", "Hacl_Bignum4096", "Hacl_Chacha20_Vec32", "Hacl_Bignum4096_32", "Hacl_HKDF_Blake2s_128", "Hacl_GenericField64", "Hacl_Bignum32", "Hacl_Bignum256_32", "Hacl_SHA2_Vec128", "Hacl_HMAC_DRBG", "Hacl_Bignum64", "Hacl_HKDF_Blake2b_256", "Hacl_EC_Ed25519", "Hacl_Bignum256"];
var my_debug = false;

if (typeof module !== "undefined")
  module.exports = {
    my_js_files: my_js_files,
    my_modules: my_modules,
    my_debug: my_debug
  }
