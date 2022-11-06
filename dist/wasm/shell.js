
// To be loaded by main.js
var my_js_files = ["./test.js"];
var my_modules = ["WasmSupport", "FStar", "LowStar_Endianness", "LowStar", "Hacl_Impl_Blake2_Constants", "Hacl_Hash_Base", "Hacl_Hash_Blake2", "Hacl_Hash_Blake2b_256", "Hacl_Hash_Blake2s_128", "Hacl_SHA3", "Hacl_Hash_MD5", "Hacl_Hash_SHA1", "Hacl_Hash_SHA2", "EverCrypt_TargetConfig", "EverCrypt", "Vale", "Hacl_Streaming", "EverCrypt_Hash", "Hacl_Chacha20", "Hacl_Salsa20", "Hacl_IntTypes_Intrinsics", "Hacl_Bignum_Base", "Hacl_Bignum", "Hacl_Bignum25519_51", "Hacl_Curve25519_51", "Hacl_Ed25519_PrecompTable", "Hacl_Ed25519", "Hacl_Poly1305_32", "Hacl_NaCl", "Hacl_P256", "Hacl_HMAC", "Hacl_HKDF", "Hacl_Chacha20Poly1305_32", "Hacl_HPKE_Curve51_CP32_SHA256", "Hacl_HPKE_Curve51_CP32_SHA512", "Steel_Reference", "Hacl_GenericField32", "Hacl_Bignum256", "Hacl_Bignum4096", "Hacl_Chacha20_Vec32", "Hacl_Bignum4096_32", "Hacl_HMAC_Blake2s_128", "Hacl_HKDF_Blake2s_128", "Hacl_GenericField64", "Hacl_Bignum32", "Hacl_Bignum256_32", "Hacl_HMAC_DRBG", "Hacl_Bignum64", "Hacl_HMAC_Blake2b_256", "Hacl_HKDF_Blake2b_256", "Hacl_EC_Ed25519"];
var my_debug = false;

if (typeof module !== "undefined")
  module.exports = {
    my_js_files: my_js_files,
    my_modules: my_modules,
    my_debug: my_debug
  }
