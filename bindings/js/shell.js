
// To be loaded by main.js
var my_js_files = [];
var my_modules = ["WasmSupport", "FStar", "LowStar_Endianness", "Hacl_Hash", "Hacl_SHA3", "Hacl_Impl_Blake2_Constants", "Hacl_Chacha20", "Hacl_Salsa20", "Hacl_Curve25519_64_Slow", "Hacl_Curve25519_51", "Hacl_Ed25519", "Hacl_Poly1305_32", "Hacl_NaCl", "Hacl_Blake2b_32", "Hacl_Chacha20_Vec32", "Hacl_Blake2s_32", "Hacl_HMAC", "Hacl_HKDF", "Hacl_Chacha20Poly1305_32"];
var my_debug = false;

if (typeof module !== "undefined")
  module.exports = {
    my_js_files: my_js_files,
    my_modules: my_modules,
    my_debug: my_debug
  }
