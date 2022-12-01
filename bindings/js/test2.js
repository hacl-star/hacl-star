// jshint esversion: 8

// We demonstrate how to write a sample program that uses the high-level HACL*
// API. Run this with `node test2.js`. See `test.html` for a version to be run
// directly from within the browser.

var HaclWasm = require('./api.js');
var loader = require('./loader.js');

// Test helpers
// ------------

const buf2hex = buffer => [...new Uint8Array(buffer)].map(x => `00${x.toString(16)}`.slice(-2)).join('');

function hex2buf(hexString) {
  if (hexString === "")
    return new Uint8Array(0);
  else
    return new Uint8Array(hexString.match(/.{2}/g).map(byte => parseInt(byte, 16)));
}

function assert(b, msg) {
  if (!b)
    throw new Error(msg);
}

// Functional test
// ---------------

function testBignum64(Hacl) {
  let a = Hacl.Bignum_64.new_bn_from_bytes_le(hex2buf("4100000000000000"));
  let b = Hacl.Bignum_64.new_bn_from_bytes_le(hex2buf("4200000000000000"));
  let c = Hacl.Bignum_64.new_bn_from_bytes_le(hex2buf("4300000000000000"));
  assert(a instanceof BigUint64Array, "a not of the right return type");
  assert(a.length == 1, "a does not have the right length");
  assert(a[0] == 0x41n, "incorrect layout for a");
  let ctx = Hacl.Bignum_64.mont_ctx_init(c);
  let [ d ] = Hacl.Bignum_64.mul(a, b);
  assert(d instanceof BigUint64Array, "d not of the right return type");
  assert(d.length == 2, "d does not have the right length");
  assert(d[0] == 0x41n*0x42n);
  let [ e ] = Hacl.Bignum_64.mod_precomp(ctx, d);
  assert(e[0] == 0x02);
  let [ e_bytes ] = Hacl.Bignum_64.bn_to_bytes_le(e);
  assert (e_bytes instanceof Uint8Array);
  assert (e_bytes.length == 8);
  assert (e_bytes[0] == 0x02);
  console.log("testBignum64 successful", buf2hex(e_bytes.buffer));
}

function testBignumMontgomery64(Hacl) {
  let a = Hacl.Bignum_64.new_bn_from_bytes_le(hex2buf("4100000000000000"));
  let b = Hacl.Bignum_64.new_bn_from_bytes_le(hex2buf("4200000000000000"));
  let n = Hacl.Bignum_64.new_bn_from_bytes_le(hex2buf("4300000000000000"));

  let ctx = Hacl.Bignum_Montgomery_64.field_init(n);
  let [ aM ] = Hacl.Bignum_Montgomery_64.to_field(ctx, a);
  let [ bM ] = Hacl.Bignum_Montgomery_64.to_field(ctx, b);
  let [ dM ] = Hacl.Bignum_Montgomery_64.mul(ctx, aM, bM);

  let [ e ] = Hacl.Bignum_Montgomery_64.from_field(ctx, dM);
  assert(e[0] == 0x02);
  console.log("testBignumMontgomery64 successful", buf2hex(e.buffer));
}

// Initialization
// --------------

// Note: this is an optimization. We demonstrate how to selectively load only a
// subset of the WASM files so as to provide only the functionality one is
// interested in. If packaging the entire set of WASM files is not a problem,
// leave `modules` undefined.
let modules = [
  "WasmSupport",
  "FStar",
  "Hacl_Bignum_Base",
  "Hacl_Bignum",
  "Hacl_GenericField64",
  "Hacl_Bignum64",
];

// Main test driver
HaclWasm.getInitializedHaclModule(modules).then(function(Hacl) {
  testBignumMontgomery64(Hacl);
  testBignum64(Hacl);
});
