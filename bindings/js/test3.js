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

// Assumes ASCII!!
function stringToUint8Array(s) {
  let b = new Uint8Array(s.length);
  (new TextEncoder).encodeInto(s, b);
  return b;
}

// Functional test
// ---------------

const SHA2_256 = 1;

function testEverCryptHash(Hacl) {
  let err, s;
  s = Hacl.EverCrypt_Hash.create(SHA2_256);
  assert (Hacl.EverCrypt_Hash.alg_of_state(s) == SHA2_256);
  console.log("STEP 1", s, Hacl.EverCrypt_Hash.alg_of_state(s));

  [ err, s ] = Hacl.EverCrypt_Hash.update(s, stringToUint8Array("hello world"));
  assert (err == 0);
  console.log("STEP 2", err, s);

  let [ digest ] = Hacl.EverCrypt_Hash.finish(s);
  assert (buf2hex(digest) == "b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9");
  console.log("STEP 3", digest);
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
  "Hacl_Hash_MD5",
  "Hacl_Hash_SHA1",
  "Hacl_Hash_SHA2",
  "Hacl_Impl_Blake2_Constants",
  "Hacl_Hash_Blake2",
  "Hacl_Hash_Blake2s_128",
  "Hacl_Hash_Blake2b_256",
  "Hacl_SHA3",
  "Vale",
  "EverCrypt",
  "EverCrypt_Hash",
];

// Main test driver
HaclWasm.getInitializedHaclModule(modules).then(function(Hacl) {
  testEverCryptHash(Hacl);
});
