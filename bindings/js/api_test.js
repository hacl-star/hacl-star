// jshint esversion: 8

var path = require('path');
var HaclWasm = require(path.resolve(__dirname, './api.js'));
var test_vectors = require(path.resolve(__dirname, './api.json'));
var loader = require(path.resolve(__dirname, './loader.js'));

function buf2hex(buffer) {
  return Array.prototype.map.call(new Uint8Array(buffer), function(x) {
    return ('00' + x.toString(16)).slice(-2);
  }).join('');
}

function hex2buf(hexString) {
  if (hexString === "") {
    return new Uint8Array(0);
  } else {
    return new Uint8Array(hexString.match(/.{2}/g).map(function(byte) {
      return parseInt(byte, 16);
    }));
  }
}

function assert(b, msg) {
  if (!b)
    throw new Error(msg);
}

var preprocessing = function(typ, value) {
  if (typ === "buffer") {
    return hex2buf(value);
  }
  if (typ === "bool") {
    return JSON.parse(value);
  }
  if (typ === "int32") {
    return JSON.parse(value);
  }
  throw "Unimplemented !";
};

var postprocessing = function(typ, value) {
  if (typ === "buffer") {
    return buf2hex(value);
  }
  if (typ === "bool") {
    return value.toString();
  }
  if (typ === "int32") {
    return value.toString();
  }
  throw "Unimplemented !";
};

var passTest = function(func_sig, func, msg, t) {
  var args = func_sig.args.filter(function(arg) {
    return (arg.kind === "input") && (arg.tests !== undefined);
  }).map(function(arg) {
    return preprocessing(arg.type, arg.tests[t]);
  });
  var result = func.apply(null, args);
  if (func_sig.return.type !== "void") {
    var expected_result = postprocessing(func_sig.return.type, func_sig.return.tests[t]);
    var result_val = postprocessing(func_sig.return.type, result[0]);
    if (result_val !== expected_result) {
      throw "Wrong return value ! Expecting " + expected_result + ", got " + result_val;
    }
  }
  func_sig.args.filter(function(arg) {
    return arg.kind === "output";
  }).map(function(arg, i) {
    var result_val;
    var result_name = arg.name;
    if (func_sig.return.type !== "void") {
      result_val = result[i + 1];
    } else {
      if (Array.isArray(result)) {
        result_val = result[i];
      } else {
        result_val = result;
      }
    }
    result_val = postprocessing(arg.type, result_val);
    if (result_val !== arg.tests[t]) {
      throw "Wrong return value for " + result_name + " ! Expecting " + arg.tests[t] + ", got " + result_val;
    }
  });
  console.log("Test #" + (t + 1) + " passed !");
};

function checkTestVectors(func_sig, func, msg) {
  var number_of_tests = Infinity;
  func_sig.args.map(function(arg) {
    if (arg.tests !== undefined) {
      number_of_tests = Math.min(number_of_tests, arg.tests.length);
    }
  });
  if (func_sig.return.tests !== undefined) {
    number_of_tests = Math.min(number_of_tests, func_sig.return.tests.length);
  }
  console.log("Starting tests for " + msg);
  if (number_of_tests === 0) {
    console.warn("No tests for " + msg + "!");
  }
  for (var t = 0; t < number_of_tests; t++) {
    passTest(func_sig, func, msg, t);
  }
}

// A series of hand-written tests for modules that require API testing that
// cannot be described at the level of a single function.
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
}

// Main test driver
HaclWasm.getInitializedHaclModule().then(function(Hacl) {
  testBignum64(Hacl);
  return;

  var tests = [];
  Promise.all(Object.keys(test_vectors).map(function(key_module) {
    Object.keys(test_vectors[key_module]).map(function(key_func) {
      tests.push([test_vectors[key_module][key_func], Hacl[key_module][key_func], key_module + "." + key_func]);
    });
  }));
  for (var i = 0; i < tests.length; i++) {
    checkTestVectors.apply(null, tests[i]);
  }
});
