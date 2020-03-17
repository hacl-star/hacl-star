var api = require('./api.js')
var test_vectors = require('./api.json');
var eq_array = function(a1, a2) {
  if (a1.length !== a2.length) {
    return false
  }
  for (var i = 0; i < a1.length; i++) {
    if (a1[i] !== a2[i]) {
      return false
    }
  }
  return true
}

function buf2hex(buffer) {
  return Array.prototype.map.call(new Uint8Array(buffer), x => ('00' + x.toString(16)).slice(-2)).join('');
}

function hex2buf(hexString) {
  return new Uint8Array(hexString.match(/.{2}/g).map(byte => parseInt(byte, 16)));
}

async function checkTestVectors(func_sig, func, msg) {
  var number_of_tests = Infinity;
  let preprocessing = function(typ, value) {
    if (typ === "buffer") {
      return hex2buf(value)
    }
    if (typ === "bool") {
      return JSON.parse(value)
    }
    if (typ === "int") {
      return JSON.parse(value)
    }
    throw "Unimplemented !"
  };
  let postprocessing = function(typ, value) {
    if (typ === "buffer") {
      return buf2hex(value)
    }
    if (typ === "bool") {
      return value.toString()
    }
    if (typ === "int") {
      return value.toString()
    }
    throw "Unimplemented !"
  };
  func_sig.args.map(arg => {
    number_of_tests = Math.min(number_of_tests, arg.tests.length)
  });
  number_of_tests = Math.min(number_of_tests, func_sig.return.tests.length);
  console.log("Passing tests for " + msg)
  for (var t = 0; t < number_of_tests; t++) {
    let args = func_sig.args.filter(arg =>
      arg.kind === "input"
    ).map(arg => {
      return preprocessing(arg.type, arg.tests[t])
    });
    let result = await func.apply(null, args);
    if (func_sig.return.type !== "void") {
      var result_val;
      if (func_sig.args.filter(arg => arg.kind === "output").length > 0) {
        result_val = result[0];
      } else {
        result_val = result;
      }
      var expected_result = postprocessing(func_sig.return.type, func_sig.return.tests[t]);
      if (result_val === expected_result) {
        throw "Wrong return value ! Expecting " + expected_result + ", got " + result_val;
      }
    }
    func_sig.args.filter(arg =>
      arg.kind === "output"
    ).map((arg, i) => {
      var correct_i;
      if (func_sig.return.type !== "void") {
        correct_i = i + 1;
      } else {
        correct_i = i;
      }
      var result_val = postprocessing(arg.type, result[correct_i]);
      if (result_val !== arg.tests[t]) {
        throw "Wrong return value ! Expecting " + arg.tests[t] + ", got " + result_val
      }
    })
    console.log("Test " + t + " passed !");
  }
}

api.HaclWasm.checkIfInitialized().then(() =>
  checkTestVectors(test_vectors.Curve25519_51.ecdh, api.HaclWasm.Curve25519_51.ecdh, "Curve25519_51")
)
