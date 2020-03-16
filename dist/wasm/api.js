var my_print = console.log;

var fs = require('fs');
var browser = require('./browser.js')
var loader = require('./loader.js')
var shell = require('./shell.js')


// Beginning

var HaclWasm = (function() {
  'use strict';
  var isInitialized = false
  var Module = {}

  // This object is passed at the wasm instantiation to link the missing
  // `random_bytes` function, needed for generating new keyPairs.
  var my_imports = {}

  const checkIfInitialized = function() {
    if (isInitialized === false) {
      return Promise.all(shell.my_modules.map(m => {
        var source = fs.readFileSync('./' + m + ".wasm");
        return new Uint8Array(source)
      })).then(bufs => {
        return loader.link(my_imports, bufs.map((b, i) => ({
          buf: b,
          name: shell.my_modules[i]
        })))
      }).then(scope => {
        Module = scope;
        isInitialized = true;
      })
    } else {
      return Promise.resolve()
    }
  }

  /*
  Inside WebAssembly, the functions only take pointers to memory and integers.
  However, we want to expose the functions of the wasm module with a nice Javascript
  API that manipulates ArrayBuffers.

  In order to do that, we have to describe the Javascript prototype of each function
  that we expose. The functions can take and return multiple objects that can be
  buffers, integers or booleans. The buffers can either have a fixed length (and
  in that case we check dynamically whether they have the correct length), or
  have a variable length (and we have to pass that length as an additional
  parameter to WebAssembly).

  In order to match the Javascript API with the actual calls to WebAssembly functions,
  we make several assumptions on the functions exposed in the WebAssembly generated
  from Low*:
  - each variable length buffer argument is preceded by an additional argument,
    its length;
  - output buffers are always first in the list of arguments;
  - if the Javascript function returns a variable length buffer, then the Low* function
    should always return the length of the buffer as an integer.

  For functions that return a variable length buffer, the prototype has to be
  initialized before each call with the maximum output length (that can
  depend on some input variables).
  */

  const Signatures = {
    "Curve25519_51": {
      "ecdh": {
        "module": "Hacl_Curve25519_51",
        "name": "ecdh",
        "args": [{
            "type": "buffer",
            "size": 32,
            "kind": "output",
          },
          {
            "type": "buffer",
            "size": 32,
            "kind": "input",
            "interface_index": 0,
          },
          {
            "type": "buffer",
            "size": 32,
            "kind": "input",
            "interface_index": 1,
          }
        ],
        "return": "bool",
      }
    }
  }

  const CheckIfByteArray = function(candidate, length, name) {
    if (!(typeof(candidate) === "object") ||
      !(candidate.length === length) ||
      !(candidate.constructor === Uint8Array)
    ) {
      throw new Error(
        "name: Please ensure the argument is a " + length + "-bytes Uint8Array."
      );
    }
  };

  const malloc_array = function(array) {
    let pointer = loader.reserve(Module.Kremlin.mem, array.length);
    let memory = new Uint8Array(Module.Kremlin.mem.buffer);
    for (let i = 0; i < array.length; i++) {
      memory[pointer + i] = array[i];
    }
    return pointer;
  };

  const read_memory = function(ptr, len) {
    var result = new ArrayBuffer(len);
    (new Uint8Array(result).set(new Uint8Array(Module.Kremlin.mem.buffer)
      .subarray(ptr, ptr + len)));
    return new Uint8Array(result);
  };

  const callWithProto = function(proto, args) {
    if (args.length != proto.args.filter(arg => arg.interface_index !== undefined).length) {
      throw Error("wrong number of arguments to call the FStar function !")
    }
    let memory = new Uint32Array(Module.Kremlin.mem.buffer);
    let sp = memory[0];
    let args_pointers = proto.args.map((arg, i) => {
      if (arg.type === "buffer") {
        var argByteBuffer;
        if (arg.kind === "input") {
          let func_arg = args[arg.interface_index];
          argByteBuffer = new Uint8Array(func_arg);
        } else if (arg.kind === "output") {
          argByteBuffer = new Uint8Array(arg.size);
        }
        CheckIfByteArray(argByteBuffer, arg.size, proto.name);
        let pointer = malloc_array(argByteBuffer);
        return {
          "value": pointer,
          "index": i
        };
      }
      if (protoArg.type === "bool" || protoArg.type === "integer") {
        let func_arg = args[arg.interface_index];
        return {
          "value": func_arg,
          "index": i
        };
      }
      throw Error("Unimplemented !");
    });
    let call_return = Module[proto.module][proto.module + "_" + proto.name](
      ...args_pointers.map(x => {
        return x.value;
      })
    );
    let return_buffers = args_pointers.filter(pointer =>
      proto.args[pointer.index].kind === "output"
    ).map(pointer => {
      let protoRet = proto.args[pointer.index];
      var size = protoRet.size;
      let retBuf = new ArrayBuffer(size);
      (new Uint8Array(retBuf)).set(read_memory(pointer.value, size))
      return retBuf;
    });
    if (return_buffers.length == 1) {
      return_buffers = return_buffers[0]
    }
    memory[0] = sp;
    if (proto.return === "bool") {
      return [call_return === 1, return_buffers];
    }
    if (proto.return === "integer") {
      return [call_return, return_buffers];
    }
    if (proto.return === "void") {
      return return_buffers;
    }
    throw "Unimplemented !"
  }


  const Curve25519_51 = {
    ecdh: async function ecdh(
      key,
      input
    ) {
      await checkIfInitialized();
      return callWithProto(Signatures.Curve25519_51.ecdh, [
        key,
        input,
      ]);
    }
  }

  return {
    checkIfInitialized: checkIfInitialized,
    Curve25519_51: Curve25519_51,
  }
})();

var scalar = new Uint8Array([
  0xa5, 0x46, 0xe3, 0x6b, 0xf0, 0x52, 0x7c, 0x9d,
  0x3b, 0x16, 0x15, 0x4b, 0x82, 0x46, 0x5e, 0xdd,
  0x62, 0x14, 0x4c, 0x0a, 0xc1, 0xfc, 0x5a, 0x18,
  0x50, 0x6a, 0x22, 0x44, 0xba, 0x44, 0x9a, 0xc4
]);
var input = new Uint8Array([
  0xe6, 0xdb, 0x68, 0x67, 0x58, 0x30, 0x30, 0xdb,
  0x35, 0x94, 0xc1, 0xa4, 0x24, 0xb1, 0x5f, 0x7c,
  0x72, 0x66, 0x24, 0xec, 0x26, 0xb3, 0x35, 0x3b,
  0x10, 0xa9, 0x03, 0xa6, 0xd0, 0xab, 0x1c, 0x4c,
])
var result = HaclWasm.Curve25519_51.ecdh(scalar, input);
var expected_result = new Uint8Array([
  0xc3, 0xda, 0x55, 0x37, 0x9d, 0xe9, 0xc6, 0x90,
  0x8e, 0x94, 0xea, 0x4d, 0xf2, 0x8d, 0x08, 0x4f,
  0x32, 0xec, 0xcf, 0x03, 0x49, 0x1c, 0x71, 0xf7,
  0x54, 0xb4, 0x07, 0x55, 0x77, 0xa2, 0x85, 0x52,
]);
var eq_array = function (a1, a2) {
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
result.then(result => console.log(eq_array(expected_result, new Uint8Array(result[1]))))
