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
        "name: Please ensure the argument " + candidate + " is a " + length + "-bytes Uint8Array."
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
    Curve25519_51: Curve25519_51
  }
})();

if (typeof module !== "undefined")
  module.exports = {
    HaclWasm: HaclWasm,
  }
