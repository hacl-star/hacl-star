var fs = require('fs');
var loader = require('./loader.js')
var shell = require('./shell.js')
var api_json = require('./api.json')

// The following function validates the contents of `api.json`. It is meant as
// a helper when creating new binders, it provides explicit error messages.
const validateJSON = function(json) {
  Object.keys(json).map(function(key_module) {
    Object.keys(json[key_module]).map(function(key_func) {
      var func_obj = json[key_module][key_func];
      var obj_name = key_module + "." + key_func;
      if (func_obj.module === undefined) {
        throw Error("please provide a 'module' field for " + obj_name + " in api.json");
      }
      if (!(shell.my_modules.includes(func_obj.module))) {
        throw Error(obj_name +".module='"+func_obj.module+"' of api.json should be listed in shell.js");
      }
      if (func_obj.name === undefined) {
        throw Error("please provide a 'name' field for " + obj_name + " in api.json");
      }
      if (func_obj.args === undefined) {
        throw Error("please provide a 'args' field for " + obj_name + " in api.json");
      }
      if (!Array.isArray(func_obj.args)) {
        throw Error("the 'args' field for " + obj_name + " should be an array");
      }
      var length_args_available = [];
      func_obj.args.map(function(arg, i) {
        if (!(arg.kind === "input" || (arg.kind === "output"))) {
          throw Error("in " + obj_name + ", argument #" + i + " should have a 'kind' that is 'output' or 'input'")
        }
        if (!(arg.type === "bool" || (arg.type === "int") || (arg.type === "buffer"))) {
          throw Error("in " + obj_name + ", argument #" + i + " should have a 'kind' that is 'int', 'bool' or 'buffer'")
        }
        if (arg.type === "buffer") {
          if (arg.size === undefined) {
            throw Error("in " + obj_name + ", argument #" + i + " is a buffer and should have a 'size' field")
          }
        }
        if (arg.kind === "input" && arg.type === "buffer") {
          if (arg.interface_index === undefined) {
              throw Error("in " + obj_name + ", argument #" + i + " is an input and should have a 'interface_index' field")
          }
        }
        if ((arg.kind === "output" || (arg.kind === "input" && arg.interface_index !== undefined)) && arg.tests === undefined) {
          throw Error("please provide a 'tests' field for argument #" + i + " of " + obj_name + " in api.json");
        }
        if ((arg.kind === "output" || (arg.kind === "input" && arg.interface_index !== undefined)) && !Array.isArray(arg.tests)) {
          throw Error("the 'tests' field for argument #" + i + " of " + obj_name + " should be an array");
        }
        if (arg.type === "int" && arg.kind === "input") {
          length_args_available.push(arg.name)
        }
      });
      func_obj.args.map(function(arg, i) {
        if (arg.type === "buffer" && typeof arg.size === "string") {
          if (!length_args_available.includes(arg.size)) {
            throw Error("incorrect 'size' field value ("+ arg.size +")for argument #" + i + " of " + obj_name + " in api.json")
          }
        }
      });
      if (func_obj.return === undefined) {
        throw Error("please provide a 'return' field for " + obj_name + " in api.json");
      }
    })
  });
}
validateJSON(api_json);

// The module is encapsulated inside a closure to prevent anybody from accessing
// the WebAssembly memory.
var HaclWasm = (function() {
  'use strict';
  var isInitialized = false
  var Module = {}

  // This object is passed at the wasm instantiation, it's required by the
  // KreMLin-generated files. Since we don't need to import anything, it's empty.
  var my_imports = {}

  // The WebAssembly modules have to be initialized before calling any function.
  // This checks if it has been done already, and if not does it.
  const checkIfInitialized = function() {
    if (isInitialized === false) {
      return Promise.all(shell.my_modules.map(m => {
        var source = fs.readFileSync(require.resolve('./' + m + ".wasm"));
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
  we have to describe the correspondance between the two in the `api.json` file.

  The scheme of the JSON file is the following :
  - `module`, this module name will be shown in the JS API
    - `function`, this function name will be shown in the JS API
      - `module`, the name of the WebAssembly file where to find the function
      - 'name', the name of the WebAssembly export corresponding to the function
      - 'args', the list of the WebAssembly arguments expected by the function
        - 'name', the name of the argument which will be shown in the JS Doc
        - 'kind', either `input` or `output` of the function
        - 'type', either 'int' or 'boolean' or 'buffer'
        - 'size', either an integer of a string which is the 'name' of another
          argument of type 'int'
        - 'interface_index', for all `input` that should appear in JS, position
          inside the argument list of the JS function
        - 'tests', a list of values for this arguments, each value corresponding
          to a different test case
      - 'return', the return type of the WebAssembly function
  */

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

  const callWithProto = function(proto, args, loc_name) {
    var expected_args_number = proto.args.filter(arg => arg.interface_index !== undefined).length;
    if (args.length != expected_args_number) {
      throw Error("wrong number of arguments to call the F*-wasm function " + loc_name + ": expected " + expected_args_number + ", got " + args.length)
    }
    let memory = new Uint32Array(Module.Kremlin.mem.buffer);
    let sp = memory[0];
    var var_lengths = {};
    // Populating the variable length arguments by retrieving buffer lengths
    proto.args.map((arg) => {
      if (arg.type === "buffer") {
        if ((typeof arg.size === "string") && (arg.interface_index !== undefined)) {
          let func_arg = args[arg.interface_index];
          var_lengths[arg.size] = func_arg.length;
        }
      }
      if ((arg.type === "int") && (arg.interface_index !== undefined)) {
        let func_arg = args[arg.interface_index];
        var_lengths[arg.name] = func_arg;
      }
    });
    // Retrieving all input buffers and allocating them in the Wasm memory
    let args_pointers = proto.args.map((arg, i) => {
      if (arg.type === "buffer") {
        var size;
        if (typeof arg.size === "string") {
          size = var_lengths[arg.size]
        } else {
          size = arg.size;
        }
        var argByteBuffer;
        if (arg.kind === "input") {
          let func_arg = args[arg.interface_index];
          argByteBuffer = new Uint8Array(func_arg);
        } else if (arg.kind === "output") {
          argByteBuffer = new Uint8Array(size);
        }
        CheckIfByteArray(argByteBuffer, size, proto.name);
        let pointer = malloc_array(argByteBuffer);
        return {
          "value": pointer,
          "index": i
        };
      }
      if (arg.type === "bool" || arg.type === "int") {
        var value;
        if (arg.interface_index === undefined) {
          value = var_lengths[arg.name];
        } else {
          value = args[arg.interface_index];
        }
        return {
          "value": value,
          "index": i
        };
      }
      throw Error("Unimplemented !");
    });
    // Calling the wasm function !
    let call_return = Module[proto.module][proto.module + "_" + proto.name](
      ...args_pointers.map(x => {
        return x.value;
      })
    );
    // Populating the JS buffers returned with their values read from Wasm memory
    let return_buffers = args_pointers.filter(pointer =>
      proto.args[pointer.index].kind === "output"
    ).map(pointer => {
      let protoRet = proto.args[pointer.index];
      var size;
      if (typeof protoRet.size === "string") {
        size = var_lengths[protoRet.size];
      } else {
        size = protoRet.size;
      }
      let retBuf = new ArrayBuffer(size);
      (new Uint8Array(retBuf)).set(read_memory(pointer.value, size));
      return retBuf;
    });
    if (return_buffers.length == 1) {
      return_buffers = return_buffers[0]
    }
    memory[0] = sp;
    if (proto.return.type === "bool") {
      return [call_return === 1, return_buffers];
    }
    if (proto.return.type === "integer") {
      return [call_return, return_buffers];
    }
    if (proto.return.type === "void") {
      return return_buffers;
    }
    throw "Unimplemented !"
  }

  var checkObj = {
    checkIfInitialized: checkIfInitialized,
  }

  var api_obj = {};

  // Creating object by mapping from api.json structure
  Object.keys(api_json).map(function(key_module) {
    Object.keys(api_json[key_module]).map(function(key_func) {
      if (api_obj[key_module] == null) {
        api_obj[key_module] = {}
      }
      api_obj[key_module][key_func] = async function() {
        var argumentArray = [...arguments];
        await checkIfInitialized();
        return callWithProto(api_json[key_module][key_func], argumentArray);
      }
    })
  });

  return { ...checkObj,
    ...api_obj
  }
})();

if (typeof module !== "undefined") {
  module.exports = HaclWasm
}
