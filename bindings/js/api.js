// jshint esversion: 6

if (typeof module !== 'undefined') {
  var fs = require('fs');
  var path = require('path');
  var loader = require(path.resolve(__dirname, './loader.js'));
  var shell = require(path.resolve(__dirname, './shell.js'));
  var api_promise = Promise.resolve(require(path.resolve(__dirname, './api.json')));
  var modules_promise = Promise.resolve(shell.my_modules.map(m => {
    var source = fs.readFileSync(path.resolve(__dirname, './' + m + ".wasm"));
    return new Uint8Array(source);
  }));

} else {
  var loader = this;
  var shell = this;
  var api_promise = fetch("wasm/api.json").then(r => r.json());
  var modules_promise = Promise.all(my_modules.map(m => fetch("wasm/" + m + ".wasm")))
    .then(response => Promise.all(response.map(r => r.arrayBuffer())));
}

// The following function validates the contents of `api.json`. It is meant as
// a helper when creating new binders, it provides explicit error messages.
var validateJSON = function(json) {
  for (let key_module in json) {
    for (let key_func in json[key_module]) {
      let func_obj = json[key_module][key_func];
      let obj_name = key_module + "." + key_func;

      if (!("module" in func_obj))
        throw Error("please provide a 'module' field for " + obj_name + " in api.json");
      if (!(shell.my_modules.includes(func_obj.module)))
        throw Error(obj_name + ".module='" + func_obj.module + "' of api.json should be listed in shell.js");
      if (!("name" in func_obj))
        throw Error("please provide a 'name' field for " + obj_name + " in api.json");
      if (!("args" in func_obj))
        throw Error("please provide a 'args' field for " + obj_name + " in api.json");
      if (!Array.isArray(func_obj.args))
        throw Error("the 'args' field for " + obj_name + " should be an array");

      let length_args_available = [];
      func_obj.args.forEach((arg, i) => {
        if (!(arg.kind === "input" || (arg.kind === "output")))
          throw Error("in " + obj_name + ", argument #" + i + " should have a 'kind' that is 'output' or 'input'");
        if (!(arg.type === "bool" || (arg.type === "int32") || (arg.type === "buffer")))
          throw Error("in " + obj_name + ", argument #" + i + " should have a 'kind' that is 'int', 'bool' or 'buffer'");
        if (arg.type === "buffer" && arg.size === undefined)
          throw Error("in " + obj_name + ", argument #" + i + " is a buffer and should have a 'size' field");
        if (arg.kind === "input" && arg.type === "buffer" && !("interface_index" in arg))
          throw Error("in " + obj_name + ", argument #" + i + " is an input and should have a 'interface_index' field");
        if ((arg.kind === "output" || (arg.kind === "input" && arg.interface_index !== undefined)) && arg.tests === undefined)
          throw Error("please provide a 'tests' field for argument #" + i + " of " + obj_name + " in api.json");
        if ((arg.kind === "output" || (arg.kind === "input" && arg.interface_index !== undefined)) && !Array.isArray(arg.tests))
          throw Error("the 'tests' field for argument #" + i + " of " + obj_name + " should be an array");

        if (arg.type === "int32" && arg.kind === "input")
          length_args_available.push(arg.name);
      });
      func_obj.args.forEach(function(arg, i) {
        if (arg.type === "buffer" && typeof arg.size === "string" &&
          !length_args_available.includes(arg.size) &&
          !length_args_available.includes(arg.size.substring(0, arg.size.indexOf("+"))) &&
          !length_args_available.includes(arg.size.substring(0, arg.size.indexOf("-")))
        )
          throw Error("incorrect 'size' field value (" + arg.size + ")for argument #" + i + " of " + obj_name + " in api.json");
      });
      if (func_obj.return === undefined) {
        throw Error("please provide a 'return' field for " + obj_name + " in api.json");
      }
    };
  };
};

function p8(n) {
  return ("0"+Number(n).toString(16)).slice(-2);
}
function p32(n) {
  return p8((n >>> 24) & 255) + p8((n >>> 16) & 255) + p8((n >>> 8) & 255) + p8(n & 255);
}

// The module is encapsulated inside a closure to prevent anybody from accessing
// the WebAssembly memory.
var HaclWasm = (function() {
  'use strict';
  var isInitialized = false;
  var Module = {};

  // This object is passed at the wasm instantiation, it's required by the
  // KreMLin-generated files. Since we don't need to import anything, it's empty.
  var my_imports = {};

  // The WebAssembly modules have to be initialized before calling any function.
  // This checks if it has been done already, and if not does it.
  var checkIfInitialized = function() {
    if (isInitialized === false) {
      return modules_promise
      .then(function(bufs) {
        return loader.link(my_imports, bufs.map(function(b, i) {
          return {
            buf: b,
            name: shell.my_modules[i]
          };
        }));
      }).then(function(scope) {
        Module = scope;
        isInitialized = true;
      });
    } else {
      return Promise.resolve();
    }
  };

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
        - 'size', either an integer or a string which is the 'name' of another
          argument of type 'int'; in the latter case, it can be optionally
          followed by '+' or '-' and an integer, e.g. "mlen+16"
        - 'interface_index', for all `input` that should appear in JS, position
          inside the argument list of the JS function
        - 'tests', a list of values for this arguments, each value corresponding
          to a different test case
      - 'return', the return type of the WebAssembly function
      - 'custom_module_name', if true, it signifies that the prefix of the name
        of the WebAssembly function does not coincide with the name of the
        WebAssembly module; the module name will not be used when calling it,
        instead 'name' will contain the full name of the function
  */

  var check_if_byte_array = function(candidate, length, name) {
    if ((typeof(candidate) !== "object") ||
      (candidate.length !== length) ||
      (candidate.constructor !== Uint8Array)
    ) {
      throw new Error(
        "name: Please ensure the argument " + name + " is a " + length + "-bytes Uint8Array."
      );
    }
  };

  var copy_array_to_stack = function(array) {
    var pointer = loader.reserve(Module.Kremlin.mem, array.length);
    (new Uint8Array(Module.Kremlin.mem.buffer)).set(array, pointer);
    return pointer;
  };

  var read_memory = function(ptr, len) {
    var result = new ArrayBuffer(len);
    (new Uint8Array(result).set(new Uint8Array(Module.Kremlin.mem.buffer)
      .subarray(ptr, ptr + len)));
    return new Uint8Array(result);
  };

  var heapReadBuffer = (ptr) => {
    // Pointer points to the actual data, header is 8 bytes before, length in
    // header includes header.
    var m8 = new Uint8Array(Module.Kremlin.mem.buffer);
    var m32 = new Uint32Array(Module.Kremlin.mem.buffer)
    let len = m32[ptr/4-2]-8;
    // console.log("pointer:", p32(ptr), "header:", p32(ptr-8), "len:", p32(len));
    return read_memory(ptr, len);
  };

  var evalSizeWithOp = function(arg, op, var_lengths) {
     if (arg.indexOf(op) >= 0) {
       var terms = arg.split(op);
       if (op === "+") {
         return var_lengths[terms[0]] + parseInt(terms[1]);
       } else if (op === "-") {
         return var_lengths[terms[0]] - parseInt(terms[1]);
       } else {
         throw Error("Operator " + op + " not valid in `size` parameter, only '+' and '-' are supported.")
       }
     }
  };

  var parseSize = function(arg, var_lengths) {
    if (arg.indexOf("+") >= 0) {
      return evalSizeWithOp(arg, "+", var_lengths);
    } else if (arg.indexOf("-") >= 0) {
      return evalSizeWithOp(arg, "-", var_lengths);
    } else {
      return var_lengths[arg];
    }
  };

  var callWithProto = function(proto, args, loc_name) {
    var expected_args_number = proto.args.filter(function(arg) {
      return arg.interface_index !== undefined;
    }).length;
    if (args.length != expected_args_number) {
      throw Error("wrong number of arguments to call the F*-wasm function " + loc_name + ": expected " + expected_args_number + ", got " + args.length);
    }
    var memory = new Uint32Array(Module.Kremlin.mem.buffer);
    var sp = memory[0];
    var var_lengths = {};
    // Populating the variable length arguments by retrieving buffer lengths
    proto.args.map(function(arg) {
      var func_arg;
      if (arg.type === "buffer") {
        if ((typeof arg.size === "string") && (arg.interface_index !== undefined)) {
          func_arg = args[arg.interface_index];
          var_lengths[arg.size] = func_arg.length;
        }
      }
      if ((arg.type === "int32") && (arg.interface_index !== undefined)) {
        func_arg = args[arg.interface_index];
        var_lengths[arg.name] = func_arg;
      }
    });
    // Retrieving all input buffers and allocating them in the Wasm memory
    var args_pointers = proto.args.map(function(arg, i) {
      if (arg.type === "buffer") {
        var size;
        if (typeof arg.size === "string") {
          size = parseSize(arg.size, var_lengths);
        } else {
          size = arg.size;
        }
        var arg_byte_buffer;
        if (arg.kind === "input") {
          var func_arg = args[arg.interface_index];
          arg_byte_buffer = new Uint8Array(func_arg);
        } else if (arg.kind === "output") {
          arg_byte_buffer = new Uint8Array(size);
        }
        check_if_byte_array(arg_byte_buffer, size, arg.name);
        var pointer = copy_array_to_stack(arg_byte_buffer);
        return {
          "value": pointer,
          "index": i
        };
      }
      if (arg.type === "bool" || arg.type === "int32") {
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
      throw Error("Unimplemented ! ("+loc_name+")");
    });
    // Calling the wasm function !
    if (proto.custom_module_name) {
      var func_name = proto.name;
    } else {
      var func_name = proto.module + "_" + proto.name;
    }
    if (!(proto.module in Module))
      throw new Error(proto.module + " is not in Module");
    if (!(func_name in Module[proto.module]))
      throw new Error(func_name + " is not in Module["+proto.module+"]");
    var call_return = Module[proto.module][func_name](
      ...args_pointers.map(function(x) {
        return x.value;
      })
    );
    // Populating the JS buffers returned with their values read from Wasm memory
    var return_buffers = args_pointers.filter(function(pointer) {
      return proto.args[pointer.index].kind === "output";
    }).map(function(pointer) {
      var protoRet = proto.args[pointer.index];
      var size;
      if (typeof protoRet.size === "string") {
        size = parseSize(protoRet.size, var_lengths);
      } else {
        size = protoRet.size;
      }
      return read_memory(pointer.value, size);
    });
    // Resetting the stack pointer to its old value
    memory[0] = sp;
    if ("kind" in proto.return && proto.return.kind === "layout") {
      // Heap-allocated value
      if (proto.return.type === "buffer") {
        let r = heapReadBuffer(call_return);
        memory[Module.Kremlin.mem.buffer.byteLength/4-1] = 0;
        return r;
      } else {
        throw new Error(func_name+": non-buffer return layout not implemented");
      }
    }
    if (proto.return.type === "bool") {
      return [call_return === 1, return_buffers].flat();
    }
    if (proto.return.type === "int32") {
      return [call_return, return_buffers].flat();
    }
    if (proto.return.type === "void") {
      return return_buffers;
    }
    throw new Error(func_name+": Unimplemented !");
  };

  var api_obj = {};
  let loaded = false;

  var getInitializedHaclModule = async function () {
    await checkIfInitialized();
    if (!loaded) {
      let api_json = await api_promise;
      validateJSON(api_json);

      // Creating object by mapping from api.json structure
      Object.keys(api_json).map(function(key_module) {
        Object.keys(api_json[key_module]).map(function(key_func) {
          if (api_obj[key_module] == null) {
            api_obj[key_module] = {};
          }
          api_obj[key_module][key_func] = function(...args) {
            if (isInitialized === false) {
              throw 'Uninitialized';
            };
            return callWithProto(api_json[key_module][key_func], args);
          };
        });
      });

      loaded = true;
    }
    return Promise.resolve(api_obj);
  };

  var checkObj = {
    getInitializedHaclModule: getInitializedHaclModule,
  };

  return checkObj;
})();

if (typeof module !== "undefined") {
  module.exports = HaclWasm;
}
