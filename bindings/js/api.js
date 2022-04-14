// jshint esversion: 6

if (typeof module !== 'undefined') {
  var fs = require('fs');
  var path = require('path');
  var loader = require(path.resolve(__dirname, './loader.js'));
  var shell = require(path.resolve(__dirname, './shell.js'));
  var api_promise = Promise.resolve(require(path.resolve(__dirname, './api.json')));
  var layouts_promise = Promise.resolve(require(path.resolve(__dirname, './layouts.json')));
  var modules_promise = Promise.resolve(shell.my_modules.map(m => {
    var source = fs.readFileSync(path.resolve(__dirname, './' + m + ".wasm"));
    return new Uint8Array(source);
  }));

} else {
  var loader = this;
  var shell = this;
  var api_promise = fetch("wasm/api.json").then(r => r.json());
  var layouts_promise = fetch("wasm/layouts.json").then(r => r.json());
  var modules_promise = Promise.all(my_modules.map(m => fetch("wasm/" + m + ".wasm")))
    .then(response => Promise.all(response.map(r => r.arrayBuffer())));
}

// HELPERS FOR SIZE FIELDS
// -----------------------

// Grammar of size fields: var<OP>n where
// - var is the name of a variable
// - n is an integer constant
// - <OP> is +, - or *
// - no spaces at all.
var parseOp = (arg, op) => {
  let [ var_, const_ ] = arg.split(op);
  return [ var_, op, const_ ];
};

var parseSize = (arg) => {
  if (arg.indexOf("+") >= 0)
    return parseOp(arg, "+");
  if (arg.indexOf("-") >= 0)
    return parseOp(arg, "-");
  if (arg.indexOf("*") >= 0)
    return parseOp(arg, "*");
  if (arg.indexOf("/") >= 0)
    return parseOp(arg, "/");
  return [ arg ];
};

var evalSize = function(arg, args_int32s) {
  let [ var_, op, const_ ] = parseSize(arg);
  switch (op) {
    case "+":
      return args_int32s[var_] + parseInt(const_);
    case "-":
      return args_int32s[var_] - parseInt(const_);
    case "*":
      return args_int32s[var_] * parseInt(const_);
    case "/":
      let x = parseInt(const_);
      if (args_int32s[var_] % x != 0)
        throw new Error("Argument whose length is "+arg+" is not a multiple of "+x);
      return args_int32s[var_] / x;
    default:
      return args_int32s[var_];
  }
};

var invertSize = function(arg, total) {
  let [ var_, op, const_ ] = parseSize(arg);
  switch (op) {
    case "+":
      return [ var_, total - parseInt(const_) ];
    case "-":
      return [ var_, total + parseInt(const_) ];
    case "*":
      let x = parseInt(const_);
      if (total % x != 0)
        throw new Error("Argument whose length is "+arg+" is not a multiple of "+x);
      return [ var_, total / x ];
    case "/":
      return [ var_, total * parseInt(const_) ];
    default:
      return [var_, total];
  }
};

// VALIDATION
// ----------

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
        if (!(arg.type === "bool" || arg.type === "int32" || arg.type.startsWith("buffer") || arg.type[0].toUpperCase() == arg.type[0]))
          throw Error("in " + obj_name + ", argument #" + i + " should have a 'kind' that is 'int', 'bool' or 'buffer'");
        if (arg.type.startsWith("buffer") && arg.size === undefined)
          throw Error("in " + obj_name + ", argument #" + i + " is a buffer and should have a 'size' field");
        if (arg.kind === "input" && arg.type.startsWith("buffer") && !("interface_index" in arg))
          throw Error("in " + obj_name + ", argument #" + i + " is an input and should have a 'interface_index' field");
        if ((arg.kind === "output" || (arg.kind === "input" && arg.interface_index !== undefined)) && arg.tests === undefined)
          throw Error("please provide a 'tests' field for argument #" + i + " of " + obj_name + " in api.json");
        if ((arg.kind === "output" || (arg.kind === "input" && arg.interface_index !== undefined)) && !Array.isArray(arg.tests))
          throw Error("the 'tests' field for argument #" + i + " of " + obj_name + " should be an array");

        if (arg.type === "int32" && arg.kind === "input")
          length_args_available.push(arg.name);
        if (arg.type.startsWith("buffer") && arg.kind === "input" && typeof arg.size === "string")
          // TODO: we should first check the field is syntactically correct
          // before parsing it... if parsing fails, this will yield a
          // nonsensical size and the error will be caught below.
          length_args_available.push(parseSize(arg.size)[0]);
      });
      func_obj.args.forEach(function(arg, i) {
        if (arg.type.startsWith("buffer") && typeof arg.size === "string" && arg.kind === "output" &&
          !length_args_available.includes(arg.size) &&
          !length_args_available.includes(arg.size.substring(0, arg.size.indexOf("+"))) &&
          !length_args_available.includes(arg.size.substring(0, arg.size.indexOf("-"))) &&
          !length_args_available.includes(arg.size.substring(0, arg.size.indexOf("/"))) &&
          !length_args_available.includes(arg.size.substring(0, arg.size.indexOf("*")))
        )
          throw Error("incorrect 'size' field value (" + arg.size + ")for argument #" + i + " of " + obj_name + " in api.json");
      });
      if (func_obj.return === undefined) {
        throw Error("please provide a 'return' field for " + obj_name + " in api.json");
      }
    };
  };
};

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
  // To be called only if isInitialized == false.
  var loadWasm = function() {
    if (isInitialized)
      return Promise.resolve();
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
  we have to describe the correspondence between the two in the `api.json` file.

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

  var array_type = function(type) {
    switch (type) {
      case "buffer":
        return Uint8Array;
      case "buffer(uint32)":
        return Uint32Array;
      case "buffer(uint64)":
        return BigUint64Array;
      default:
        throw new Error("Unknown array type: "+type);
    }
  }

  var cell_size = function(type) {
    switch (type) {
      case "buffer":
        return 1;
      case "buffer(uint32)":
        return 4;
      case "buffer(uint64)":
        return 8;
      default:
        throw new Error("Unknown array type: "+type);
    }
  }

  var check_array_type = function(type, candidate, length, name) {
    if ((typeof(candidate) !== "object") ||
      (candidate.length !== length) ||
      (candidate.constructor !== array_type(type))
    ) {
      throw new Error(
        "name: Please ensure the argument " + name + " has length " + length + " and is a " + array_type(type)
      );
    }
  };

  var copy_array_to_stack = function(type, array) {
    // This returns a suitably-aligned pointer.
    var pointer = loader.reserve(Module.Kremlin.mem, array.length, cell_size(type));
    (new Uint8Array(Module.Kremlin.mem.buffer)).set(new Uint8Array(array.buffer), pointer);
    // console.log("stack pointer got", loader.p32(pointer));
    // console.log("source", array.buffer);
    // loader.dump(Module.Kremlin.mem, 2048, 0x13000);
    return pointer;
  };

  // len is in number of elements
  var read_memory = function(type, ptr, len) {
    // TODO: faster path with aligned pointers?
    var result = new ArrayBuffer(len*cell_size(type));
    // console.log("New memory buffer", type, len, len*cell_size(type));
    (new Uint8Array(result).set(new Uint8Array(Module.Kremlin.mem.buffer)
      .subarray(ptr, ptr + len*cell_size(type))));
    // console.log(result);
    return new (array_type(type))(result);
  };

  // HELPERS FOR HEAP LAYOUT
  // -----------------------

  // Filled out via a promise.
  var layouts;

  var heapReadBlockSize = (ptr) => {
    var m32 = new Uint32Array(Module.Kremlin.mem.buffer)
    return m32[ptr/4-2]-8;
  };

  var heapReadBuffer = (type, ptr) => {
    // Pointer points to the actual data, header is 8 bytes before, length in
    // header includes header. Heap base pointers are always aligned on 8 byte
    // boundaries, but inner pointers (e.g. within a struct) are aligned on
    // their size.
    if (!((ptr % cell_size(type)) == 0))
      throw new Error("malloc violation (1)");
    let block_size = heapReadBlockSize(ptr);
    if (!(block_size % cell_size(type) == 0))
      throw new Error("malloc violation (2)");
    let len = block_size / cell_size(type);
    // console.log("pointer:", loader.p32(ptr), "header:", loader.p32(ptr-8), "len:", loader.p32(len));
    return read_memory(type, ptr, len);
  };

  var heapReadInt = (typ, ptr) => {
    switch (typ) {
      case "A8":
        var m8 = new Uint8Array(Module.Kremlin.mem.buffer);
        return m8[ptr];

      case "A32":
        if (!(ptr % 4) == 0)
          throw new Error("malloc violation (3)");
        var m32 = new Uint32Array(Module.Kremlin.mem.buffer);
        return m32[ptr/4];

      case "A64":
        if (!(ptr % 8) == 0)
          throw new Error("malloc violation (4)");
        var m64 = new BigUint64Array(Module.Kremlin.mem.buffer);
        return m64[ptr/8];

      default:
        throw new Error("Not implemented: "+typ);
    }
  };

  var heapWriteInt = (typ, ptr, v) => {
    switch (typ) {
      case "A8":
        var m8 = new Uint8Array(Module.Kremlin.mem.buffer);
        m8[ptr] = v;
        break;

      case "A32":
        if (!(ptr % 4) == 0)
          throw new Error("malloc violation (3)");
        var m32 = new Uint32Array(Module.Kremlin.mem.buffer);
        m32[ptr/4] = v;
        break;

      case "A64":
        if (!(ptr % 8) == 0)
          throw new Error("malloc violation (4)");
        var m64 = new BigUint64Array(Module.Kremlin.mem.buffer);
        m64[ptr/8] = v;
        break;

      default:
        throw new Error("Not implemented: "+typ);
    }
  };

  // Fast-path for arrays of flat integers.
  var heapReadBlockFast = (int_type, ptr) => {
    switch (int_type) {
      case "A8":
        return heapReadBuffer("buffer", ptr);
      case "A32":
        return heapReadBuffer("buffer(uint32)", ptr);
      case "A64":
        return heapReadBuffer("buffer(uint64)", ptr);
      default:
        throw new Error("Not implemented: "+int_type);
    }
  };

  // Fast-path for arrays of flat integers.
  var heapWriteBlockFast = (int_type, ptr, arr) => {
    // console.log(arr);
    (new Uint8Array(Module.Kremlin.mem.buffer)).set(new Uint8Array(arr.buffer), ptr);
  };

  // Eventually will be mutually recursive once Layout is implemented (flat
  // packed structs).
  var heapReadType = (runtime_type, ptr) => {
    let [ type, data ] = runtime_type;
    switch (type) {
      case "Int":
        return heapReadInt(data[0], ptr);
      case "Pointer":
        if (data[0] == "Int")
          return heapReadBlockFast(data[1][0], heapReadInt("A32", ptr));
        // pass-through
      default:
        throw new Error("Not implemented: "+tag);
    }
  };

  var heapWriteType = (runtime_type, ptr, v) => {
    let [ type, data ] = runtime_type;
    switch (type) {
      case "Int":
        heapWriteInt(data[0], ptr, v);
        break;
      case "Pointer":
        if (data[0] == "Int") {
          let sz = v.buffer.byteLength;
          // NB: could be more precise with alignment, I guess
          let dst = loader.reserve(Module.Kremlin.mem, sz, 8);
          heapWriteInt("A32", ptr, dst);
          heapWriteBlockFast(data[1][0], dst, v);
          break;
        }
        // pass-through
      default:
        throw new Error("Not implemented: "+tag);
    }
  };

  var heapReadLayout = (layout, ptr) => {
    // console.log(layout);
    let [ tag, data ] = layouts[layout];
    switch (tag) {
      case "LFlat":
        let o = {};
        // console.log(data);
        data.fields.forEach(([field, [ ofs, typ ]]) =>
          o[field] = heapReadType(typ, ptr + ofs)
        );
        return o;
      default:
        throw new Error("Not implemented: "+tag);
    }
  };

  var heapWriteLayout = (layout, ptr, v) => {
    let [ tag, data ] = layouts[layout];
    // console.log(v);
    switch (tag) {
      case "LFlat":
        data.fields.forEach(([field, [ ofs, typ ]]) => {
          // console.log("Writing", v[field]);
          heapWriteType(typ, ptr + ofs, v[field]);
        });
        break;
      default:
        throw new Error("Not implemented: "+tag);
    }
  };

  var stackWriteLayout = (layout, v) => {
    let [ tag, data ] = layouts[layout];
    switch (tag) {
      case "LFlat":
        let ptr = loader.reserve(Module.Kremlin.mem, data.size, 8);
        heapWriteLayout(layout, ptr, v);
        return ptr;
      default:
        throw new Error("Not implemented: "+tag);
    }
  };

  // END HELPERS FOR HEAP LAYOUT
  

  // This is the main logic; this function is partially applied to its
  // first two arguments for each API entry. We assume JITs are working well
  // enough to make this efficient.
  var callWithProto = function(proto, args) {
    var expected_args_number = proto.args.filter(function(arg) {
      return arg.interface_index !== undefined;
    }).length;
    if (args.length != expected_args_number) {
      throw Error("wrong number of arguments to call the F*-wasm function " + proto.name + ": expected " + expected_args_number + ", got " + args.length);
    }
    var memory = new Uint32Array(Module.Kremlin.mem.buffer);
    var sp = memory[0];

    // Integer arguments are either
    // - user-provided, in which case they have an interface_index
    // - automatically determined, in which case they appear in the `size` field
    //   of another buffer argument.
    // In a first pass, we need to figure out the value of all integer
    // arguments to enable lookups by name.
    // - When allocating a variable-length output buffer, we look up the
    //   corresponding integer argument by name (user provides length but not
    //   array).
    // - When fill out an integer argument that corresponds to the length of a
    //   variable-length input buffer, we also look it up by name (user provides
    //   array but not length).
    var args_int32s = {};
    proto.args.forEach(function(arg) {
      if (arg.type.startsWith("buffer") && typeof arg.size === "string" && arg.interface_index !== undefined && arg.kind === "input") {
        // API contains e.g.:
        //   { "name": "len" },
        //   { "name": "buf", "type": "buffer", "size": "len", "interface_index": 3, "kind": "input" }
        // We need to figure out `len` automatically since it doesn't have an
        // interface index, meaning it isn't one of the arguments passed to the
        // high-level API. We know `buf` is the second argument passed to the
        // function, and thus allows us to fill out `len`.
        let [ var_, var_value ] = invertSize(arg.size, args[arg.interface_index].length);
        // console.log("Determined "+var_+"="+var_value);

        if (var_ in args_int32s && var_value != args_int32s[arg.size])
          throw new Error("Inconsistency in sizes");
        args_int32s[var_] = var_value;
      } else if (arg.type === "int32" && arg.interface_index !== undefined) {
        // API contains e.g.:
        //   { "name": "len", "interface_index": 3 },
        //   { "name": "buf", "type": "buffer", "size": "len", "kind": "output" }
        // We know we will need `len` below when trying to allocate an array for
        // `output` -- insert it into the table.
        args_int32s[arg.name] = args[arg.interface_index];
      }
    });

    // Figure out the value of all arguments and write to the WASM stack
    // accordingly. 
    var args = proto.args.map(function(arg, i) {
      if (arg.type.startsWith("buffer")) {
        var size;
        if (typeof arg.size === "string") {
          size = evalSize(arg.size, args_int32s);
        } else {
          size = arg.size;
        }
        var arg_byte_buffer;
        if (arg.kind === "input") {
          var func_arg = args[arg.interface_index];
          arg_byte_buffer = new (array_type(arg.type))(func_arg);
        } else if (arg.kind === "output") {
          arg_byte_buffer = new (array_type(arg.type))(size);
        }
        check_array_type(arg.type, arg_byte_buffer, size, arg.name);
        // TODO: this copy is un-necessary in the case of output buffers.
        return copy_array_to_stack(arg.type, arg_byte_buffer);
      }

      if (arg.type === "bool" || arg.type === "int32") {
        if (arg.interface_index === undefined) {
          // Variable-length argument, determined via first pass above.
          return args_int32s[arg.name];
        } else {
          // Regular interger argument, passed by the user.
          return args[arg.interface_index];
        }
      }

      // Layout
      if (arg.type[0].toUpperCase() == arg.type[0]) {
        let func_arg = args[arg.interface_index];
        return stackWriteLayout(arg.type, func_arg);
      }

      throw Error("Unimplemented ! ("+proto.name+")");
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
    var call_return = Module[proto.module][func_name](...args);

    // Populating the JS buffers returned with their values read from Wasm memory
    var return_buffers = args.map(function(pointer, i) {
      if (proto.args[i].kind === "output") {
        var protoRet = proto.args[i];
        var size;
        if (typeof protoRet.size === "string") {
          size = evalSize(protoRet.size, args_int32s);
        } else {
          size = protoRet.size;
        }
        return read_memory(protoRet.type, pointer, size);
      } else {
        return null;
      }
    }).filter(v => v !== null);

    // Resetting the stack pointer to its old value
    memory[0] = sp;
    if ("kind" in proto.return && proto.return.kind === "layout") {
      // Heap-allocated value
      if (proto.return.type.startsWith("buffer")) {
        let r = heapReadBuffer(proto.return.type, call_return);
        memory[Module.Kremlin.mem.buffer.byteLength/4-1] = 0;
        return r;
      } else {
        let r = heapReadLayout(proto.return.type, call_return);
        memory[Module.Kremlin.mem.buffer.byteLength/4-1] = 0;
        return r;

        // loader.dump(Module.Kremlin.mem, 2048, Module.Kremlin.mem.buffer.byteLength - 2048);
        // console.log(loader.p32(call_return), r, JSON.stringify(layouts[proto.return.type], null, 2));

        // let ptr = stackWriteLayout(proto.return.type, r);
        // console.log(loader.p32(ptr));
        // loader.dump(Module.Kremlin.mem, 2048, 0x13000);
        // throw new Error(func_name+": non-buffer return layout not implemented");
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

  var getInitializedHaclModule = async function () {
    if (!isInitialized) {
      // Load all WASM modules from network (web) or disk (node).
      await loadWasm();
      // Write into the global.
      layouts = await layouts_promise;

      // Initial API validation (TODO: disable for release...?)
      let api_json = await api_promise;
      validateJSON(api_json);

      // We follow the structure of api.json to expose an object whose structure
      // follows the keys of api.json; each entry is a partial application of
      // `callWithProto` (generic API wrapper) to its specific entry in api.json
      // held in `api_json[key_module][key_func]`.
      for (let key_module in api_json) {
        for (let key_func in api_json[key_module]) {
          if (api_obj[key_module] == null) {
            api_obj[key_module] = {};
          }
          api_obj[key_module][key_func] = function(...args) {
            return callWithProto(api_json[key_module][key_func], args);
          };
        };
      };
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
