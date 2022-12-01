// jshint esversion: 6

if (typeof module !== 'undefined') {
  var fs = require('fs');
  var path = require('path');
  var loader = require(path.resolve(__dirname, './loader.js'));
  var shell = require(path.resolve(__dirname, './shell.js'));
  var api_promise = Promise.resolve(require(path.resolve(__dirname, './api.json')));
  var layouts_promise = Promise.resolve(require(path.resolve(__dirname, './layouts.json')));

} else {
  var loader = this;
  var shell = this;
  var api_promise = fetch("api.json").then(r => r.json());
  var layouts_promise = fetch("layouts.json").then(r => r.json());
}

// We now allow the user to pass a custom list of modules if they want to do
// their own, more lightweight packaging.
function getModulesPromise(modules=shell.my_modules) {
  const readModule = async m =>
    typeof module !== 'undefined'
      ? new Uint8Array(await fs.promises.readFile(path.resolve(__dirname, './' + m)))
      : (await fetch(m)).arrayBuffer();
  return Promise.all(modules.map(async name =>
    ({ buf: await readModule(name + ".wasm"), name })
  ));
}

// Comment out for debug
loader.setMyPrint((x) => {});

// HELPERS FOR SIZE FIELDS
// -----------------------

// Grammar of size fields:
//
// f ::=
//   var
//   var<OP>n
//   M.f(var)
//
// var: variable, one of the length variables, may be ghost
// n:   integer constant
// <OP>: +, -, * or /
// M.f: function, referred to by its name in the high-level API, e.g.
//      EverCrypt_Hash.hash_len (and not EverCrypt_Hash_Incremental_hash_len)

var parseOp = (arg, op) => {
  let [ var_, const_ ] = arg.split(op);
  return [ "Op", var_, op, parseInt(const_) ];
};

var parseApp = (arg) => {
  let i = arg.indexOf("(");
  let [ m, f ] = arg.substr(0, i).split(".");
  let x = arg.substr(i+1, arg.length - 1 - i - 1);
  return [ "App", m, f, parseSize(x) ];
}

var parseSize = (arg) => {
  if (arg.includes("+"))
    return parseOp(arg, "+");
  if (arg.includes("-"))
    return parseOp(arg, "-");
  if (arg.includes("*"))
    return parseOp(arg, "*");
  if (arg.includes("/"))
    return parseOp(arg, "/");

  if (arg.includes("("))
    return parseApp(arg);

  return [ "Var", arg ];
};

var evalSize = function(parsedSize, args_int32s, api) {
  let [ kind, ...args ] = parsedSize;
  switch (kind) {
    case "Var": {
      let [ var_ ] = args;
      return args_int32s[var_];
    }
    case "Op": {
      let [ var_, op, const_ ] = args;
      switch (op) {
        case "+":
          return args_int32s[var_] + const_;
        case "-":
          return args_int32s[var_] - const_;
        case "*":
          return args_int32s[var_] * const_;
        case "/":
          if (args_int32s[var_] % const_ != 0)
            throw new Error("Argument whose length is "+arg+" is not a multiple of "+const_);
          return args_int32s[var_] / const_;
        default:
          throw new Error("Illegal operator: "+op);
      }
    }
    case "App": {
      let [ m, f, x ] = args;
      if (!(m in api))
        throw new Error("For size "+parsedSize+", module "+m+" is unknown");
      if (!(f in api[m]))
        throw new Error("For size "+parsedSize+", function "+m+"."+f+" is unknown");
      // console.log("RECURSIVE EVAL SIZE ENTER: ", x);
      x = evalSize(x, args_int32s, api);
      // console.log("RECURSIVE EVAL SIZE END: ", x);
      return api[m][f](x)[0];
    }
  }
};


// Given a size formula `var<OP>n` = `total`, invert it, i.e. solve the
// equation where `var` is unknown.
//
// @param {String} arg        The formula of the form var<OP>n
// @param {Number} total      The value of the formula
// @return {[String, Number]} The variable name `var` and its value.
var invertSize = function(parsedSize, total) {
  let [ kind, var_, op, const_ ] = parsedSize;
  if (kind != "Var" && kind != "Op")
    throw new Error("Illegal size for an input: "+parsedSize);
  switch (op) {
    case "+":
      return [ var_, total - parseInt(const_) ];
    case "-":
      return [ var_, total + parseInt(const_) ];
    case "*":
      let x = parseInt(const_);
      if (total % x != 0)
        throw new Error("Argument whose length is "+parsedSize+" is not a multiple of "+x);
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
// It also has the side effect of filling out the parsedSize field on `arg`
// objects, so that we don't needlessly re-parse every size field all the time.
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

      let length_args_available = {};
      func_obj.args.forEach((arg, i) => {
        if (!(arg.kind === "input" || (arg.kind === "output")))
          throw Error("in " + obj_name + ", argument #" + i + " should have a 'kind' that is 'output' or 'input'");
        if (!(arg.type === "bool" || arg.type === "uint32" || arg.type.startsWith("buffer") || arg.type[0].toUpperCase() == arg.type[0]))
          throw Error("in " + obj_name + ", argument #" + i + " should have a 'kind' that is 'int', 'bool' or 'buffer'");
        if (arg.type.startsWith("buffer") && arg.size === undefined)
          throw Error("in " + obj_name + ", argument #" + i + " is a buffer and should have a 'size' field");
        if (arg.kind === "input" && arg.type.startsWith("buffer") && !("interface_index" in arg))
          throw Error("in " + obj_name + ", argument #" + i + " is an input and should have a 'interface_index' field");
        if ((arg.kind === "output" || (arg.kind === "input" && arg.interface_index !== undefined)) && arg.tests === undefined)
          throw Error("please provide a 'tests' field for argument #" + i + " of " + obj_name + " in api.json");
        if ((arg.kind === "output" || (arg.kind === "input" && arg.interface_index !== undefined)) && !Array.isArray(arg.tests))
          throw Error("the 'tests' field for argument #" + i + " of " + obj_name + " should be an array");

        if (arg.type === "uint32" && arg.kind === "input" && arg.interface_index !== undefined)
          length_args_available[arg.name] = true;

        if (arg.type.startsWith("buffer") && arg.kind === "input" && typeof arg.size === "string") {
          arg.parsedSize = parseSize(arg.size);
          let [ kind, var_ ] = arg.parsedSize;
          if (kind == "Var" || kind == "Op")
            length_args_available[var_] = true;
        }
      });
      func_obj.args.forEach(function(arg, i) {
        if (arg.type.startsWith("buffer") && typeof arg.size === "string" && arg.kind === "output") {
          arg.parsedSize = parseSize(arg.size);
          let [ kind, var_ ] = arg.parsedSize;
          if ((kind == "Var" || kind == "Op") && !(var_ in length_args_available)) {
            console.log(arg);
            console.log(length_args_available);
            throw Error("incorrect 'size' field value (" + arg.size + ") for argument #" + i + " of " + obj_name + " in api.json");
          }
        }
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

  // We defined a few WASM-specific "compile-time macros".
  var my_imports = {
    EverCrypt_TargetConfig: (mem) => ({
      hacl_can_compile_vale: 0,
      hacl_can_compile_vec128: 0,
      hacl_can_compile_vec256: 0,
      has_vec128_not_avx: () => false,
      has_vec256_not_avx2: () => false,
    }),
  };

  // The WebAssembly modules have to be initialized before calling any function.
  // To be called only if isInitialized == false.
  var loadWasm = async (modules) => {
    if (!isInitialized) {
      Module = await loader.link(
        my_imports,
        await getModulesPromise(modules)
      );
      isInitialized = true;
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
  we have to describe the correspondence between the two in the `api.json` file.

  The scheme of the JSON file is the following :
  - `module`, this module name will be shown in the JS API
    - `function`, this function name will be shown in the JS API
      - `module`, the name of the WebAssembly file where to find the function
      - 'name', the name of the WebAssembly export corresponding to the function
      - 'args', the list of the WebAssembly arguments expected by the function
        - 'name', the name of the argument which will be shown in the JS Doc
        - 'kind', either `input` or `output` of the function
        - 'type', either 'int', 'boolean', 'buffer', 'buffer(uint32)',
          'buffer(uint64)', or the name of a struct starting with an uppercase;
          for the latter case, this is understood to be a pointer (the WASM API
          does not take structs by value), and we assume the type is described
          in layouts.json -- in that case, kind is implicitly assumed to be
          input, and kind == "output" is understood to mean input-output
        - 'size', see grammar of size fields above
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

  var cell_size = type => array_type(type).BYTES_PER_ELEMENT;

  var check_array_type = function(type, candidate, length, name) {
    if (!(candidate instanceof array_type(type)) || candidate.length !== length) {
      throw new Error(
        "name: Please ensure the argument " + name + " has length " + length + " and is a " + array_type(type)
      );
    }
  };

  var copy_array_to_stack = function(type, array, i) {
    // This returns a suitably-aligned pointer.
    var pointer = loader.reserve(Module.Karamel.mem, array.length*cell_size(type), cell_size(type));
    (new Uint8Array(Module.Karamel.mem.buffer)).set(new Uint8Array(array.buffer), pointer);
    // console.log("argument "+i, "stack pointer got", loader.p32(pointer));
    // console.log(array, array.length);
    // console.log("source", array.buffer);
    // loader.dump(Module.Karamel.mem, 2048, 0x13000);
    return pointer;
  };

  // len is in number of elements
  var read_memory = function(type, ptr, len) {
    // TODO: faster path with aligned pointers?
    var result = new ArrayBuffer(len*cell_size(type));
    // console.log("New memory buffer", type, len, len*cell_size(type));
    (new Uint8Array(result).set(new Uint8Array(Module.Karamel.mem.buffer)
      .subarray(ptr, ptr + len*cell_size(type))));
    // console.log(result);
    return new (array_type(type))(result);
  };

  // HELPERS FOR HEAP LAYOUT
  // -----------------------

  // Filled out via a promise.
  var layouts;

  var heapReadBlockSize = (ptr) => {
    var m32 = new Uint32Array(Module.Karamel.mem.buffer)
    return m32[ptr/4-2]-8;
  };

  // We adopt a uniform layout and length-tag buffers upon copying them onto the
  // stack. This allows reading back layouts safely after they're modified.
  var heapWriteBlockSize = (ptr, sz) => {
    var m32 = new Uint32Array(Module.Karamel.mem.buffer)
    return m32[ptr/4-2] = sz + 8;
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
        var m8 = new Uint8Array(Module.Karamel.mem.buffer);
        return m8[ptr];

      case "A32":
        if (!(ptr % 4) == 0)
          throw new Error("malloc violation (3)");
        var m32 = new Uint32Array(Module.Karamel.mem.buffer);
        return m32[ptr/4];

      case "A64":
        if (!(ptr % 8) == 0)
          throw new Error("malloc violation (4)");
        var m64 = new BigUint64Array(Module.Karamel.mem.buffer);
        return m64[ptr/8];

      default:
        throw new Error("Not implemented: "+typ);
    }
  };

  var heapWriteInt = (typ, ptr, v) => {
    switch (typ) {
      case "A8":
        var m8 = new Uint8Array(Module.Karamel.mem.buffer);
        m8[ptr] = v;
        break;

      case "A32":
        if (!(ptr % 4) == 0)
          throw new Error("malloc violation (3)");
        var m32 = new Uint32Array(Module.Karamel.mem.buffer);
        m32[ptr/4] = v;
        break;

      case "A64":
        if (!(ptr % 8) == 0)
          throw new Error("malloc violation (4)");
        var m64 = new BigUint64Array(Module.Karamel.mem.buffer);
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
    (new Uint8Array(Module.Karamel.mem.buffer)).set(new Uint8Array(arr.buffer), ptr);
  };

  // Eventually will be mutually recursive once Layout is implemented (flat
  // packed structs).
  var heapReadType = (runtime_type, ptr) => {
    // console.log("headReadType", runtime_type, loader.p32(ptr));
    let [ type, data ] = runtime_type;
    switch (type) {
      case "Int":
        return heapReadInt(data[0], ptr);
      case "Pointer":
        if (data[0] == "Int")
          return heapReadBlockFast(data[1][0], heapReadInt("A32", ptr));
        else if (data[0] == "Layout")
          return heapReadLayout(data[1], heapReadInt("A32", ptr));
        // pass-through
      default:
        throw new Error("Not implemented: "+type+","+data);
    }
  };

  var heapWriteType = (runtime_type, ptr, v) => {
    // console.log("heapWriteType", runtime_type, loader.p32(ptr), v);
    let [ type, data ] = runtime_type;
    switch (type) {
      case "Int":
        heapWriteInt(data[0], ptr, v);
        break;
      case "Pointer":
        if (data[0] == "Int") {
          let sz = v.buffer.byteLength;
          // NB: could be more precise with alignment, I guess
          let dst = loader.reserve(Module.Karamel.mem, sz + 8, 8) + 8;
          heapWriteInt("A32", ptr, dst);
          heapWriteBlockFast(data[1][0], dst, v);
          heapWriteBlockSize(dst, sz);
          break;
        } else if (data[0] == "Layout") {
          let dst = stackWriteLayout(data[1], v);
          heapWriteInt("A32", ptr, dst);
          break;
        }
        // pass-through
      default:
        throw new Error("Not implemented: "+type);
    }
  };

  var lFlatIsTaggedUnion = data => {
    if (data.fields.length == 2 && data.fields[0][0] == "tag" && data.fields[1][0] == "val") {
      let [ tag_name, [ tag_ofs, [ tag_type, [ tag_width ]]]] = data.fields[0];
      if (!(tag_name == "tag" && tag_ofs == "0" && tag_type == "Int" && tag_width == "A32"))
        throw new Error("Inconsistent tag");
      let [ val_name, [ val_ofs, [ val_type, val_cases]]] = data.fields[1];
      if (!(val_name == "val" && val_ofs == "8" && val_type == "Union"))
        throw new Error("Inconsistent val");
      return true;
    } else {
      return false;
    }
  };

  var taggedUnionGetCase = (data, tag) => {
    let [ val_name, [ val_ofs, [ val_type, val_cases]]] = data.fields[1];
    return val_cases[tag];
  };

  var heapReadLayout = (layout, ptr) => {
    // console.log("heapReadLayout", layout, loader.p32(ptr));
    let [ tag, data ] = layouts[layout];
    switch (tag) {
      case "LFlat":
        if (lFlatIsTaggedUnion(data)) {
          let tag = heapReadInt("A32", ptr);
          return ({
            tag,
            val: heapReadType(taggedUnionGetCase(data, tag), ptr + 8)
          });
        } else {
          let o = {};
          data.fields.forEach(([field, [ ofs, typ ]]) =>
            o[field] = heapReadType(typ, ptr + ofs)
          );
          return o;
        }
      default:
        throw new Error("Not implemented: "+tag);
    }
  };

  var heapWriteLayout = (layout, ptr, v) => {
    let [ tag, data ] = layouts[layout];
    // console.log(v);
    switch (tag) {
      case "LFlat":
        if (lFlatIsTaggedUnion(data)) {
          heapWriteInt("A32", ptr, v.tag);
          heapWriteType(taggedUnionGetCase(data, v.tag), ptr + 8, v.val);
        } else {
          data.fields.forEach(([field, [ ofs, typ ]]) => {
            // console.log("Writing", v[field]);
            heapWriteType(typ, ptr + ofs, v[field]);
          });
        }
        break;
      default:
        throw new Error("Not implemented: "+tag);
    }
  };

  var stackWriteLayout = (layout, v) => {
    // console.log("stackWriteLayout", layout, v);
    let [ tag, data ] = layouts[layout];
    switch (tag) {
      case "LFlat":
        let ptr = loader.reserve(Module.Karamel.mem, data.size, 8);
        heapWriteLayout(layout, ptr, v);
        return ptr;
      default:
        throw new Error("Not implemented: "+tag);
    }
  };

  // END HELPERS FOR HEAP LAYOUT

  // The object being filled:
  // - first level of keys = modules,
  // - second level of keys = functions within a module
  var api_obj = {};

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
    var memory = new Uint32Array(Module.Karamel.mem.buffer);
    var sp = memory[0];

    // Integer arguments are either
    // - user-provided, in which case they have an interface_index
    // - automatically determined, in which case they appear in the `size` field
    //   of another buffer argument.
    // In a first pass, we need to figure out the value of all integer
    // arguments to enable lookups by name.
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
        let [ var_, var_value ] = invertSize(arg.parsedSize, args[arg.interface_index].length);
        // console.log("Determined "+var_+"="+var_value);

        if (var_ in args_int32s && var_value != args_int32s[var_])
          throw new Error("Inconsistency in sizes; previously, "+var_+"="+args_int32s[var_]+"; now "+var_value);
        args_int32s[var_] = var_value;
      } else if (arg.interface_index !== undefined) {
        // API contains e.g.:
        //   { "name": "len", "interface_index": 3 },
        //   { "name": "buf", "type": "buffer", "size": "len", "kind": "output" }
        // We know we will need `len` below when trying to allocate an array for
        // `output` -- insert it into the table.
        // Note: we are quite lax and don't require that a length be a uint32,
        // it's sometimes useful to allow it to be anything, like an address.
        args_int32s[arg.name] = args[arg.interface_index];
      }
    });

    // We have determined the value of all user-provided and synthesized
    // (computed) integer lengths. Now what happens with lengths is:
    // - when allocating a variable-length output buffer, we compute the
    //   corresponding size via evalSize, passing it the args_int32s in case the
    //   size field of the output buffer refers to a variable
    // - when computing the value of an integer argument that is not
    //   user-provided (i.e. has no interface_index), we look it up in
    //   args_int32s too

    // This returns the effective arguments for the function call (all integers,
    // some of which may be pointers on the stack). It has the side effect of
    // growing the stack and copying the input buffers onto it.
    var args = proto.args.map(function(arg, i) {
      let debug = (type, x) => {
        // console.log("Argument", i, type, loader.p32(x));
        return x;
      };
      if (arg.type.startsWith("buffer")) {
        var size;
        if (typeof arg.size === "string") {
          size = evalSize(arg.parsedSize, args_int32s, api_obj);
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
        return debug("array", copy_array_to_stack(arg.type, arg_byte_buffer, i));
      }

      if (arg.type === "bool" || arg.type === "uint32") {
        if (arg.interface_index === undefined) {
          // Variable-length argument, determined via first pass above.
          return debug("int(auto)", args_int32s[arg.name]);
        } else {
          // Regular integer argument, passed by the user.
          return debug("int", args[arg.interface_index]);
        }
      }

      // Layout... TODO: the "kind" field is unused because we do not have the
      // case where the caller allocates empty space for a layout.
      if (arg.type[0].toUpperCase() == arg.type[0]) {
        let func_arg = args[arg.interface_index];
        return debug("layout", stackWriteLayout(arg.type, func_arg));
      }

      throw Error("Unimplemented ! ("+proto.name+")");
    });
    // console.log("Arguments laid out in WASM memory");
    // args.forEach((arg, i) => console.log("argument "+i, loader.p32(arg)));
    // loader.dump(Module.Karamel.mem, 2048, args[0] - (args[0] % 0x20));

    // Calling the wasm function !
    if (proto.custom_module_name) {
      var func_name = proto.name;
    } else {
      var func_name = proto.module + "_" + proto.name;
    }
    if (!(proto.module in Module))
      throw new Error(proto.module + " is not in Module");
    if (!(func_name in Module[proto.module])) {
      console.log(Object.keys(Module[proto.module]));
      throw new Error(func_name + " is not in Module["+proto.module+"]");
    }
    var call_return = Module[proto.module][func_name](...args);

    // console.log("After function call");
    // loader.dump(Module.Karamel.mem, 256, args[0] - (args[0] % 0x20));
    //loader.dump(Module.Karamel.mem, 256, call_return - (call_return % 0x20));

    // Populating the JS buffers returned with their values read from Wasm memory
    var return_buffers = args.map(function(pointer, i) {
      let arg = proto.args[i];
      if (arg.type[0].toUpperCase() == arg.type[0] && arg.kind == "output") {
        // Layout
        return heapReadLayout(arg.type, pointer);
      } else if (arg.kind === "output") {
        // Output buffer, allocated by us above, now need to read its contents
        // out.
        var size;
        if (typeof arg.size === "string") {
          size = evalSize(arg.parsedSize, args_int32s, api_obj);
        } else {
          size = arg.size;
        }
        // console.log("About to read", protoRet.type, loader.p32(pointer), size);
        let r = read_memory(arg.type, pointer, size);
        // console.log(r);
        return r;
      } else {
        return null;
      }
    }).filter(v => v !== null);

    // Resetting the stack pointer to its old value
    memory[0] = sp;
    if ("kind" in proto.return && proto.return.kind === "layout") {
      // Heap-allocated value
      let read = proto.return.type.startsWith("buffer") ? heapReadBuffer : heapReadLayout;
      let r = read(proto.return.type, call_return);
      memory[Module.Karamel.mem.buffer.byteLength/4-1] = 0;
      return r;

      // loader.dump(Module.Karamel.mem, 2048, Module.Karamel.mem.buffer.byteLength - 2048);
      // console.log(loader.p32(call_return), r, JSON.stringify(layouts[proto.return.type], null, 2));

      // let ptr = stackWriteLayout(proto.return.type, r);
      // console.log(loader.p32(ptr));
      // loader.dump(Module.Karamel.mem, 2048, 0x13000);
      // throw new Error(func_name+": non-buffer return layout not implemented");
    }
    if (proto.return.type === "bool") {
      return [call_return === 1, return_buffers].flat();
    }
    if (proto.return.type === "uint32") {
      return [call_return >>> 0, return_buffers].flat();
    }
    if (proto.return.type === "uint64") {
      // krml convention: uint64s are sent over as two uint32s
      // console.log(call_return);
      return [BigInt(call_return[0]>>>0) + (BigInt(call_return[1]>>>0) << 32n), return_buffers].flat();
    }
    if (proto.return.type === "void") {
      return return_buffers;
    }
    throw new Error(func_name+": Unimplemented ! "+proto.return.type);
  };

  var getInitializedHaclModule = async function (modules) {
    if (!isInitialized) {
      // Load all WASM modules from network (web) or disk (node).
      await loadWasm(modules);
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

  return {
    getInitializedHaclModule: getInitializedHaclModule,
    dump: (sz, ofs) => loader.dump(Module.Karamel.mem, sz, ofs)
  };
})();

if (typeof module !== "undefined") {
  module.exports = HaclWasm;
}
