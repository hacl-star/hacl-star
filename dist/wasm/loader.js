// This module performs low-level WASM manipulations, such as linking several
// modules together and inspecting the debug zone at the bottom of the memory.
// This module is aware of the compilation strategy of kreMLin. It can be
// included from either a browser or a shell context, as long as my_print is
// defined in scope.

"use strict";

var my_print, my_random;

// When loaded "as is" via d8 or ch, we inherit the caller's scope. When loaded
// via node, we don't, so we redefine my_print.
if (typeof process !== "undefined") {
  my_print = console.log;
  let crypto = require("crypto");
  my_random = (mem, addr, len) => {
    var m8 = new Uint8Array(mem.buffer);
    crypto.randomFillSync(m8, addr, len);
    return true;
  };
} else {
  my_random = (mem, addr, len) => {
    throw new Error("TODO: random bytes for non-Node platforms");
  };
}

/******************************************************************************/
/* Some printing helpers                                                      */
/******************************************************************************/

function p8(n) {
  return ("0"+Number(n).toString(16)).slice(-2);
}

function hex(m8, start, len) {
  let s = "";
  for (let i = 0; i < len; ++i)
    s += p8(m8[start + i]);
  return s;
}

function hexle(m8, i, m) {
  let buf = "";
  let n = m - 1;
  while (n >= 0) {
    buf += p8(m8[i+n]);
    n--;
  }
  return buf;
}

function hex32(m8, start) {
  return hexle(m8, start, 4);
}

function hex64(m8, start) {
  return hexle(m8, start, 8);
}

function p32(n) {
  return p8((n >>> 24) & 255) + p8((n >>> 16) & 255) + p8((n >>> 8) & 255) + p8(n & 255);
}

function dump(mem, size) {
  let m8 = new Uint8Array(mem.buffer);
  let i = 0;
  let buf = "";
  while (i < size) {
    buf += p32(i) + "    ";
    for (let j = 0; j < 32; ++j) {
      buf += p8(m8[i+j]);
      if (j % 4 == 3)
        buf += " ";
    }
    buf += "    ";
    for (let j = 0; j < 32; ++j) {
      let c = m8[i+j];
      if (32 <= c && c < 128)
        buf += String.fromCharCode(c);
      else
        buf += ".";
    }
    buf += "\n";
    i += 32;
  }
  my_print(buf);
}

/******************************************************************************/
/* Implementations of the kremlin runtime support library                     */
/******************************************************************************/

function stringAtAddr(mem, addr) {
  let m8 = new Uint8Array(mem.buffer);
  let buf = "";
  while (m8[addr] != 0) {
    buf += String.fromCharCode(m8[addr++]);
  }
  return buf;
}

function readLeAtAddr(mem, addr, bytes) {
  let m8 = new Uint8Array(mem.buffer);
  let i = 0;
  while (bytes-- > 0)
    i = (i << 8) + m8[addr + bytes];
  return i;
}

function writeLeAtAddr(mem, addr, n, bytes) {
  let m8 = new Uint8Array(mem.buffer);
  for (let i = 0; i < bytes; ++i) {
    m8[addr + i] = n & 255;
    n >>>= 8;
  }
}

function writeBeAtAddr(mem, addr, n, bytes) {
  let m8 = new Uint8Array(mem.buffer);
  while (bytes > 0) {
    m8[addr + bytes - 1] = n & 255;
    bytes--;
    n >>>= 8;
  }
}

function dummyModule(funcs, globals) {
  let module = {};
  for (let f of funcs)
    module[f] = () => {
      my_print("Not implemented: " + s);
      throw new Error();
    };
  for (let g of globals)
    module[g] = 0;
  return module;
}

let mkWasmSupport = (mem) => ({
  WasmSupport_trap: () => {
    dump(mem, 2*1024);
    my_print("Run-time trap, e.g. zero-sized array or abort.");
    throw new Error();
  }
});

let mkFStar = () => dummyModule(
  [ "FStar_UInt128_constant_time_carry_ok", "FStar_PropositionalExtensionality_axiom" ],
  [ "FStar_Monotonic_Heap_lemma_mref_injectivity" ]);

let mkPrims = (mem) => ({
  Prims_op_Addition: (x, y) => { return x + y; }
});

let mkC = (mem) => ({
  srand: () => { throw new Error("todo: srand") },
  rand: () => { throw new Error("todo: rand") },
  exit: (errno) => { throw new Error("Program exited via C.exit [errno="+errno+"]") },
  portable_exit: (errno) => { throw new Error("Program exited via C.portable_exit [errno="+errno+"]") },
  print_bytes: () => { throw new Error("todo: print_bytes") },

  char_uint8: () => { throw new Error("todo: char_uint8") },
  uint8_char: () => { throw new Error("todo: uint8_char") },
  char_of_uint8: (x) => { throw new Error("todo: char_of_uint8") },
  uint8_of_char: (x) => { throw new Error("todo: uint8_of_char") },

  // A Prims_string generates a literal allocated in the data segment;
  // string_of_literal is just a typing trick.
  string_of_literal: (x) => x,
  print_string: (addr) => my_print(stringAtAddr(mem, addr)),

  // Truncated
  clock: () => Date.now(),
});

let mkLibRandomBufferSystem = (mem) => ({
  Lib_RandomBuffer_System_randombytes: (addr, len) => { return my_random(mem, addr, len); }
});

let mkLibMemzero = (mem) => ({
  Lib_Memzero_clear_words_u8: (nwords, addr) => {
    let m8 = new Uint8Array(mem.buffer);
    for (let i = 0; i < nwords; ++i) {
      m8[addr+i] = 0;
    }
  },
  Lib_Memzero_clear_words_u16: (nwords, addr) => {
    let m8 = new Uint8Array(mem.buffer);
    for (let i = 0; i < nwords; ++i) {
      m8[addr+2*i] = 0;
      m8[addr+2*i+1] = 0;
    }
  }
});

let mkLowStarEndianness = (mem) => ({
  htole16: (x) => { throw new Error("todo: htole16") },
  le16toh: (x) => { throw new Error("todo: le16toh") },
  htole32: (x) => { throw new Error("todo: htole32") },
  le32toh: (x) => { throw new Error("todo: le32toh") },
  htole64: (x) => { throw new Error("todo: htole64") },
  le64toh: (x) => { throw new Error("todo: le64toh") },
  htobe16: (x) => { throw new Error("todo: htobe16") },
  be16toh: (x) => { throw new Error("todo: be16toh") },
  htobe32: (x) => { throw new Error("todo: htobe32") },
  be32toh: (x) => { throw new Error("todo: be32toh") },
  htobe64: (x) => { throw new Error("todo: htobe64") },
  be64toh: (x) => { throw new Error("todo: be64toh") },
  index_32_be: (x) => { throw new Error("todo: index_32_be") },
  index_32_le: (x) => { throw new Error("todo: index_32_le") },
  index_64_be: (x) => { throw new Error("todo: index_64_be") },
  index_64_le: (x) => { throw new Error("todo: index_64_le") },
  // all of these: implemented natively in CFlatToWasm
  store16_le: (addr, n) => { throw new Error("todo: store16_le") },
  load16_le: (addr) => { throw new Error("todo: load16_le") },
  store16_be: (addr, n) => { throw new Error("todo: store16_be") },
  load16_be: (addr) => { throw new Error("todo: load16_be") },
  store32_le: (addr, n) => { throw new error("todo: store32_le") },
  store32_be: (addr, n) => { throw new error("todo: store32_be") },
  load32_be: (addr) => { throw new Error("todo: load32_be") },
  store64_le: (addr, n) => { throw new Error("todo: store64_le") },
  load64_le: (addr) => { throw new Error("todo: load64_le") },
  store64_be: (addr, n) => { throw new Error("todo: store64_be") },
  load64_be: (addr) => { throw new Error("todo: load64_be") },
  store128_le: (addr, n) => { throw new Error("todo: store128_le") },
  load128_le: (addr) => { throw new Error("todo: load128_le") },
  store128_be: (addr, n) => { throw new Error("todo: store128_be") },
  load128_be: (addr) => { throw new Error("todo: load128_be") },
  // this definition works for both C.Endianness and LowStar.Endianness
  store16_le_i: (addr, n) => { throw new Error("todo_i: store16_le") },
  load16_le_i: (addr) => { throw new Error("todo_i: load16_le") },
  store16_be_i: (addr, n) => { throw new Error("todo_i: store16_be") },
  load16_be_i: (addr) => { throw new Error("todo_i: load16_be") },
  store32_le_i: (addr, n) => { throw new error("todo_i: store32_le") },
  store32_be_i: (addr, n) => { throw new error("todo_i: store32_be") },
  load32_be_i: (addr) => { throw new Error("todo_i: load32_be") },
  store64_le_i: (addr, n) => { throw new Error("todo_i: store64_le") },
  load64_le_i: (addr) => { throw new Error("todo_i: load64_le") },
  store64_be_i: (addr, n) => { throw new Error("todo_i: store64_be") },
  load64_be_i: (addr) => { throw new Error("todo_i: load64_be") },
  store128_le_i: (addr, n) => { throw new Error("todo_i: store128_le") },
  load128_le_i: (addr) => { throw new Error("todo_i: load128_le") },
  store128_be_i: (addr, n) => { throw new Error("todo_i: store128_be") },
  load128_be_i: (addr) => { throw new Error("todo_i: load128_be") }
});

let mkCNullity = (mem) => ({
  C_Nullity_is_null: () => { throw new Error("todo: is_null") }
});

let mkCString = (mem, prefix) => ({
  [prefix + '_print']: (ptr) => my_print(stringAtAddr(mem, ptr)),
  [prefix + '_of_literal']: (ptr) => { throw new Error("primitive: "+prefix+"_of_literal") },
  [prefix + '_strlen']: (ptr) => {
    let m8 = new Uint8Array(mem.buffer);
    let ofs = 0;
    while (m8[ptr+ofs] != 0)
      ofs++;
    return ofs;
  },
  [prefix + '_memcpy']: (dst, src, n) => {
    let m8 = new Uint8Array(mem.buffer);
    let i = 0;
    while (i < n) {
      m8[dst+i] = m8[src+i];
      i++;
    }
  },
});

function checkEq(mem, name) {
  return (x1, x2) => {
    if (x1 != x2) {
      dump(mem, 2*1024);
      my_print(name + ": equality failure, "+x1+" != "+x2);
      throw new Error();
    }
    return 0;
  };
}

let mkTestLib = (mem, prefix) => ({
  [prefix + '_touch']: () => 0,
  [prefix + '_check8']: checkEq(mem, prefix+"_check8"),
  [prefix + '_check16']: checkEq(mem, prefix+"_check16"),
  [prefix + '_check32']: checkEq(mem, prefix+"_check32"),
  [prefix + '_check64']: checkEq(mem, prefix+"_check64"),
  [prefix + '_checku8']: checkEq(mem, prefix+"_checku8"),
  [prefix + '_checku16']: checkEq(mem, prefix+"_checku16"),
  [prefix + '_checku32']: checkEq(mem, prefix+"_checku32"),
  [prefix + '_checku64']: checkEq(mem, prefix+"_checku64"),
  [prefix + '_check']: (b) => {
    if (!b) {
      dump(mem, 2*1024);
      my_print(prefix+"_check: assertion failure");
      throw new Error();
    }
    return 0;
  },
  [prefix + '_unsafe_malloc']: () => { throw new Error("todo: unsafe_malloc") },
  [prefix + '_perr']: (err) => {
    my_print("Got error code "+err);
    return 0;
  },
  [prefix + '_uint8_p_null']: 0,
  [prefix + '_uint32_p_null']: 0,
  [prefix + '_uint64_p_null']: 0,
  [prefix + '_compare_and_print']: (addr, b1, b2, len) => {
    let m8 = new Uint8Array(mem.buffer);
    let str = stringAtAddr(m8, addr);
    let hex1 = hex(m8, b1, len);
    let hex2 = hex(m8, b2, len);
    my_print("[test] expected output "+str+" is "+hex1);
    my_print("[test] computed output "+str+" is "+hex2);
    for (let i = 0; i < len; ++i) {
      if (m8[b1+i] != m8[b2+i]) {
        my_print("[test] reference "+str+" and expected "+str+" differ at byte "+i);
        my_print("b1="+p32(b1)+",b2="+p32(b2));
        dump(mem, 4*1024);
        throw new Error("test failure");
      }
    }
    my_print("[test] "+str+" is a success\n");
  },
  [prefix + '_print_clock_diff']: (t1, t2) => {
    my_print("[benchmark] took: " + (t2 - t1) + "ms\n");
  },
});

/******************************************************************************/
/* Memory layout                                                              */
/******************************************************************************/

// mem[0..3] = top-of-the-stack pointer (I32);
// mem[4..127] = scratch space for debugging.
// Conventions for debugging and "debugging format" (lolz) are in WasmDebug.ml
const header_size = 128;

// this sets up the base data pointer and the debug entry point for the WASM
// context; WASM-generated code expects to have these defined.
function init() {
  let mem = new WebAssembly.Memory({ initial: 16 });
  let m8 = new Uint8Array(mem.buffer);
  let nest = 0;

  let debug = () => {
    let i = 0;
    let buf = "";
    let string = () => {
      let ptr = m8[i] + (m8[i+1] << 8) + (m8[i+2] << 16) + (m8[i+3] << 24);
      i += 4;
      while (m8[ptr] != 0) {
        buf += String.fromCharCode(m8[ptr]);
        ptr++;
      }
    };
    let int32 = () => {
      buf += "0x";
      buf += hex32(m8, i);
      i += 4;
    };
    let int64 = () => {
      buf += "0x";
      buf += hex64(m8, i);
      i += 8;
    };
    // Dump the stack pointer
    int32();
    buf += " | ";
    buf += " ".repeat(nest);
    while (m8[i] != 0 && i < 128) {
      let c = m8[i];
      i++;
      switch (c) {
        case 1:
          string();
          break;
        case 2:
          int32();
          break;
        case 3:
          int64();
          break;
        case 4:
          nest++;
          break;
        case 5:
          nest--;
          break;
        default:
          my_print(hex(m8, 0, 128));
          throw "unrecognized debug format:\n  buf="+buf+"\n  c=0x"+p8(c)+"\n  i="+i;
      }
      buf += " ";
    }
    my_print(buf);
  };

  // Initialize the highwater mark.
  new Uint32Array(mem.buffer)[0] = header_size;

  // Base stuff that appears as requirement, because they're exposed in TestLib
  // and/or C.
  let imports = {
    Kremlin: {
      mem: mem,
      debug: debug,
      data_start: header_size
    },
    WasmSupport: mkWasmSupport(mem),
    FStar: mkFStar(mem),
    Prims: mkPrims(mem),
    LowStar_Endianness: mkLowStarEndianness(mem),
    C: mkC(mem),
    C_Compat: mkC(mem),
    C_Endianness: mkLowStarEndianness(mem),
    C_Compat_Endianness: mkLowStarEndianness(mem),
    C_Nullity: mkCNullity(mem),
    C_String: mkCString(mem, 'C_String'),
    C_Compat_String: mkCString(mem, 'C_Compat_String'),
    TestLib: mkTestLib(mem, 'TestLib'),
    TestLib_Compat: mkTestLib(mem, 'TestLib_Compat'),
    Lib_RandomBuffer_System: mkLibRandomBufferSystem(mem),
    Lib_Memzero: mkLibMemzero(mem)
  };
  return imports;
}

// One MUST call this function after loading a module.
function propagate(module_name, imports, instance) {
  my_print("Module", module_name, "successfully loaded");
  my_print("Adding exports into global import table:\n ", Object.keys(instance.exports));
  if (!(module_name in imports))
    imports[module_name] = {};
  for (let o of Object.keys(instance.exports)) {
    imports[module_name][o] = instance.exports[o];
  }
  my_print("This module has a data segment of size: ", instance.exports.data_size);
  imports.Kremlin.data_start += instance.exports.data_size;
  my_print("Next data segment will start at: ", imports.Kremlin.data_start);
  // Set the highwater mark right after the data segment
  new Uint32Array(imports.Kremlin.mem.buffer)[0] = imports.Kremlin.data_start;
  my_print();
}

// One MAY only call this function after all modules have been loaded and
// suitable calls to propagate have been performed.
function reserve(mem, size) {
  let m32 = new Uint32Array(mem.buffer);
  let p = m32[0];
  m32[0] += size;
  my_print("Reserved memory area 0x"+p32(p)+"..0x"+p32(m32[0]));
  return p;
}

function link(imports, modules) {
  let fold = async (imports, modules) => {
    if (!modules.length)
      return imports;

    let [{ name, buf }, ...ms] = modules;
    // Note: this may throw with:
    //   error: module is not an object or function
    // This merely indicates a missing import. Look at the .wast to figure it
    // out.
    my_print("Attempting to instantiate", name);
    let { module, instance } = await WebAssembly.instantiate(buf, imports);
    propagate(name, imports, instance);
    return fold(imports, ms);
  };

  let i = init ();
  my_print("Custom imports:", imports);
  for (let k in imports)
    i[k] = imports[k](i.Kremlin.mem);

  return fold(i, modules);
}

if (typeof module !== "undefined")
  module.exports = {
    link: link,
    reserve: reserve,
    dump: dump
  };
