// This module expects that all custom JS files have already been brought into
// scope, that my_modules contains a list of .wasm files, and that it is
// included from a webpage.
var my_print;

// Debugging helpers
function p8(n) {
  return ("0"+Number(n).toString(16)).slice(-2);
}


function hex(m8, start, len) {
  let s = "";
  for (let i = 0; i < len; ++i)
    s += p8(m8[start + i]);
  return s;
}

// We provide a few extra definitions; these are normally compile-time macros
// and play a similar role here.
var my_imports = {
  EverCrypt_TargetConfig: (mem) => ({
    hacl_can_compile_vale: 0,
  }),
};

// Definitions manually replicated from EverCrypt_Hash.h
const EverCrypt_Hash_MD5_s = 0;
const EverCrypt_Hash_SHA1_s = 1;
const EverCrypt_Hash_SHA2_224_s = 2;
const EverCrypt_Hash_SHA2_256_s = 3;
const EverCrypt_Hash_SHA2_384_s = 4;
const EverCrypt_Hash_SHA2_512_s = 5;
const EverCrypt_Hash_Blake2S_s = 6;
const EverCrypt_Hash_Blake2B_s = 7;


// Demo of how to manually construct and copy evercrypt streaming hash state
// into the stack.
function main({ reserve, dump, my_print, hex }, scope) {
  let mem = scope.Kremlin.mem;
  let mem32 = new Uint32Array(mem.buffer);
  let mem8 = new Uint8Array(mem.buffer);
  // Save stack pointer
  let sp0 = mem32[0];

  // Based on KReMLin's AstToCFlat module, which establishes the layout for
  // structs in KReMLin's WASM backends, we look at how much space we need for a
  // `Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *`. Better
  // have the C type definitions open in another buffer. Also pass `-d cflat` to
  // KReMLin to have the layouts printed out!
  //
  // Struct (Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____):
  // ┗ Pointer (block_state): 4 bytes
  //   ┗ Struct (EverCrypt_Hash_state_s):
  //     ┗ UInt8 (tag): 1 byte BUT 7 bytes of padding (?!! KReMLin bug?!)
  //     ┗ Pointer (case_SHA2_256_s): 4 bytes
  //       ┗ 8 * 4 bytes for the internal SHA2-256 state
  // ┗ Pointer (buf): 4 bytes
  //   ┗ SHA2-256 block size: 64 bytes (see EverCrypt_Hash_Incremental_block_len)
  // ┗ UInt64 (total_len): 8 bytes
  //
  // There's a comment somewhere in AstToCFlat that says that structs are 64-bit
  // aligned. So...
  let need =
    /* Incremental state (starting 64-bit aligned), 2 * Pointer + UInt64 */ 16 +
    /* Block state (still 64-bit aligned), UInt8 + 3 + Pointer */ 12 +
    /* Internal hash state */ 32 +
    /* Block buffer */ 64 +
    /* Padding in case we need to realign */ 8;
  let p = reserve(mem, need);
  let align64 = p => (p % 8 == 0) ? p : p + (8 - p % 8);
  p = align64(p);

  let incremental_state = p;
  let block_state = incremental_state + 16;
  let internal_hash_state = block_state + 12;
  let block_buffer = internal_hash_state + 32;

  // Debug
  // console.log("incremental_state", incremental_state);
  // console.log("block_state", block_state);
  // console.log("internal_hash_state", internal_hash_state);
  // console.log("block_buffer", block_buffer);
  // window.m8 = mem8;
  // window.m32 = mem32;

  // Construct the object graph.
  mem32[incremental_state/4] = block_state;
  mem32[incremental_state/4 + 1] = block_buffer;
  mem8[block_state] = EverCrypt_Hash_SHA2_256_s;
  mem32[block_state/4 + 2] = internal_hash_state;

  console.log("STREAMING: init");
  scope.EverCrypt_Hash.EverCrypt_Hash_Incremental_init(incremental_state);

  console.log("STREAMING: update");
  let sp = mem32[0];
  let hello = reserve(mem, 5);
  mem8[hello] = "hello".charCodeAt(0);
  mem8[hello+1] = "hello".charCodeAt(1);
  mem8[hello+2] = "hello".charCodeAt(2);
  mem8[hello+3] = "hello".charCodeAt(3);
  mem8[hello+4] = "hello".charCodeAt(4);
  scope.EverCrypt_Hash.EverCrypt_Hash_Incremental_update(incremental_state, hello, 5);
  mem32[0] = sp;

  console.log("STREAMING: finish");
  let dst = reserve(mem, 32);
  scope.EverCrypt_Hash.EverCrypt_Hash_Incremental_finish(incremental_state, dst);
  console.log("Hash is:", hex(mem8, dst, 32));
  mem32[0] = sp;
  mem32[0] = sp0;

  return 0;
}

function kremlin_start () {
  my_print = (...msg) =>
    document.getElementById("terminal").appendChild(
      document.createTextNode(msg.join(" ")+"\n"));

  if (!("my_imports" in this))
    this.my_imports = {};

  if (!("WebAssembly" in this))
    my_print("Error: WebAssembly not enabled. Use Chrome Canary?");

  my_print("... assembling WASM modules " + my_modules);
  return Promise.all(my_modules.map(m => fetch(m + ".wasm")))
    .then(responses =>
      Promise.all(responses.map(r => r.arrayBuffer()))
    ).then(bufs =>
      link(my_imports, bufs.map((b, i) => ({ buf: b, name: my_modules[i] }))))
    .then(scope => {
      for (let m of Object.keys(scope)) {
        if ("main" in scope[m]) {
          my_print("... main found in module " + m);
          return scope[m].main(scope);
        }
      }
      if (!("main" in window)) {
        my_print("... no main in current window");
        throw "Aborting";
      }
      return main({ reserve, dump, my_print, hex }, scope);
    }).then(err => {
      my_print("... main exited with " + err);
      if (err != 0)
        throw "Main returned non-zero status";
    }).catch(e => {
      my_print(e);
      throw e;
    });
}
