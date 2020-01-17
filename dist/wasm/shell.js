
// To be loaded by main.js
var my_js_files = [];
var my_modules = ["WasmSupport", "FStar", "LowStar_Endianness", "C_String", "TestLib", "C", "Lib_RandomBuffer_System", "EverCrypt", "Test_NoHeap"];
var my_debug = false;

if (typeof module !== "undefined")
  module.exports = {
    my_js_files: my_js_files,
    my_modules: my_modules,
    my_debug: my_debug
  }
