//jshint multistr: true

var path = require('path');
var api_json = require(path.resolve(__dirname, './api.json'));
var fs = require('fs');


// Generates a file wherez every function is exanded for doc purposes
fs.writeFile("doc/readable_api.js", (function() {

  var contents =
    "var HaclWasm = require('../api.js');\n\
/**\n\
 * Hacl bindings for Javascript using WebAssembly.\n\
 * @module Hacl\n\
 */";
  Object.keys(api_json).map(function(key_module) {
    contents += "\n\n";
    contents += "/**\n";
    contents += " * @namespace " + key_module + "\n";
    contents += " */\n";
    contents += "var  " + key_module + " = {\n";
    Object.keys(api_json[key_module]).map(function(key_func) {
      contents += "\n\n";
      contents += "/**\n";
      // Params info
      api_json[key_module][key_func].args.filter(function(arg) {
        return arg.interface_index !== undefined;
      }).sort(function(a1, a2) {
        return (a1.interface_index - a2.interface_index);
      }).map(function(arg) {
        contents += " * @param {" + arg.type + "} " + arg.name;
        if (arg.type === "buffer" && typeof arg.size === "number") {
          contents += " - size " + arg.size;
        }
        if (arg.type === "buffer" && typeof arg.size === "string") {
          contents += " - size " + arg.size;
        }
        contents += "\n";
      });
      // Return info
      if (api_json[key_module][key_func].return.type !== "void") {
        contents += " * @return {" + api_json[key_module][key_func].return.type + "}\n";
      }
      api_json[key_module][key_func].args.filter(function(arg) {
        return arg.kind === "output";
      }).map(function(arg) {
        contents += " * @return {" + arg.type + "} " + arg.name;
        if (arg.type === "buffer" && typeof arg.size === "number") {
          contents += " - size " + arg.size;
        }
        if (arg.type === "buffer" && typeof arg.size === "string") {
          contents += " - size " + arg.size;
        }
        contents += "\n";
      });
      contents += " */\n";
      contents += key_func + ": function(";
      api_json[key_module][key_func].args.filter(function(arg) {
        return arg.interface_index !== undefined;
      }).sort(function(a1, a2) {
        return a1.interface_index - a2.interface_index;
      }).map(function(arg) {
        contents += arg.name + ",";
      });
      contents += ") { " + key_func + ": HaclWasm." + key_module + "." + key_func + ".apply(null, arguments) },\n";
    });
    contents += "}\n";
    contents += "module.exports." + key_module + " = " + key_module + "\n";
  });
  return contents;
})(), 'utf8', function(err, data) {
  if (err !== null) {
    console.log(err);
  }
});
