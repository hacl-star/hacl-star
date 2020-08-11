// This module expects that all custom JS files have already been brought into
// scope, that my_modules contains a list of .wasm files, and that it is
// included from a webpage.
var my_print;

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
      return main(scope);
    }).then(err => {
      my_print("... main exited with " + err);
      if (err != 0)
        throw "Main returned non-zero status";
    }).catch(e =>
      my_print(e)
    );
}
