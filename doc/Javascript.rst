Using the Javascript bindings of HACL*
======================================

To use the Javascript bindings of HACL*, please obtain the corresponding
`Node.js package <https://www.npmjs.com/package/hacl-wasm>`_. These bindings
actually call WebAssembly functions that are compiled directly from the F*
source code using the KreMLin compiler.

The `jsdoc` documentation of the package can be found `here <https://hacl-star.github.io/javascript_doc/>`_.
Please note that the API is asynchronous (it uses promises).

Example
-------

Here is a small example of how to use the library (with Node.js) :

.. code-block:: javascript

  var hacl = require("hacl-wasm");
  hacl.Curve25519.ecdh(new Uint8Array(32), new Uint8Array(32)).then(function (result) {
    // Here result contains an Uint8Array of size 32 with the DH exchange result
  });
