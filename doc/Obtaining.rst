Using the crypto library
=========================

Picking a distribution
----------------------

Building the full ``hacl-star`` repository verifies the source F* and Vale code,
then proceeds to extract it to C and assembly. However, users do not have to use
this full build process: we provide the generated code in the ``dist/``
directory, under version control to facilitate obtaining the source code.

Each subdirectory corresponds to a *distribution*, i.e. a particular set of
options passed to KreMLin (the F*-to-C compiler) that influence how the
generated C code looks like.

There is a total order on distributions:
``c89-compatible <= msvc-compatible <= gcc-compatible <= gcc64-only``

- The C89 distribution will work with the most C compilers; it relies on
  ``alloca``; eliminates compound literals and enforces C89 scope to generate
  syntactically C89-compliant code; code still relies on inttypes.h and other
  headers that you may have to provide depending on your target. It does not
  include Merkle Trees and the code is incredibly verbose.
- The MSVC distribution relies on ``alloca`` to avoid C11 VLA for the sake of
  MSVC; relies on KreMLin for tail-call optimizations. It also does not use GCC
  inline assembly for Curve25519 and uses external linkage instead.
- The GCC distribution relies on C11 VLA and therefore does not work with MSVC.
- The GCC64 distribution assumes a native ``unsigned __int128`` type which can be
  manipulated via the standard arithmetic operators. This generates very compact
  code but only works on 64-bit GCC and Clang.

Other distributions are either for distinguished consumers of our code who need
specific KreMLin compilation options (e.g. Mozilla, CCF) or for testing (e.g.
portable-gcc-compatible, which compiles without ``-march=native``, to ensure all
our assumptions about CPU targets are explicit in our Makefile).

Compiling a full distribution
-----------------------------

Each distribution comes with its own Makefile. It builds a static object
(libevercrypt.a) and a dynamic object (libevercrypt.{so,dll}) along with the
import library for Windows systems (libevercrypt.dll.a). On Windows, the
Makefile has been tested in a Cygwin environment equipped with the MinGW
cross-compilers. The `dist/compact-msvc` distribution works with the Microsoft
compilers, but we provide no build support (i.e. no Visual Studio project, no
NMake-compatible makefile).

.. note::

  The ``gcc-compatible`` distribution also features OCaml bindings to our code.
  These require a valid OCaml setup, including packages ctypes, ctypes-foreign
  and bigstring, usually obtained via OPAM. You can easily disable building
  these bindings by removing the ``lib_gen`` directory in
  ``dist/gcc-compatible``.

Integrating the code
--------------------

To incoroporate our verified crypto code into a C software project, a developer
has two choices.

- Pick a full EverCrypt distribution, along with the
  `dist/kremlin` directory, thus giving a "wholesale" integration of
  the EverCrypt library, including all supported algorithms from HACL* and Vale.
- For a more selective integration, cherry-pick the C or assembly
  files for specific versions of specific algorithms.  Each header
  file contains the list of other headers (and implementations) it
  depends on so it's easy to integrate, say, an individual algorithm
  from the HACL API without taking the full library.

The ``dist/kremlin`` directory contains all the required headers from
KreMLin.  In particular, these headers contain implementations of
FStar.UInt128, the module for 128-bit arithmetic. The
``kremlin/include/kremlin/internal/types.h`` header will attempt to
use C preprocessor macros to pick the right UInt128 implementation for
your platform:

- 64-bit environment with GCC/Clang: hand-written implementation using
  ``unsigned __int128`` (unverified)
- MSVC: hand-written implementation using intrinsics (also unverified)
- every other case, or when ``KRML_VERIFIED_UINT128`` is defined at compile-time:
  verified (slow) implementation extracted from FStar.UInt128


Bindings for Other Languages
----------------------------

HACL* and EverCrypt are designed to primarily be used either within
verification-oriented projects in F* or as part of larger C
developments.  In addition to these use cases, the library developers
and other HACL* users have also developed bindings for other programming languages:

OCaml
^^^^^

The KReMLin compiler auto-generates ``ocaml-ctypes`` bindings for HACL*. On top
of these "raw" bindings, we add a high-level wrapper that uses functors, shares
type signatures, performs run-time checks and offers a much more idiomatic API.

The former can be installed by running ``make install-hacl-star-raw`` in
``dist/gcc-compatible``. The latter can be installed by running ``dune build &&
dune install`` in ``bindings/ocaml``.

We expect these to be available in OPAM soon.

JavaScript
^^^^^^^^^^

HACL* is compiled to WebAssembly via the WASM backend of KreMLin (see the
Oakland'19 paper for details). We offer an idiomatic JavaScript API on top of
HACL-WASM so that clients do not have to be aware of the KreMLin memory layout,
calling convention, etc. This latter API is available as a
`Node.js package <https://www.npmjs.com/package/hacl-wasm>`_.

The `jsdoc` documentation of the package can be found `online
<https://hacl-star.github.io/javascript_doc/>`_.  Please note that the API is
asynchronous (it uses promises).

Here is a small example of how to use the library (with Node.js) :

.. code-block:: javascript

  var hacl = require("hacl-wasm");
  hacl.Curve25519.ecdh(new Uint8Array(32), new Uint8Array(32)).then(function (result) {
    // Here result contains an Uint8Array of size 32 with the DH exchange result
  });

Rust
^^^^

Various users have also published Rust crates for HACL*, but these have not been
vetted by the HACL maintainers.
