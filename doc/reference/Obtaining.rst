Obtaining the source code
=========================

Picking a distribution
----------------------

Building the present repository verifies the source F* code, then proceeds to
extract it to C and ASM. We provide the results of this process in the ``dist/``
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

Building the resulting code
---------------------------

Each distribution comes with its own Makefile. It builds a static object
(libevercrypt.a) and a dynamic object (libevercrypt.{so,dll}) along with the
import library for Windows systems (libevercrypt.dll.a). On Windows, the
Makefile has been tested in a Cygwin environment equipped with the MinGW
cross-compilers. The `dist/compact-msvc` distribution works with the Microsoft
compilers, but we provide no build support (i.e. no Visual Studio project, no
NMake-compatible makefile).

Integrating the resulting code
------------------------------

- When integrating EverCrypt, one can pick a distribution, along with the
  `kremlin` directory, thus giving a "wholesale" integration of
  the EverCrypt library.
- For a more gradual integration, consumers can integrate algorithms one at a
  time, by cherry-picking the files that they are interested in. Each header
  file contains the list of other headers (and implementations) it depends on so
  it's easy to integrate, say, an individual algorithm from the HACL API.

In addition, you will need the ``dist/kremlin`` directory which contains all the
required headers from KreMLin.  In particular, these headers contain
implementations of FStar.UInt128, the module for 128-bit arithmetic. The
``kremlin/include/kremlin/internal/types.h`` header will attempt to use C
preprocessor macros to pick the right UInt128 implementation for your platform:

- 64-bit environment with GCC/Clang: hand-written implementation using
  ``unsigned __int128`` (unverified)
- MSVC: hand-written implementation using intrinsics (also unverified)
- every other case, or when ``KRML_VERIFIED_UINT128`` is defined at compile-time:
  verified (slow) implementation extracted from FStar.UInt128

