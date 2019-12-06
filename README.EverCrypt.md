# EverCrypt: A Verified Crypto Provider <br>Engineered for Agile, Multi-Platform Performance

EverCrypt is a formally verified modern cryptographic provider
that provides cross-platform support as well as platform-specific optimizations
that are automatically enabled if processor support is detected (*multiplexing*).
Furthermore, EverCrypt offers an (*agile*) API that makes it simple to
switch between algorithms (e.g., from SHA2 to SHA3).

EverCrypt is written and verified using the [F\*] programming language, then
compiled to a mixture of C (using a dedicated compiler, [KreMLin]) and assembly.

EverCrypt's formal verification involves using software tools to analyze *all
possible behaviors* of a program and prove mathematically that they comply with
the code's specification (i.e., a machine-readable description of the
developer's intentions). Unlike software testing, formal verification provides
strong guarantees that a program behaves as expected and is free from entire
classes of errors.

For EverCrypt, our specifications cover a range of properties, including:

* Memory safety: EverCrypt never violates memory abstractions,
  and, as a consequence, is free from common bugs and vulnerabilities like
  buffer overflows, null-pointer dereferences, use-after-frees, double-frees,
  etc.

* Type safety: EverCrypt respects the interfaces amongs its components
  including any abstraction boundaries; e.g., one component never passes
  the wrong kind of parameters to another, or accesses its private state.

* Functional correctness: EverCrypt's input/output behavior is fully
  characterized by simple mathematical functions derived directly
  from the official cryptographic standards (e.g., from NIST or the IETF).

* Side-channel resistance: Observations about EverCrypt's low-level behavior
  (specifically, the time it takes to execute or the memory addresses that it
  accesses) are independent of the secrets manipulated by the library. Hence, an
  adversary monitoring these "side-channels" learns nothing about the secrets.

All of these guarantees *do not* prevent EverCrypt from achieving good performance!
EverCrypt meets or beats the performance of most existing cryptographic implementations in C,
and for certain targeted platforms meets or beats the performance of state-of-the-art
libraries that rely on hand-tuned assembly code.

Portions of EverCrypt are being used in [Firefox](https://bugzilla.mozilla.org/show_bug.cgi?id=1387183), the Windows kernel,
the [Tezos blockchain](https://www.reddit.com/r/tezos/comments/8hrsz2/tezos_switches_cryptographic_libraries_from/),
and the [Wireguard VPN](https://lwn.net/Articles/770750/).  

EverCrypt is developed as part of [Project Everest](https://project-everest.github.io/), 
which aims to build and deploy a verified HTTPS stack.

# Algorithms Supported by EverCrypt

EverCrypt is a work in progress!  Many algorithms are still under development.
In upcoming releases, we aim to include:
- fallback C versions for all algorithms
- NIST P curves
- AES-CBC

| Algorithm           | C version                | ASM version                | Agile API |
| ------------------- | ------------------------ | -------------------------- | --------- |
| **AEAD**            |                          |                            |           |
| AES-GCM             |                          | ✔︎ (AES-NI + PCLMULQDQ)     | ✔︎         |
| ChachaPoly          | ✔︎¹                       |                            | ✔︎         |
|                     |                          |                            |           |
| **Hashes**          |                          |                            |           |
| MD5                 | ✔︎²                       |                            | ✔︎         |
| SHA1                | ✔︎²                       |                            | ✔︎         |
| SHA2                | ✔︎                        | ✔︎³ (SHAEXT)               | ✔︎         |
| SHA3                | ✔︎                        |                            |           |
| Blake2              | ✔︎                        |                            |           |
|                     |                          |                            |           |
| **MACS**            |                          |                            |           |
| HMAC                | ✔︎⁴                       |                            | ✔︎         |
| Poly1305            | ✔︎  (+ AVX + AVX2)        | ✔︎ (X64)                    |           |
|                     |                          |                            |           |
| **Key Derivation**  |                          |                            |           |
| HKDF                | ✔︎⁴                       |                            | ✔︎         |
|                     |                          |                            |           |
| **ECC**             |                          |                            |           |
| Curve25519          | ✔︎                        | ✔︎ (BMI2 + ADX)             |           |
| Ed25519             | ✔︎                        |                            |           |
|                     |                          |                            |           |
| **Ciphers**         |                          |                            |           |
| Chacha20            | ✔︎                        |                            |           |
| AES128, 256         |                          | ✔︎ (AES NI + PCLMULQDQ)     |           |
| AES CTR             |                          | ✔︎ (AES NI + PCLMULQDQ)     |           |

¹: does not multiplex (yet) over the underlying Poly1305 implementation  
²: insecure algorithms provided for legacy interop purposes  
³: SHA2-256 only; SHA2-224, SHA2-384 and SHA2-512 are pure C  
⁴: HMAC and HKDF on top of the agile hash API, so HMAC-SHA2-256 and
   HKDF-SHA2-256 leverage the assembly version under the hood  

# Building or Integrating EverCrypt

⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️

EverCrypt is a work in progress -- if you're seriously contemplating using
this code is a real system, get in touch with us first!

⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️⚠️

## Current limitations

As we work our way towards our first official release, bear in mind that:
- only X64 is supported at the moment
- many algorithms are still under development (see above).

## Finding the code EverCrypt produces

The generated code is under version control in the present repository. This is
by far the easiest way to obtain a copy of EverCrypt.

EverCrypt's C/ASM code is packaged as a set of self-contained files in one of the
`dist/*` directories where `*` is the name of a distribution. A distribution
corresponds to a particular flavor of generated C code.

There is a total order on distributions, where:

```
c89-compatible <= msvc-compatible <= gcc-compatible <= gcc64-only
```

- The C89 distribution will work with the most C compilers; it relies on
  `alloca`; eliminates compound literals and enforces C89 scope to generate
  syntactically C89-compliant code; code still relies on inttypes.h and other
  headers that you may have to provide depending on your target. It does not
  include Merkle Trees and the code is very verbose.
- The MSVC distribution relies on `alloca` to avoid C11 VLA for the sake of
  MSVC; relies on KreMLin for tail-call optimizations. It also does not use GCC
  inline assembly for Curve25519 and uses external linkage instead.
- The GCC distribution relies on C11 VLA and therefore does not work with MSVC.
- The GCC64 distribution assumes a native `unsigned __int128` type which can be
  manipulated via the standard arithmetic operators. This generates very compact
  code but only works on 64-bit GCC and Clang.

In addition to picking one of these distributions, you will need the
`dist/kremlin` directory which contains all the required headers from KreMLin.
In particular, these headers contain implementations of FStar.UInt128, the
module for 128-bit arithmetic. The `kremlin/include/kremlin/internal/types.h`
header will attempt to use C preprocessor macros to pick the right UInt128
implementation for your platform:
- 64-bit environment with GCC: hand-written implementation using `unsigned
  __int128` (unverified)
- MSVC: hand-written implementation using intrinsics (also unverified)
- every other case, or when `KRML_VERIFIED_UINT128` is defined at compile-time:
  verified (slow) implementation extracted from FStar.UInt128

Other distributions are either for distinguished consumers of our code who need
specific KreMLin compilation options (e.g. Mozilla, CCF) or for testing (e.g.
portable-gcc-compatible, which compiles without `-march=native`, to ensure all
our assumptions about CPU targets are explicit in our Makefile).

## Integrating EverCrypt with your code

Each distribution of EverCrypt contains a GNU Makefile that generates a static
library and a shared object. The code depends on KreMLin's includes, provided in
`dist/kremlin`.

- When integrating EverCrypt, one can pick a distribution, along with the
  `kremlin` directory, thus giving a "wholesale" integration of
  the EverCrypt library.
- For a more gradual integration, consumers can integrate algorithms one at a
  time, by cherry-picking the files that they are interested in. Each header
  file contains the list of other headers (and implementations) it depends on.

Customizing distributions is easy; contact us if you need something bespoke
(e.g., EverCrypt as single file).

## Verifying and building EverCrypt with Docker

Verifying and building EverCrypt from scratch is fairly involved and requires several tools.
Hence the simplest approach is to look up the latest tag for the [HACL\* docker
container](https://cloud.docker.com/u/projecteverest/repository/docker/projecteverest/hacl-star-linux)
then retrieve it using `docker pull`. Please make sure you run `git rev-parse
origin/fstar-master` to get the latest commit hash, and please avoid builds
marked as failed.

## Verifying and building EverCrypt locally

We strongly recommend using the Everest script (as shown below)
to verify and build EverCrypt.

```bash
$ git clone https://github.com/project-everest/everest/
$ cd everest
$ ./everest check
$ # Keep trying everest check until all requirements are met
$ ./everest pull
$ # Follow suggestions and export FSTAR_HOME, KREMLIN_HOME, HACL_HOME
$ ./everest FStar make kremlin make
$ # At this stage all dependencies have been fetched and built
$ cd hacl-star
$ make -j
```

# Code Layout

The [specs/](specs/) directory contains the algorithmic specifications for our
algorithms, which capture their intended semantics. Our specifications are
written in F\*, then extracted to OCaml and executed on test vectors to rule out
errors.  Specifications run inefficiently and only serve as a concise,
auditable, high-level reference which efficient, low-level algorithms are
intended to implement.

To implement efficient, low-level, optimized code, HACL\* relies on Low\*, a
subset of F\*. Programs written in Low\* compile to readable, idiomatic C code
using the [KreMLin] compiler. Our implementations are found in the
[code/](code/) directory.

The [vale/](vale/) subdirectory of the present repository contains verified
assembly implementations of popular algorithms, written in Vale, along with a
memory model that supports interop between Low\* programs and Vale code, written
in F\*.

# Applications

This repository also contains one verified application built on top of EverCrypt.

## Merkle Trees

We offer a Merkle Tree library, implementing fast cryptographic hashes for
blockchains, in [secure_api/merkle_tree](secure_api/merkle_tree).

Merkle Trees are included in every distribution except for the C89 one.

# Components of EverCrypt

EverCrypt brings together several components of [Project Everest],
which aims to build and deploy a verified HTTPS stack.

## HACL\*: Verified C-level Cryptographic Code

[HACL\*](README.HACL.md), the High-Assurance Cryptographic Library,
is a formally verified cryptographic library providing efficient implementations
of popular algorithms; it compiles to C, using the [KreMLin] compiler.

## Vale: Verified Cryptographic Assembly Code

[Vale] (Verified Assembly Language for Everest) is a tool for constructing
formally verified high-performance assembly language code, with an emphasis on
cryptographic code.  It supports multiple architectures, such as x86, x64, and
ARM, and multiple platforms, such as Windows, Mac, and Linux. Additional
architectures and platforms can be supported with no changes to the Vale tool.

## Verification Tools

EverCrypt is developed in [F\*], a programming language with support for
program verification. To implement efficient, low-level, optimized code,
EverCrypt relies on [Low\*], a subset of F\*.  Programs written in Low\* compile
to readable, idiomatic C code using the [KreMLin] compiler.

# Research

[EverCrypt: A Fast, Verified, Cross-Platform Cryptographic Provider](https://eprint.iacr.org/2019/757)  
Jonathan Protzenko, Bryan Parno, Aymeric Fromherz, Chris Hawblitzel, Marina
Polubelova, Karthikeyan Bhargavan, Benjamin Beurdouche, Joonwon Choi, Antoine
Delignat-Lavaud, Cedric Fournet, Tahina Ramananandro, Aseem Rastogi, Nikhil
Swamy, Christoph Wintersteiger and Santiago Zanella-Beguelin

The HACL\* library:
- [HACL\*: A Verified Modern Cryptographic Library](http://eprint.iacr.org/2017/536)  
  Jean-Karim Zinzindohoué, Karthikeyan Bhargavan, Jonathan Protzenko, Benjamin Beurdouche
- [A Verified Extensible Library of Elliptic Curves](https://hal.inria.fr/hal-01425957)  
  Jean Karim Zinzindohoué, Evmorfia-Iro Bartzia, Karthikeyan Bhargavan
- The origins of HACL\* can be found in the [Ph.D. thesis of Jean Karim
  Zinzindohoué](https://www.theses.fr/s175861), and its design is 
  inspired by discussions at the [HACS series of workshops](https://github.com/HACS-workshop). 

The Low\* verification technology:
- [Verified Low-Level Programming Embedded in F\*](https://arxiv.org/abs/1703.00053)  
  Jonathan Protzenko, Jean-Karim Zinzindohoué, Aseem Rastogi, Tahina
  Ramananandro, Peng Wang, Santiago Zanella-Béguelin, Antoine Delignat-Lavaud,
  Cătălin Hriţcu, Karthikeyan Bhargavan, Cédric Fournet, and Nikhil Swamy

The Vale tool and verified assembly libraries:
- [Vale: Verifying High-Performance Cryptographic Assembly Code](https://project-everest.github.io/assets/vale2017.pdf)  
  Barry Bond, Chris Hawblitzel, Manos Kapritsos, K. Rustan M. Leino, Jacob R. Lorch, Bryan Parno, Ashay Rane, Srinath Setty, Laure Thompson.
  In Proceedings of the USENIX Security Symposium, 2017.
  *Distinguished Paper Award*

- [A Verified, Efficient Embedding of a Verifiable Assembly Language](https://www.microsoft.com/en-us/research/publication/a-verified-efficient-embedding-of-a-verifiable-assembly-language/)  
  Aymeric Fromherz, Nick Giannarakis, Chris Hawblitzel, Bryan Parno, Aseem Rastogi, Nikhil Swamy. In Proceedings of the Symposium on Principles of Programming Languages (POPL), 2019.

# License

All F\* source code is released under Apache 2.0.

All generated assembly, C, OCaml, Javascript, and Web Assembly code is released under MIT.

[INRIA Paris]: https://www.inria.fr/en/centre/paris
[Prosecco]: http://prosecco.inria.fr
[F\*]: https://github.com/FStarLang/FStar
[Low\*]: https://arxiv.org/abs/1703.00053
[KreMLin]: https://github.com/FStarLang/kremlin
[miTLS]: https://github.com/mitls/mitls-fstar
[NaCl API]: https://nacl.cr.yp.to
[libsodium]: https://github.com/jedisct1/libsodium
[Project Everest]: https://github.com/project-everest
[secure_api/]: https://github.com/mitls/hacl-star/tree/master/secure_api
[Vale]: https://github.com/project-everest/vale
[Everest Docker]: https://cloud.docker.com/u/projecteverest/repository/docker/projecteverest/everest
