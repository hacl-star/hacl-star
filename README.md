# A High-Assurance Cryptographic Library

This repository contains verified code for a library of modern
cryptographic algorithms, including Curve25519, Ed25519, AES-GCM,
Chacha20, Poly1305, SHA-2, SHA-3, HMAC, and HKDF. This set of algorithms
is enough to support the full NaCl API and several TLS 1.3 ciphersuites.
The code for all of these algorithms is formally verified using the
[F\*](https://fstarlang.github.io/) verification framework for memory
safety, functional correctness, and secret independence (resistance to
some types of timing side-channels).

**Documentation**: More detailed documentation on the library and our verification method
can be found at [hacl-star.github.io](https://hacl-star.github.io).

The code in this repository is divided into three closely-related sub-projects,
all developed as part of [Project Everest](https://project-everest.github.io/).

## HACL\*

[HACL\*](code/) is a formally verified library
of modern cryptographic algorithms written in a subset of
[F\*](https://fstarlang.github.io) called Low\* and compiled to C
using a compiler called
[KreMLin](https://github.com/FStarLang/kremlin). The Low\* source code
for each primitive is verified for memory safety, functional
correctness, and secret independence. The compiler generates
efficient, readable, standalone C code for each algorithm that
can be easily integrated into any C project.  We include the current C code for various HACL\*
algorithms in the [dist](dist/) directory. HACL\* can also be compiled to WebAssembly.

## ValeCrypt

[ValeCrypt](vale/) provides formally verified high-performance
cryptographic code for selected primitives in assembly language. It relies on the
[Vale tool](https://github.com/project-everest/vale) to produce
code and proofs in [F\*](https://github.com/FStarLang/FStar). Vale supports
multiple platforms and proves that its implementations are memory safe,
functionally correct, and that timing and memory accesses are secret
independent.

## EverCrypt

[EverCrypt](providers/evercrypt/) is a high-performance, cross-platform, formally
verified modern cryptographic provider that packages implementations from
HACL\* and ValeCrypt, and automatically picks the fastest one available,
depending on processor support and the target execution environment
(*multiplexing*). Furthermore, EverCrypt offers an (*agile*) API that makes it
simple to switch between algorithms (e.g., from SHA2 to SHA3).

## Status

*Warning*: This is a research project. Although some of our code is currently used in popular products like Mozilla Firefox and Wireguard,
we highly recommend that users consult with the HACL\* maintainers before using this code in production systems.

We are actively developing and integrating our code on the
[master](https://github.com/project-everest/hacl-star/tree/master/)
branch, which tracks F\*'s `master` branch. Ongoing developments on new
cryptographic primitives happen in the [dev](https://github.com/project-everest/hacl-star/tree/dev/)
branch, which runs a little ahead of master. You can find a current snapshot
of our C and assembly code in the [dist](dist/) directory; stable releases of the full library
can be found in the [releases](https://github.com/project-everest/hacl-star/releases) page.

## License

All the code in this repository is released under an Apache 2.0 license.
The generated C code from HACL\* is also released under an MIT license.
Contact the maintainers if you have other licensing requirements.

## Contact or Contribute

This repository contains contributions from many students and researchers at INRIA, Microsoft Research, and Carnegie Mellon University,
and it is under active development. The primary authors of each verified algorithm are noted in the corresponding AUTHORS.md file.
For questions and comments, or if you want to contribute to the project, contact the current maintainers at hacl-star-maintainers@lists.gforge.inria.fr.

