Vale (Verified Assembly Language for Everest) cryptographic libraries
=====================================================================

This directory contains the Vale cryptographic libraries, i.e., formally verified high-performance
cryptographic code in assembly language.  It relies
on the [Vale tool](https://github.com/project-everest/vale) to produce
code and proofs in [F\*](https://github.com/FStarLang/FStar).

The code currently targets x64, but it will be expanded to support
other hardware platforms, such as x86 and ARM.  Our toolchain
produces assembly for Windows, Mac, and Linux.

Vale is part of the [Everest project](https://project-everest.github.io).

# Installation

See the [INSTALL](./INSTALL.md) file for installing Vale and its dependencies.

# Code Organization

See the [CODE](./CODE.md) file for more details on the various files in this directory.

# Documentation

You can see our academic paper describing Vale:

> [Vale: Verifying High-Performance Cryptographic Assembly Code](https://project-everest.github.io/assets/vale2017.pdf)
> Barry Bond, Chris Hawblitzel, Manos Kapritsos, K. Rustan M. Leino, Jacob R. Lorch, Bryan Parno, Ashay Rane, Srinath Setty, Laure Thompson.
> In Proceedings of the USENIX Security Symposium, 2017.
> Distinguished Paper Award

# License

Our Vale code is licensed under the Apache license in the [LICENSE](./LICENSE) file.

# Version History
- v0.2: Vale/F* code release.
- v0.1: Initial code release, containing code written by:
Andrew Baumann, Barry Bond, Andrew Ferraiuolo, Chris Hawblitzel,
Jon Howell, Manos Kapritsos, K. Rustan M. Leino, Jacob R. Lorch,
Bryan Parno, Ashay Rane, Srinath Setty, and Laure Thompson.
