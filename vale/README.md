Vale (Verified Assembly Language for Everest) <br>Cryptographic Libraries
=====================================================================

This directory contains the Vale cryptographic libraries, i.e., formally verified high-performance
cryptographic code in assembly language.  They rely
on the [Vale tool](https://github.com/project-everest/vale) to produce
code and proofs in [F\*](https://github.com/FStarLang/FStar).

The code currently targets x64, but it will be expanded to support
other hardware platforms, such as x86 and ARM.  Our toolchain
produces assembly that is suitable for Windows, Mac, and Linux,
and that is compatible with both MSVC and GCC based toolchains.

Vale is part of the [Everest project](https://project-everest.github.io), 
which aims to build and deploy a verified HTTPS stack.

# Installation

See the [INSTALL](./INSTALL.md) file for installing Vale and its dependencies.

# Code Organization

See the [CODE](./CODE.md) file for more details on the various files in this directory.

# Documentation

You can see our academic papers describing Vale:

* [Vale: Verifying High-Performance Cryptographic Assembly Code](https://project-everest.github.io/assets/vale2017.pdf)  
Barry Bond, Chris Hawblitzel, Manos Kapritsos, K. Rustan M. Leino, Jacob R. Lorch, Bryan Parno, Ashay Rane, Srinath Setty, Laure Thompson.
In Proceedings of the USENIX Security Symposium, 2017.
*Distinguished Paper Award*

* [A Verified, Efficient Embedding of a Verifiable Assembly Language](https://www.microsoft.com/en-us/research/publication/a-verified-efficient-embedding-of-a-verifiable-assembly-language/)  
Aymeric Fromherz, Nick Giannarakis, Chris Hawblitzel, Bryan Parno, Aseem Rastogi, Nikhil Swamy. In Proceedings of the Symposium on Principles of Programming Languages (POPL), 2019.

# License

Our Vale code is licensed under the Apache license in the [LICENSE](./LICENSE) file.

# Version History
- v0.2: Vale/F* code release.
- v0.1: Initial code release, containing code written by:
Andrew Baumann, Barry Bond, Andrew Ferraiuolo, Chris Hawblitzel,
Jon Howell, Manos Kapritsos, K. Rustan M. Leino, Jacob R. Lorch,
Bryan Parno, Ashay Rane, Srinath Setty, and Laure Thompson.
