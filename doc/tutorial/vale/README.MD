Vale (Verified Assembly Language for Everest)
=============================================

Vale is a tool for constructing formally verified high-performance assembly language code,
with an emphasis on cryptographic code.
It uses existing verification frameworks,
such as [Dafny](https://github.com/Microsoft/dafny) and [F\*](https://github.com/FStarLang/FStar),
for formal verification.
It supports multiple architectures, such as x86, x64, and ARM, and multiple platforms, such as Windows, Mac, and Linux.
Additional architectures and platforms can be supported with no changes to the Vale tool.

Vale is part of the [Everest project](https://github.com/project-everest/project-everest.github.io).

# Installation

See the [INSTALL](./INSTALL.md) file for installing Vale and its dependencies.

# Code Organization

See the [CODE](./CODE.md) file for more details on the various files in the repository.

# License

Vale is licensed under the Apache license in the [LICENSE](./LICENSE) file.

We have used Vale to verify assembly language code derived from OpenSSL
(https://www.openssl.org/source/license.html).
Files containing code derived from OpenSSL contain acknowledgments of the specific OpenSSL source code.

# Version History
- v0.1:   Initial code release, containing code written by:
Andrew Baumann, Barry Bond, Andrew Ferraiuolo, Chris Hawblitzel,
Jon Howell, Manos Kapritsos, K. Rustan M. Leino, Jacob R. Lorch,
Bryan Parno, Ashay Rane, Srinath Setty, and Laure Thompson.
