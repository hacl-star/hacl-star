HACL*
=====

HACL* is a formally verified cryptographic library in [F\*],
developed by the [Prosecco](http://prosecco.inria.fr) team at 
[INRIA Paris](https://www.inria.fr/en/centre/paris) in collaboration
with Microsoft Research, as part of [Project Everest].

HACL stands for High-Assurance Cryptographic Library and its design is
inspired by discussions at the [HACS series of workshops](https://github.com/HACS-workshop).
The goal of this library is to develop verified C reference implementations
for popular cryptographic primitives and to verify them for memory safety,
functional correctness, and secret independence.

More details about the HACL* library and its design can be found in our ACM CCS 2017 research paper:    
https://eprint.iacr.org/2017/536

All our code is written and verified in [F\*] and then compiled to C via
the [KreMLin tool](https://github.com/FStarLang/kremlin/). Details on the verification and compilation
toolchain and their formal guarantees can be found in the ICFP 2017 paper:    
https://arxiv.org/abs/1703.00053

# Supported Cryptographic Algorithms

The primitives and constructions supported currently are:

* Stream ciphers: Chacha20, Salsa20, XSalsa20
* MACs: Poly1305, HMAC
* Elliptic Curves: Curve25519
* Elliptic Curves Signatures: Ed25519
* Hash functions: SHA2 (256,384,512)
* NaCl API: secret_box, box, sign
* TLS API: IETF Chacha20Poly1305 AEAD

Developers can use HACL* through the [NaCl API].
In particular, we implement the same C API as [libsodium] for the
NaCl constructions, so any application that relies on
libsodium only for these constructions can be immediately ported to use the verified code in HACL*
instead. (Warning: libsodium also implements other algorithms not in NaCl
that are not implemented by HACL*)

The verified primitives can also be used to support larger F* verification projects.  
For example, HACL* code is used through the agile cryptographic model developed in
[secure_api/] as the basis for cryptographic proofs of the TLS record layer in [miTLS]. 
A detailed description of the code in [secure_api/] and its formal security guarantees 
appears in the IEEE S&P 2017 paper: https://eprint.iacr.org/2016/1178.pdf

[F\*]: https://github.com/FStarLang/FStar
[KreMLin]: https://github.com/FStarLang/kremlin
[miTLS]: https://github.com/mitls/mitls-fstar
[NaCl API]: https://nacl.cr.yp.to
[libsodium]: https://github.com/jedisct1/libsodium
[Project Everest]: https://github.com/project-everest
[secure_api/]: https://github.com/mitls/hacl-star/tree/master/secure_api

# Warning

This library is at the pre-production stage.
Please consult the authors before using it in production systems.


# Licenses

All F* source code is released under Apache 2.0

All generated C code is released under MIT


# Installation

See [INSTALL.md](INSTALL.md) for prerequisites.

For convenience, C code for our verified primitives has already been extracted
and is available in [snapshots/hacl-c](snapshots/hacl-c).
To build the library, you need a modern C compiler (preferably GCC-7).

[INSTALL.md]: https://github.com/mitls/hacl-star/INSTALL.md


# Verifying and Building HACL*

Type `make` to get more information:
```
HACL* Makefile:
If you want to run and test the C library:
- 'make build' will generate a shared library from the hacl-c snapshot (no verification)
- 'make unit-tests' will run tests on the library built rom the hacl-c snapshot (no verification)
- 'make clean-build' will clean 'build' artifacts

If you want to verify the F* code and regenerate the C library:
- 'make prepare' will try to install F* and Kremlin (still has some prerequisites)
- 'make verify' will run F* verification on all specs, code and secure-api directories
- 'make extract' will generate all the C code into a snapshot and test it (no verification)
- 'make test-all' will generate and test everything (no verification)
- 'make world' will run everything (except make prepare)
- 'make clean' will remove all artifacts created by other targets
```

Verification and C code generation requires [F\*] and [KreMLin].
Benchmarking performance in `test-all` requires [openssl] and [libsodium].
An additional CMake build is available and can be run with `make build-cmake`.


# Performance

To measure see the performance of HACL* primitives on your platform and C compiler,
run the targets from `test/Makefile` if you have the dependencies installed. (experimental)
To compare its performance with the C reference code (not the assembly versions) in [libsodium] and [openssl],
download and compile [libsodium] with the `--disable-asm` flag and [openssl] with the `-no-asm` flag.

While HACL* is typically as fast as hand-written C code, it is typically 1.1-5.7x slower than
assembly code in our experiments. In the future, we hope to close this gap by using verified assembly implementations 
like [Vale](https://github.com/project-everest/vale) for some primitives.

[openssl]: https://github.com/openssl/openssl
[libsodium]: https://github.com/jedisct1/libsodium


# Experimental features

The [code/experimental](code/experimental) directory includes other (partially verified) cryptographic primitives that will become part of the library in the near future:
* Encryption: AES-128, AES-256
* MACs: GCM
* Key Derivation: HKDF
* Signatures: RSA-PSS

We are also working on a JavaScript backend for F* that would enable us to extract HACL* as a JavaScript library.


# Authors and Maintainers

HACL* was originially developed as part of the Ph.D. thesis of Jean Karim Zinzindohoué
in the [Prosecco](http://prosecco.inria.fr) team at [INRIA Paris](https://www.inria.fr/en/centre/paris).
It contains contributions from many researchers at INRIA and Microsoft Research, and is
being actively developed and maintained within [Project Everest].

For questions and comments, or if you want to contribute to the project, do contact the current maintainers at:
* Benjamin Beurdouche (benjamin.beurdouche@inria.fr)
* Karthikeyan Bhargavan (karthikeyan.bhargavan@inria.fr)

