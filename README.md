HaCl-star
=========

HaCl* is a formally verified cryptographic library in [F\*],
developed as part of [Project Everest].

[![Build Status](https://travis-ci.org/mitls/hacl-star.svg?branch=master)](https://travis-ci.org/mitls/hacl-star)

HACL stands for High-Assurance Cryptographic Library and its design is
inspired by discussions at the HACS series of workshops.
The goal of this library is to develop *reference* implementations
for popular cryptographic primitives and to verify them for memory safety,
side-channel resistance, and (where applicable) functional correctness.

All code is written and verified in F\* and then compiled to C or to
OCaml for execution.

The primitives and constructions supported currently are:

* Stream ciphers: Chacha20, Salsa20, XSalsa20
* MACs: Poly1305
* Elliptic Curves: Curve25519
* Hash functions: SHA2 (224,256,384,512)
* NaCl API: secret_box, box

HACL* can be used in two ways. The verified primitives can be directly
used in larger verification projects.  For example, HACL* code is used
as the basis for cryptographic proofs of the TLS record layer in
[miTLS].  Alternatively, developers can use HACL* through the [NaCl API].
In particular, we implement the same C API as [libsodium] for the
Box and SecretBox primitives, so any application that runs on
libsodium can be immediately ported to use the verified code in HACL*
instead.

[F\*]: https://github.com/FStarLang/FStar
[miTLS]: https://github.com/mitls/mitls-fstar
[NaCl API]: https://nacl.cr.yp.to
[libsodium]: https://github.com/jedisct1/libsodium
[Project Everest]: https://github.com/project-everest


# Warning

This library is experimental and only at the pre-production stage.

Do not use it in production systems without consulting the authors.


# Build and Installation

See [INSTALL.md](INSTALL.md).

For convenience, C code for our verified primitives has already been extracted
and is available in [snapshots/hacl-c](snapshots/hacl-c).
To build the library, you need a modern C compiler (preferably GCC-6) and CMake.

To build a static and shared versions of this library:

```make build```


[INSTALL.md]: https://github.com/mitls/hacl-star/INSTALL.md


# Verification and Extraction

See [INSTALL.md](INSTALL.md).

To verify the F\* code, you need to install the [F\*] typechecker.
To extract F\* code to C, you need to install the [KreMLin] compiler.

[INSTALL.md]: https://github.com/mitls/hacl-star/INSTALL.md
[KreMLin]: https://github.com/FStarLang/kremlin


# Performance

HACL* primitives, when compiled to C, are as fast as state-of-the-art
C implementations. You can see the numbers for your platform and C compiler
by running `make test` in the snapshot folder.

To compare its performance with the C reference code in libsodium and openssl,
download and compile [libsodium] with the `--disable-asm` flag
and [openssl] with the `-no-asm` flag.

While the raw performance is quite good, HaCl is not as fast as hand-written
assembly code.  Linking HACL* to verified assembly language components
is a long-term goal.


[openssl]: https://github.com/openssl/openssl
[libsodium]: https://github.com/jedisct1/libsodium


# Experimental features

The [code/experimental](code/experimental) directory includes other (partially verified) cryptographic primitives that will become part of the library in the near future:
* Elliptic Curves: NIST P-256, Curve448
* Encryption: AES-128, AES-256
* MACs: HMAC, GCM
* Key Derivation: HKDF

To build a static and shared versions of the experimental library:

```make build-experimental```

We are also working on a JavaScript backend to F* that would enable us to extract HACL* as a JavaScript library.


# Maintainers

* Jean-Karim Zinzindohoué
* Karthikeyan Bhargavan
* Benjamin Beurdouche
