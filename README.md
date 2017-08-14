HaCl-star
=========


HaCl* is a formally verified cryptographic library in [F\*]
developed as part of [Project Everest]. This specific version of the code
is in a production branch dedicated to NSS for Mozilla and RedHat.
Please consult the authors (see below) for gracious help if you intend
to use this project in a different setting.

HACL stands for High-Assurance Cryptographic Library and its design is
inspired by discussions at the HACS series of workshops.
The goal of this library is to develop *reference* implementations
for popular cryptographic primitives and to verify them for memory safety,
side-channel resistance, and (where applicable) functional correctness.

Research Paper: https://eprint.iacr.org/2017/536

* Benjamin Beurdouche <benjamin.beurdouche@inria.fr>
* Jean-Karim Zinzindohoué <jean-karim.zinzindohoue@inria.fr>
* Karthikeyan Bhargavan <karthikeyan.bhargavan@inria.fr>
* Jonathan Protzenko <protz@microsoft.com>


All code is written and verified in F\* and then compiled to C or to
OCaml for execution.

The primitives and constructions supported currently are:

* Stream ciphers: Chacha20, Salsa20, XSalsa20
* MACs: Poly1305
* Elliptic Curves: Curve25519
* Elliptic Curves Signatures: Ed25519
* Hash functions: SHA2 (256,384,512)
* MAC: HMAC
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


# Build and Installation

See [INSTALL.md](INSTALL.md).

[INSTALL.md]: https://github.com/mitls/hacl-star/INSTALL.md
