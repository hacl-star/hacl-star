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

# Warning

While HACL* is used in several products such as Mozilla Firefox or Wireguard,
we highly recommand to consult the authors before using HACL* in production systems.

# Supported Cryptographic Algorithms

The primitives and constructions supported currently are:

* Stream ciphers: Chacha20, Salsa20
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

# Licenses

All F* source code is released under Apache 2.0.

All generated C, OCaml, Javascript and Web Assembly code is released under MIT.


# Authors and Maintainers

HACL* was originially developed as part of the Ph.D. thesis of Jean Karim Zinzindohoué
in the [Prosecco](http://prosecco.inria.fr) team at [INRIA Paris](https://www.inria.fr/en/centre/paris).
It contains contributions from many researchers at INRIA and Microsoft Research, and is
being actively developed and maintained within [Project Everest].

For questions and comments, or if you want to contribute to the project, do contact the current maintainers at:
* Benjamin Beurdouche (benjamin.beurdouche@inria.fr)
* Karthikeyan Bhargavan (karthikeyan.bhargavan@inria.fr)
