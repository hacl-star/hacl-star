# EverCrypt: A Verified Crypto Library Engineered for Agile, Multi-Platform Performance

EverCrypt is a formally verified modern cryptographic library
that provides cross-platform support as well as platform-specific optimizations
that are automatically enabled if processor support is detected (*multiplexing*).
Furthermore, EverCrypt offers an (*agile*) API that makes it simple to
switch between algorithms (e.g., from SHA2 to SHA3) if one of the algorithms is broken.

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
  characterized by a simple mathematical functions derived directly
  from the official cryptographic standards (e.g., from NIST or the IETF).

* Side-channel resistance: Observations about EverCrypt's low-level
  behavior (specifically, the time it takes to execute or the memory addresses that it accesses)
  are independent of the secrets manipulated by the library.
  Hence, an adversary monitoring these "side-channels" learns
  nothing about the secrets.

* Cryptographic security: Based on standard cryptographic assumptions (e.g.,
  factoring is hard), except for negligible probability, EverCrypt algorithms are
  indistinguishable from ideal cryptographic functionalities; i.e., the
  mathematical definitions that cryptographers use to capture the notion of
  secrecy, integrity, or secure encryption.  Note that these guarantees
  currently only apply to ***SUBSET HERE***; extending these guarantees
  to the entire library is on-going work.

All of these guarantees *do not* prevent EverCrypt from achieving good performance!
EverCrypt meets or beats the performance of most existing cryptographic implementations in C,
and for certain targeted platforms meets or beats the performance of state-of-the-art
libraries that rely on hand-tuned assembly code.

Portions of EverCrypt are being used in [Firefox][Hacl-Firefox], the Windows kernel,
the [Tezos blockchain][Hacl-Tezos], and the [Wireguard VPN][Hacl-Wireguard].

This repository brings together several components of [Project Everest],
which aims to build and deploy a verified HTTPS stack.

# Algorithms Supported by EverCrypt

* Block ciphers: AES (128, 256)\*, AES-CBC\*, AES-CTR\*
* Stream ciphers: Chacha20, Salsa20
* MACs: Poly1305\*, HMAC+
* Key Derivation+: HKDF
* Elliptic curves: Curve25519\*
* Elliptic curves signatures: Ed25519
* Hash functions+: MD5, SHA1, SHA2 (224, 256\*, 384, 512), SHA3, Blake2
* NaCl API: secret_box, box, sign
* AEAD: IETF Chacha20Poly1305, AES-GCM\*

Algorithms with stars include optimized implementations targeting specific platforms
(e.g., x64 with AES-NI, BMI2, ADX, or SHA).
Algorithms with a plus are agile and multiplexed.

# Building or Integrating EverCrypt

Building EverCrypt from scratch is fairly involved and requires several tools.
Hence the simplest approach is to use the [Everest Docker] project, then get
the latest `everest` image. The EverCrypt code will be in
`$HOME/everest/hacl-star/code/dist/*`; in order to integrate it in your project,
you will also need the `minimal` variant of `kremlib`, found in
`$HOME/everest/kremlin/kremlib/dist/minimal`.

The `.c` files in `code/dist`, along with their headers, form the EverCrypt C API.
The EverCrypt API subsumes the original [NaCl API] as offered by [libsodium],
meaning that applications that rely on the [NaCl] subset of [libsodium] can be
straightforwardly recompiled against EverCrypt.

Note that `code/dist` contains several flavors of generated C code, depending on
whether you need to support MSVC or not, C89 or not, etc. It's always easy to
add one more flavor of generated C code. Ask us.

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

This repository also contains two verified applications built on top of EverCrypt.

## Merkle Trees

We offer a Merkle Tree library, implementing fast cryptographic hashes for
blockchains, in [secure_api/merkle_tree](secure_api/merkle_tree).

The generated C code is also built as part of the container and can be found in
`$HOME/everest/hacl-star/secure_api/merkle_tree/dist`.

## TLS record layer

We offer an agile cryptographic model which is the basis for proofs of
cryptographic security of the TLS 1.3 record layer, in
[secure_api](secure_api/).  For more details, see:

[Implementing and Proving the TLS 1.3 Record Layer](https://eprint.iacr.org/2016/1178)
Karthikeyan Bhargavan, Antoine Delignat-Lavaud, Cedric Fournet, Markulf
Kohlweiss, Jianyang Pan, Jonathan Protzenko, Aseem Rastogi, Nikhil Swamy,
Santiago Zanella-Beguelin, Jean-Karim Zinzindohoue

# Research

The HACL\* library:
- [HACL\*: A Verified Modern Cryptographic Library](http://eprint.iacr.org/2017/536)
  Jean-Karim Zinzindohoué, Karthikeyan Bhargavan, Jonathan Protzenko, Benjamin Beurdouche
- [A verified extensible library of elliptic curves](https://hal.inria.fr/hal-01425957)
  Jean Karim Zinzindohoué, Evmorfia-Iro Bartzia, Karthikeyan Bhargavan

The Low\* verification technology:
- [Verified Low-Level Programming Embedded in F\*](https://arxiv.org/abs/1703.00053)
  Jonathan Protzenko, Jean-Karim Zinzindohoué, Aseem Rastogi, Tahina
  Ramananandro, Peng Wang, Santiago Zanella-Béguelin, Antoine Delignat-Lavaud,
  Cătălin Hriţcu, Karthikeyan Bhargavan, Cédric Fournet, and Nikhil Swamy

# License

All F\* source code is released under Apache 2.0.

All generated assembly, C, OCaml, Javascript, and Web Assembly code is released under MIT.

[INRIA Paris](https://www.inria.fr/en/centre/paris)
[Prosecco](http://prosecco.inria.fr)
[F\*]: https://github.com/FStarLang/FStar
[KreMLin]: https://github.com/FStarLang/kremlin
[miTLS]: https://github.com/mitls/mitls-fstar
[NaCl API]: https://nacl.cr.yp.to
[libsodium]: https://github.com/jedisct1/libsodium
[Project Everest]: https://github.com/project-everest
[secure_api/]: https://github.com/mitls/hacl-star/tree/master/secure_api
[Vale]: https://github.com/project-everest/vale
[Everest Docker]: https://cloud.docker.com/u/projecteverest/repository/docker/projecteverest/everest
