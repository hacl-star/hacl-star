# Secure APIs and Cryptographic Proofs for Constructions using HACL\* Primitives #

This directory contains APIs and verified code for
standardized cryptographic constructions used (in particular) in the
[miTLS] implementation of the Transport Layer Security protocol.

The security for these APIs and their underlying algorithms is
specified using *cryptographic games* between the real code and its
idealization. Both variants of the code are programmed and verified in
F\*, using precise types that capture their security properties. 
These APIs can be used in turn to build and verify more complex functionalities.

For each API, we provide a security proof, by reduction to assumptions
on the underlying algorithms. A [research paper] "Implementing and
Proving the TLS 1.3 Record Layer " details our verification method and
results. It further reduces (on paper) our code-based assumptions to
simpler common assumptions. It also gives concrete security bounds,
that is, upper bounds on the probability that an adversary that calls
our API may distinguish between its real and idealized code, and
thereby defeat its security.

We provides three constructions in separate directories:

* `uf1cma`: a one-time message-authentication functionality that
provides resistance to forgeries against chosen-message attacks.  We
use a generic Wegman-Carter-Shoup construction, parameterized by a
field, and instantiated with (verified HACL\* implementations of)
Poly1305 and GF128.  We obtain concrete probabilistic bounds (without
any cryptographic assumption besides key randomness).

* `prf`: an agile, pseudo-random block function, instantiated with
(verified HACL\* implementations of) ChaCha20, AES128, and AES256.
Our idealization is based on a standard computational PRF assumption,
with an interface specialized for the AEAD construction below
(accounting for different usages of the PRF blocks, as authentication
keys and one-time pads for encryption).

* `aead`: an authenticated encryption with additional data
functionality. We implement and verify the standardized construction
used in the Chacha-Poly and AES-GCM ciphersuites of TLS. The
type-based security proof is by reduction to the two APIs described
above.


[miTLS]: https://github.com/mitls/mitls-star
[research paper]: https://eprint.iacr.org/2016/1178.pdf 
