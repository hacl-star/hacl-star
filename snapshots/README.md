# HACL* SNAPSHOTS

This directory contains several code snapshots of C code extracted from HACL*.

These snapshots can be removed and regenerated from the top-level makefile
if you have a correct installation of F*, Kremlin and Z3 using
`make extract-new` from within the root directory.


## Directory structure

This directory contains:

- `hacl-c`

  Reference snapshot code for HACL*. Includes the following primitives:
  - Symetric ciphers: ChaCha20, Salsa20
  - MAC: Poly1305
  - Hash: SHA256, SHA512
  - Signature: Ed25519
  - ECDH: Curve25519
  - Authenticated Encyption: SecretBox, Box, AEAD ChaCha20Poly1305 (IETF compliant)

  NB: the primitives have been selectively picked from either `snapshot-gcc`
  or `snapshot-gcc-unrolled` to provide best performance, see below.

- `snapshot-gcc`

  HACL* snapshot extracted for mainstream C compilers. Same primitives as listed above.

- `snapshot-gcc-unrolled`

  HACL* snapshot extracted for mainstream C compilers. Same primitives as listed above.
  Loops have been unrolled up to 5 iterations.

- `snapshot-ccomp`

  HACL* snapshot extracted for the [CompCert C compiler](www.http://compcert.inria.fr/).
  Same primitives as listed above. Loops have been unrolled up to 10 iterations.

- `hacl-c-experimental`

  Experimental (unverified) HACL* code, useful to third party application,
  to be verified and ported to the main `hacl-c` snapshot.

- `ecc-star`

  Legacy code snapshot for [A Verified Extensible Library of Elliptic Curves](http://ieeexplore.ieee.org/document/7536383/).
