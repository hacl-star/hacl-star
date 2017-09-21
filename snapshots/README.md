# HACL* SNAPSHOTS

This directory contains several code snapshots of C code extracted from HACL*.

These snapshots can be removed and regenerated from the top-level makefile using
`make extract-new` (assuming you have correctly installed F* and KreMLin).


## Directory structure

This directory contains:

- `hacl-c`

  Reference snapshot code for HACL*. Includes the following primitives:
  - Symmetric ciphers: ChaCha20, Salsa20
  - MAC: Poly1305
  - Hash: SHA-256, SHA-384, SHA-512
  - Signature: Ed25519
  - ECDH: Curve25519
  - NaCl API: SecretBox, Box, Sign
  - TLS API: IETF ChaCha20Poly1305 AEAD

  The code in hacl-c has been selectively picked from the make targets `snapshot-gcc`
  or `snapshot-gcc-unrolled` to provide best performance.
  
  To build the library, execute `make libhacl.co` or `make libhacl32.so` (on 32-bit systems).
  To test the library, execute `make unit-tests` or `make unit-tests32`, which
  runs the tests in `../test/test-files/unit-tests.c`.

- `hacl-c-compcert`

  HACL* snapshot extracted for the [CompCert C compiler](www.http://compcert.inria.fr/).
  Same primitives as listed above. Loops have been unrolled up to 10 iterations.

- `hacl-c-experimental`

  Experimental (unverified) HACL* code, to be verified and ported to the main `hacl-c` snapshot.

- `kremlib`

  A cached version of the KreMLin C libraries, including platform-specific endianness libraries, 
  and a compiled C version of the F* verified UInt128 library. Note that except for FStar.h other files
  are unverified hence are trusted code.

- `ecc-star`

  Legacy OCaml code for [A Verified Extensible Library of Elliptic Curves](http://ieeexplore.ieee.org/document/7536383/).
