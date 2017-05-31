# HACL* SNAPSHOTS

This directory contains several code snapshots related to or extracted from HACL*.

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

  NB: the primitives have been selectively picked from either `snapshot-gcc` or `snapshot-gcc-unrolled` to provide best performance, see below.
- `snapshot-gcc`

  HACL* snapshot extracted for mainstream C compilers. Same primitives as listed above. Can be re-extracted using a working HACL* setup and the invocation `make -C ../test/ snapshot-gcc`.
- `snapshot-gcc-unrolled`

  HACL* snapshot extracted for mainstream C compilers. Same primitives as listed above. Loops have been unrolled up to 5 iterations. Can be re-extracted using a working HACL* setup and the invocation `make -C ../test/ snapshot-gcc-unrolled`.
- `snapshot-ccomp`

  HACL* snapshot extracted for the [CompCert C compiler](www.http://compcert.inria.fr/). Same primitives as listed above. Loops have been unrolled up to 10 iterations. Can be re-extracted using a working HACL* setup and the invocation `make -C ../test/ snapshot-ccomp`.

- `hacl-c-experimental`

  Experimental (unverified) HACL* code, useful to third party application, to be verified and ported to the main `hacl-c` snapshot.

- `ecc-star`

  Legacy code snapshot for [A Verified Extensible Library of Elliptic Curves](http://ieeexplore.ieee.org/document/7536383/).

## Building libhacl.so

HACL* can be compiled to a dynamic library which third party applications can link against (e.g. see [PneuTube](../apps/pneutube)).

In this directory, run:
```
make libhacl
```

## Testing and performance

HACL* tests and benchmarks rely on a working installation
of [LibSodium](https://download.libsodium.org/doc/)
and [OpenSSL](https://www.openssl.org/). Those two libraries are
provided via git submodule in the [dependencies](../dependencies)
directory and can be compiled and run from there.  Alternatively the
`OPENSSL_HOME` and `LIBSODIUM_HOME` can be set to the custom
installation directories.

For the `hacl-c` reference code, either run `make test` for tests only
or `make perf` to run tests and performance comparison. If necessary
the `CC` and `CCOPTS` variables can be used to specify specific
compilers and options.

Alternatives for the other snapshots are `make test-gcc`, `make test-gcc-unrolled`, `make test-ccomp`, `make perf-gcc`, `make perf-gcc-unrolled`, `make perf-ccomp`.

The *perf* targets will generate benchmark result files in readable format:

- `benchmark-cc.txt` for `hacl-c`
- `benchmark-gcc.txt` for `snapshot-gcc`
- `benchmark-gcc-unrolled.txt` for `snapshot-gcc-unrolled`
- `benchmark-ccomp.txt` for `snapshot-ccomp`
