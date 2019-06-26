# A brief documentation of the EverCrypt provider

This documentation is written for consumers of EverCrypt who wish to use the
APIs from C programs. This document assumes one has properly obtained a
distribution of EverCrypt, e.g. by fetching the latest Docker container (see the
[README](../README.EverCrypt.md) for further pointers).

## Building EverCrypt

Any of the `dist/` subdirectories provides a self-contained Makefile that has
been tested on Linux, OSX and Windows. It builds a static object
(libevercrypt.a) and a dynamic object (libevercrypt.{so,dll}) along with the
import library for Windows systems (libevercrypt.dll.a). On Windows, the
Makefile has been tested in a Cygwin environment equipped with the MinGW
cross-compilers. The `dist/compact-msvc` distribution works with the Microsoft
compilers, but we provide no build support (i.e. no Visual Studio project, no
NMake-compatible makefile).

## Breaking changes

See [Changes.md](Changes.md) for a list of breaking changes for each release. We
aim to be ABI-stable by version 1.0.

## EverCrypt vs. HACL\* vs. ValeCrypt

EverCrypt is a superset of HACL\* and ValeCrypt. HACL\* provides a collection of
standalone core algorithms written in C. ValeCrypt provides a collection of
standalone core routines written in assembly. Above HACL\* and ValeCrypt, EverCrypt:

- auto-detects your CPU features, and
- picks the best implementation automatically;
- offers *agile* APIs that allow you to switch to a different algorithm (e.g.
  hash, AEAD) by changing a single parameter, rather than rewriting your code
  against a new set of functions;
- offers higher-level APIs: for hashes, for instance, the incremental API allows
  feeding arbitrary chunks of data into the hash function rather than
  block-by-block.

Most clients will therefore only read the `EverCrypt_*.h` header files. For
advanced users that, say, need none of the advanced APIs or already have their
own CPU auto-detection facilities, it may be better to skip the EverCrypt
abstraction layer and use the underlying `Hacl_*.h` set of headers.

## Reading fsti files instead of C headers

Our C code is generated; as such, some information is lost in the translation
process. Instead of looking at C header files, we strongly advise prospective
users to read the original F\* interface files (`.fsti`). These have the most
up-to-date comments, as well as a wealth of information regarding preconditions,
such as length of arrays, disjointness, etc. that C clients MUST obey.

Most `.h` headers can be mapped to their original F\* interface file in
the [evercrypt](evercrypt/) directory: a function of the form `Foo_Bar_baz` will
be declared in `Foo.Bar.fsti`.

## Overview of the APIs

### Deprecated APIs

- **`EverCrypt.h`**: the types and functions declared in `EverCrypt.h` are
  currently *deprecated* (we plan to generate `__attribute__ (deprecated)`).
  - Users of AES-GCM should use `EverCrypt_AEAD.h` instead with a suitable
    algorithm parameter.
  - Users of AES-CTR (and the AES block function), of DH shares and of randomness
    should be aware that new modules (`EverCrypt.Random`, `EverCrypt.CTR`) will soon
    land to replace these deprecated functions.
  Once `EverCrypt.h` has been removed, EverCrypt will sever its dependency to
  BCrypt and/or OpenSSL.
- **`EverCrypt_Chacha20Poly1305.h`** is **deprecated**, use `EverCrypt_AEAD.h`
  instead
- **`EverCrypt_Cipher.h`** is **deprecated** and will be replaced by
  **`EverCrypt_CTR.h`**
- **`EverCrypt_Hacl.h`, `EverCrypt_Vale.h`** are deprecated and not to be used
  by clients under any circumstances

### Agile APIs

- **`EverCrypt_Hash.h`** contains two agile, multiplexing APIs.
  - Functions of the form `EverCrypt_Hash_*` expect to receive block-sized data
    except for the final call to `EverCrypt_Hash_update_last` (see fsti).
  - Functions of the form `EverCrypt_Hash_Incremental_*` can take any input
    size, at the expense of an intermediary data structure with an internal buffer
    and a length. Note that `EverCrypt_Hash_Incremental_finish` keeps the
    underlying state as-is, allowing clients to resume hashing after computing
    an intermediate hash.
- **`EverCrypt_AEAD.h`** contains the agile AEAD API.
  - Keys are expanded once then are reusable for subsequent calls to `encrypt`
    and `decrypt`.
- **`EverCrypt_HMAC.h`**, **`EverCrypt_HKDF.h`**: agile and multiplexing

### Non-agile APIs

For algorithms that are not covered by an agile API for the underlying
construction, we offer individual headers so that clients still get the benefits
of multiplexing. These may be deprecated in the future if we end up adding an
agile API (e.g. `EverCrypt_ECC.h`).

- **`EverCrypt_Poly1305.h`** contains a multiplexing implementation of Poly1305.
- **`EverCrypt_Curve25519.h`** contains a multiplexing implementation of Curve25519.
- **`EverCrypt_Ed25519.h`** contains a non-multiplexing implementation of
  Ed25519 (will be multiplexing eventually).

### Auto-configuration

Clients SHOULD call the `init` function from `EverCrypt_Autoconfig2.h`, which
will perform CPU auto-detection, then cache the results. Lacking a call to
`init`, multiplexing points will pick a slow, safe fallback for each algorithm.

Clients SHOULD NOT disable any of the CPU features and/or `wants_*` flags. These
are for internal EverCrypt test usage.

### Internal use

`EverCrypt_OpenSSL.h`, `EverCrypt_BCrypt.h`, `EverCrypt_StaticConfig.h` are for
internal use and clients should not include these headers.
