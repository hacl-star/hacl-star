# HACL* cryptographic code

## Description

This directory contains verified F* code for several cryptographic primitives.
Currently unverified and partially-verified primitives are kept in the `experimental` directory.
They will be moved out of this directory to a subdirectory of `code` once their verification is complete.

## Structure

+ `salsa-family`: Code for Salsa20, HSalsa20, XSalsa20, and ChaCha20

+ `bignum`: Code for generic prime-field arithmetic

+ `poly1305`: Code for Poly1305 MAC (relies on bignum)

+ `curve25519`: Code for Curve25519 (relies on bignum)

+ `ed25519`: Code for Ed25519 signatures (relies on bignum)

+ `hash`: Code for SHA2, in particular versions 256, 384 and 512

+ `hmac`: Code for HMAC Message Authentication Code for SHA2-{256,384,512}


## Verification

Run `make verify` to run start the library verification.
All primitives are verified for memory safety, secret independence (a side-channel mitigation),
and functional correctness against the high-level specifications in `hacl-star/specs`.

## Extraction to C and execution

Run `make extract-c` to compile the F* code into C code for those primitives
and run it on a single test vector. If you do not have F* or KreMLin installed,
and you want to see the currently generated C code, look at the snapshot
checked into the `hacl-star/snapshots/hacl-c` directory.
