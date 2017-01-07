# HACL* cryptographic code

## Description

This directory contains F* code for several cryptographic primitives.


## Structure

+ salsa-family

   Code for Salsa20, HSalsa20, XSalsa20, and ChaCha20

+ bignum

   Code for generic prime-field arithmetic 

+ poly1305

   Code for Poly1305 MAC (relies on bignum)

+ curve25519

   Code for Curve25519 (relies on bignum)

## Verification

Run `make verify` to run start the library verification.

Currently verified primitives:
+ Salsa20, HSalsa20, XSalsa20, Chacha20 (memory safety, side channel resistance)
+ Poly1305 (memory safety, overflow safety, functional correctness, side channel resistance)
+ Curve25519 (memory safety, overflow safety, functional correctness, side channel resistance)

Currently unverified and partially-verified primitives are kept in the `experimental` directory.
They will to this directory once their verification is complete.

## Extraction to C and execution

Run `make extract-c` in each directory to extract C code for the primitive and run it on a single test vector.
If you do not have F* or KreMLin installed, you can see the extracted code checked into the `extracted/c`
directory. 

