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

## Extraction to C and execution

Run `make extract` to extract C code for all primitives.
Run `make test` to run some benchmarks
Run `make speed` to run speed tests


