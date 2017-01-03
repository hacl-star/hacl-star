# HACL* cryptographic code

## Description

This directory contains code for several cryptographic primitives.
It uses a custom statful effect from the FStar.HyperStack and FStar.HST modules to ensures memory safety and emulate a C* stack with stack-allocation only.
It emulates some pointer arithmetic features via `FStar.Buffer.fst` provided in `lib/hst`.

## Structure

+ ec

   Code for Elliptic curve cryptography, for now:
   + Curve25519

+ symetric

   Code for symetric cryptography, for now:
   + Chacha20
   + Poly1305
   + AES,GCM, AEAD-AES256GCM verify

+ hash

   Code for hash functions

## Verification

Run `make` to run start the library verification.

Currently verified primitives:
+ Chacha20 (memory safety)
+ Poly1305 (memory safety)
+ AEAD-AES256GCM (memory safety)
+ Curve25519 (memory safety)
