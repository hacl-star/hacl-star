# HACL* cryptographic code

## Description

This directory contains code for several cryptographic primitives.
It uses a custom statful effect from the FStar.HyperStack and FStar.HST modules to ensures memory safety and emulate a C* stack with stack-allocation only.
It emulates some pointer arithmetic features via `FStar.Buffer.fst` provided in `lib/hst`.

## Structure

+ ec

   Code for Elliptic curve cryptography

+ symetric

   Code for symetric cryptography, for now:
   + Chacha20
   + Poly1305

+ hash

   Code for hash functions
