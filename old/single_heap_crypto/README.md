# HACL* cryptographic code

## Description

This directory contains code for several cryptographic primitives.
It uses the standard FStar.ST and FStar.Heap modules to ensures memory safety.
It emulates some pointer arithmetic features via `sbuffer.fst` provided in `lib/st`.

## Structure

+ ec

   Code for Elliptic curve cryptography

+ symetric

   Code for symetric cryptography, for now:
   + Chacha20
   + Poly1305
   + AES

+ hash

   Code for hash functions
