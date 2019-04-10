# High Performance Verified Cryptographic Code

This repository contains code from several related projects developed as part of
[Project Everest](https://project-everest.github.io/), which aims to build and
deploy a verified HTTPS stack.

We are actively developing and integrating our code on the
[fstar-master](https://github.com/project-everest/hacl-star/tree/fstar-master/)
branch, which tracks F\*'s `master` branch. See
[releases](https://github.com/project-everest/hacl-star/releases) for a preview
of our C and assembly code, including EverCrypt 0.1 (currently in **alpha**).

## HACL\*

[HACL\*](README.HACL.md), the High-Assurance Cryptographic Library, is a
formally verified cryptographic library in [F\*](https://www.fstar-lang.org).
The goal of this library is to develop highly efficient, pure C implementations
for popular cryptographic primitives and to verify them for memory safety,
functional correctness, and secret independence.

## Vale-Crypto

[Vale-Crypto](README.Vale.md) provides formally verified high-performance
cryptographic code in assembly language. It relies on the 
[Vale tool](https://github.com/project-everest/vale) to produce
code and proofs in [F\*](https://github.com/FStarLang/FStar). Vale supports
multiple platforms and proves that its implementations are memory safe,
functionally correct, and that timing and memory accesses are secret
independent.

## EverCrypt

[EverCrypt](README.EverCrypt.md) is a high-performance, cross-platform, formally
verified modern cryptographic provider. EverCrypt packages implementations from
HACL\* and Vale-Crypto, and automatically picks the fastest one available,
depending on processor support and the target execution environment
(*multiplexing*). Furthermore, EverCrypt offers an (*agile*) API that makes it
simple to switch between algorithms (e.g., from SHA2 to SHA3).
