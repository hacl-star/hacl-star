Cryptographic Proofs for constructions used in HACL*
====================================================

This directory contains proofs of security carried out by the [miTLS] team
for the cryptographic constructions used in the Transport Layer Security (TLS)
protocol. Full details of the proof are available in a [companion paper]. 
We include here only the part of the proof that relies on F* typechecking.

We describe three constructions in three subdirectories:
* UF1CMA: A one-time authentication functionality, built using the Poly1305 and GCM primitives implemented and verified in HACL.
* PRF: A pseudo-random function functionality, built using the ChaCha20 and AES primitives implemented in HACL.
* AEAD: An authentication encryption with additional data functionality, built using ChaCha-Poly and AES-GCM

[miTLS]: https://github.com/mitls/mitls-star




