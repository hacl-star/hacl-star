List of supported algorithms
============================

This table provides an overview of all the algorithms we currently support. This
only lists algorithms for which verification is complete. Please refer to
documentation for each individual API for the full details.

===================  ========================  ==========================  ===========
Algorithm            Portable C                Intel ASM                   Agile API
                     (HACL\*)                  (Vale)                      (EverCrypt)
===================  ========================  ==========================  ===========
**AEAD**
AES-GCM                                        ✔︎ (AES-NI + CLMUL)          ✔︎
Chacha20-Poly1305    ✔︎ (+ AVX,AVX2)                                        ✔︎

**ECDH**
Curve25519           ✔︎                         ✔︎ (BMI2 + ADX)
P-256                ✔︎

**Signatures**
Ed25519              ✔︎
P-256                ✔︎

**Hashes**
MD5                  ✔︎                                                     ✔︎
SHA1                 ✔︎                                                     ✔︎
SHA2-224,256         ✔︎                         ✔︎ (SHAEXT)                 ✔︎
SHA2-384,512         ✔︎                                                     ✔︎
SHA3                 ✔︎
Blake2               ✔︎ (+ AVX,AVX2)

**Key Derivation**
HKDF                 ✔︎                         ✔︎ (see notes below)        ✔︎

**Ciphers**
Chacha20             ✔︎ (+ AVX,AVX2)
AES-128,256                                    ✔︎ (AES-NI + CLMUL)

**MACS**
HMAC                 ✔︎                         ✔︎ (see notes below)         ✔︎
Poly1305             ✔︎ (+ AVX,AVX2)            ✔︎ (X64)
===================  ========================  ==========================  ===========

Points of interest:

- Some C implemenations also have verified vectorized versions optimized for
  Intel AVX and AVX2 using compiler intrinsics (there is no inline assembly)
- MD5 and SHA1 are provided for legacy purposes and backwards-compatibility
  (e.g. TLS applications); no particular effort has been made to make them
  efficient
- HMAC/HKDF only use ASM implementations if the underlying hash algorithm has
  one
- P-256 and Blake2 are available on a development branch
