List of supported algorithms
============================

This table provides an overview of all the algorithms we currently support. This
only lists algorithms for which verification is complete. Please refer to
documentation for each individual API for the full details.

 ===================  ========================  ==========================  =========
 Algorithm            C version                 ASM version                 Agile API
 ===================  ========================  ==========================  =========
 **AEAD**
 AES-GCM                                        ✔︎ (AES-NI + PCLMULQDQ)      ✔︎
 ChachaPoly           ✔︎ (+ AVX + AVX2)                                      ✔︎

 **Hashes**
 MD5                  ✔︎                                                     ✔︎
 SHA1                 ✔︎                                                     ✔︎
 SHA2-224,256         ✔︎                         ✔︎ (SHAEXT)                  ✔︎
 SHA2-384,512         ✔︎                                                     ✔︎
 SHA3                 ✔︎
 Blake2               ✔︎

 **MACS**
 HMAC                 ✔︎                         ✔︎ (see notes below)         ✔︎
 Poly1305             ✔︎ (+ AVX + AVX2)          ✔︎ (X64)

 **Key Derivation**
 HKDF                 ✔︎                         ✔︎ (see notes below)         ✔︎

 **ECC**
 Curve25519           ✔︎                         ✔︎ (BMI2 + ADX)
 Ed25519              ✔︎

 **Ciphers**
 Chacha20             ✔︎ (+ AVX + AVX2)
 AES128, 256                                    ✔︎ (AES NI + PCLMULQDQ)
 AES CTR                                        ✔︎ (AES NI + PCLMULQDQ)
 ===================  ========================  ==========================  =========

Points of interest:

- AVX and AVX2 versions of C algorithms are achieved through the use of C
  compiler intrinsics; there is no inline ASM
- MD5 and SHA1 are provided for legacy purposes and backwards-compatibility
  (e.g. TLS applications); no particular effort has been made to make them
  efficient
- HMAC/HKDF only use ASM implementations if the underlying hash algorithm has
  one
