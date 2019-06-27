## EverCrypt v0.1 alpha 2

### June 25th, 2019

- **Breaking change** for F\* (`EverCrypt.AEAD.fst`) clients.  
  The state in EverCrypt.AEAD now contains scratch space to use in
  encrypt/decrypt. It is therefore modified at each encryption/decryption.
  (Aymeric Fromherz)

### June 20th, 2019

- **Breaking change** for C (`EverCrypt_AEAD.h`) and F\* (`EverCrypt.AEAD.fst`) clients.  
  EverCrypt now supports arbitrary length IVs for AES-GCM. A new
  parameter `iv_len` needs to be passed during encryption and decryption. In C, a
  new error InvalidIVLength is returned if the length of the iv does not satisfy
  an algorithm's requirements. (Aymeric Fromherz)

### Before then

- **Breaking change** for C (`EverCrypt_Hash.h`) and F\*
  (`EverCrypt.Hash.Incremental.fst`) clients.  
  The API now takes erased algorithm parameters; the style is now in line with
  other modules, relying on abstract states and framing lemmas (now with
  patterns). (Jonathan Protzenko)

- **New feature**: WASM implementation, found in dist/wasm. There are only
  tests, no proper JavaScript wrappers yet. (Jonathan Protzenko)

- **New feature**: fully-verified AVX and AVX2 implementations of Poly1305
  (Marina Polubelova, Karthikeyan Bhargavan)

- **New feature**: fully-verified ASM implementation of SHA2-256 using the
  SHA-EXT dedicated Intel instructions (Chris Hawblitzel, Bryan Parno)
