### Proof Structure 

- `Crypto.Plain.fst` defines abstract types for variable-length secret
  bytestrings and buffers for AEAD plaintext. [Used in PRF]

- `Crypto.AEAD.BufferUtils.fst` proves framing lemmas (with very few dependencies.)

- `Crypto.AEAD.MAC_Wrapper.Invariant.fst` ?

- `Crypto.AEAD.Encoding.fst` defines binary encoding for authenticated
  materials (ciphers, additional data, and their lengths) and proves
  their injectivity.

- `Crypto.AEAD.Wrappers.PRF.fst`, `Crypto.AEAD.Wrappers.CMA.fst`, and
  `Crypto.AEAD.Wrappers.Encoding.fst` provide intermediate interfaces
  specialized for the AEAD proof.

- `Crypto.AEAD.Invariant.fst` defines our internal state and main
  invariant (between calls to AEAD).

- `Crypto.AEAD.EnxorDexor.fst` defines the two loops for
  counter-mode-based (unauthenticated) encryption and decryption.

- `Crypto.AEAD.Encrypt.Invariant.fst`,
  `Crypto.AEAD.Enxor.Invariant.fst` and
  `Crypto.AEAD.Encrypt.Ideal.Invariant.fst` prove (partial) invariant preservations through imperative calls.

- `Crypto.AEAD.Encrypt.fst` and `Crypto.AEAD.Decrypt.fst` defines the
  two main functions for authenticated encryption.

- `Crypto.AEAD.fst` finally adds key management to our main AEAD
  construction.

### Other files 

- `Crypto.AEAD.Chacha20Poly1305.fst` and `Crypto.AEAD.AES256GCM.fst`
  are not currently used.

- `Crypto.AEAD.Encrypt.Aux.fst` is dead.
