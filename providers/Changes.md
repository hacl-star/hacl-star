### June 25th, 2019
- The state in EverCrypt.AEAD now contains scratch space to use in encrypt/decrypt. It is therefore modified at each encryption/decryption.

### June 20th, 2019
- EverCrypt now supports arbitrary length IV for AES-GCM. A new parameter `iv_len` needs to be passed during encryption and decryption. In C, a new error InvalidIVLength is returned if the length of the iv does not satisfy an algorithm's requirements.
