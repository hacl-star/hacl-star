### Verified implementation of crypto_box

The files in this folder are an attempt at providing an F\* implementation of NaCL's crypto_box. We might
modify the original construction by using chacha20poly1305 instead of the original xsalsa20poly1305 as symmetric encryption algorithm.
This is due to the fact that there is presently a secure_api for aead based on that algorithm.

We attempt to provide a secure API as described in the partent directory.
Currently, everything is still work in progress and freshly ported over from FStar/examples/crypto/cryptobox.

TODO:
- implement wrapper so we can use aead
- use aead and remove any dependency on corecrypto
- construct better log_invariants so we can verify them in a reasonable time
- clean up the api and follow naming conventions from the original nacl code and/or other secure_api examples
  - split up functions accordingly?
- provide spec