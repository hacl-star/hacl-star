### Verified implementation of crypto_box

The files in this folder are an attempt at providing an F\* implementation of NaCL's crypto_box. We might
modify the original construction by using chacha20poly1305 instead of the original xsalsa20poly1305 as symmetric encryption algorithm.
This is due to the fact that there is presently a secure_api for aead based on that algorithm.

We attempt to provide a secure API as described in the partent directory.
Currently, everything is still work in progress and freshly ported over from FStar/examples/crypto/cryptobox.

### Module architecture
```
  +---------------------------+                  +---------------------------+
  |                           |                  |                           |
  | Box.PKAE                  |                  | Box.PlainPKAE             |
  |                           |                  |                           |
  | * Top level module        |                  | * Provides functions to   |
  | * Provides access to      |                  |   manipulate plaintext    |
  |   crypto_box and          |<-----------------+ * Implements strict type  +---------------------+
  |   crypto_box_open         |                  |   restrictions on honest  |                     |
  | * Receives Plaintext type |                  |   plaintexts              |                     |
  |   and functionality from  |<------+          |                           |                     |
  |   Box.PlainPKAE           |       |          |                           |                     |
  |                           |       |          |                           |                     |
  +------------+--------------+       |          +---------------------------+                     |
               ^                      |                                                            |
               |                      |                                                            |
               |                      |								   v
  +------------+--------------+       |          +---------------------------+        +---------------------------+
  |                           |       |          |                           |        |                           |
  | Box.DH                    |       |          | Box.AE                    |        | Box.PlainAE               |
  |                           |       |          |                           |        |                           |
  | * Provides functions to   |       |          | * Provides functions for  |        | * Provides a plaintext    |
  |   create a symmetric key  |       |          |   symmetric encryption    |        |   type and functions to   |
  |   from a DH public key    |       |          |   and decryption          |        |   Box.AE                  |
  |   and a DH private key    |       +----------+ * If idealized, AE works  |<-------+ * Imports the "inner"     |
  | * Imports functions and   |                  |   as follows for honest   |        |   plaintext type from     |
  |   types to handle keys    |                  |   plaintexts              |        |   Box.PKAE and provides   |
  |   from Box.PlainDH        |                  |   * Encryption: Nonces,   |        |   restricted wrapper      |
  |                           |                  |   plaintexts and cipher-  |        |   functions to handle     |
  +------------+--------------+                  |   texts are stored in a   |        |   those plaintexts        |
               ^                                 |   global log              |        |                           |
               |                                 |   * Decryption: Upon re-  |        +---------------------------+
               |                                 |   ception of a nonce and  |
  +------------+--------------+                  |   a ciphertexts, a look-  |
  |                           |                  |   up is performed on the  |
  | Box.PlainDH               |                  |   global log.             |
  |                           |                  |                           |
  | * Provides an functions   |                  +------------+--------------+
  |   and types from Box.AE   |                               |
  |   for Box.DH to use       |                               |
  | * This module exists to   |<------------------------------+
  |   preserve modularity     |
  |                           |
  +---------------------------+

+-------------------------------------------------------------------------------------------------------------------------+

  +---------------------------+
  |                           |
  | Box.Indexing              |
  |                           |
  | * Provides index types    |
  |   for AE and DH keys and  |
  |   payloads                |
  | * Contains two logs:      +---------------------------->+-------------------+
  |   a index log and         |                             |                   |
  |   an honesty log,         |               +------------>| All other modules |
  |   recording freshness and |               |             |                   |
  |   honesty of indices      |               |             +-------------------+
  |                           |               |
  |                           |               |
  +------------+--------------+               |
               ^                              |
               |                              |
               |                              |
               |                              |
  +------------+--------------+               |
  |                           |               |
  | Box.Flags                 |               |
  |                           |               |
  | * Flag interface          |               |
  | * Contains boolean values +---------------+
  |   with which the          |
  |   idealization of AE, DH  |
  |   and PKAE can be         |
  |   controlled              |
  |                           |
  +---------------------------+
```

TODO:
- use curve25519's scalar multiplication
- construct better log_invariants so we can verify them in a reasonable time
- clean up the api and follow naming conventions from the original nacl code and/or other secure_api examples
  - split up functions accordingly?
- provide spec

