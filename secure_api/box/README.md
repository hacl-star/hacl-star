### Verified implementation of crypto_box

The files in this folder are an attempt at providing an F\*
implementation of NaCL's crypto_box. We currently use the Spec.*
version of SecretBox and Curve25519 for encryption and key
derivation. At a later stage we might modify the original construction
by using chacha20poly1305 instead of the original xsalsa20poly1305 as
symmetric encryption algorithm.  This is due to the fact that there is
presently a secure_api for aead based on that algorithm.

We attempt to provide a secure API as described in the parent
directory. Currently, everything is still work in progress. The
original NaCl library by Bernstein et al. can be found
[here](https://nacl.cr.yp.to/).

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
               |                      |                                                            v
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
  | Box.AE.Key                |                  |   global log.             |
  |                           |                  |                           |
  | * Provides a  functions   |                  +------------+--------------+
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
- construct better log_invariants so we can verify them in a reasonable time
- clean up the api and follow naming conventions from the original nacl code and/or other secure_api examples
  - split up functions accordingly?


Notes:
* Module architecture figure created with [this tool](http://asciiflow.com/).
