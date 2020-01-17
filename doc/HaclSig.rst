.. _hacl-ed25519:

Signatures: Ed25519
-------------------

HACL* implements the Edwards-Curve Digital Signature Algorithm (EdDSA)
construction for the Ed25519 elliptic curve as specified in `IETF RFC 8032 <https://tools.ietf.org/html/rfc8032>`_.
The API for this signature algorithm is in ``Hacl_Ed25519.h``.

Key Generation
^^^^^^^^^^^^^^

Any 32 byte array can be used as an Ed25519 private key. In
practice, private keys should be generated using a cryptographically
strong pseudo-random number generator (CSPRNG).  In some cases, the
private key may be derived as the result of a key derivation function
such as HKDF.

Given a private key, the corresponding public key can be computed
using the ``secret_to_public`` function:

.. literalinclude:: ../dist/portable-gcc-compatible/Hacl_Ed25519.h
    :language: c
    :start-after: SNIPPET_START: Hacl_Ed25519_secret_to_public
    :end-before: SNIPPET_END: Hacl_Ed25519_secret_to_public

The first argument is a pointer to the output public key ``pub`` (64 bytes);
the second argument is a pointer to the input private key ``priv`` (32 bytes).

EdDSA Signing
^^^^^^^^^^^^^

The signature  operation is implemented by the following function:


.. literalinclude:: ../dist/portable-gcc-compatible/Hacl_Ed25519.h
    :language: c
    :start-after: SNIPPET_START: Hacl_Ed25519_sign
    :end-before: SNIPPET_END: Hacl_Ed25519_sign

The first argument is a pointer to the output signature ``signature``;
the second argument is the private key of the signer ``priv``;
the third argument is the length ``len`` of the message to be signed ``msg``.
The size of ``signature`` must be (at least) 64 bytes; the size of the private
key is 32 bytes.

EdDSA Verify
^^^^^^^^^^^^^

To verify an Ed25519 signature, one may call the following function:


.. literalinclude:: ../dist/portable-gcc-compatible/Hacl_Ed25519.h
    :language: c
    :start-after: SNIPPET_START: Hacl_Ed25519_verify
    :end-before: SNIPPET_END: Hacl_Ed25519_verify

The first argument is a pointer to the public key ``pub`` (64 bytes);
the second argument is the length ``len`` of the message to be signed ``msg``;
the last argument is the input signature ``signature``.
If the signature verification succeeds the function returns the boolean ``true``,
otherwise it returns ``false``.

EdDSA Sign Expanded
^^^^^^^^^^^^^^^^^^^

In situations where a signer needs to sign many times with the same
signature key, a part of the signature computation can be shared
between these invocations for efficiency. The caller first calls
``Hacl_Ed25519_expand_keys`` to compute an expanded signing key ``ks``,
and then can use ``ks`` to call ``Hacl_Ed25519_sign_expanded`` multiple
times with different arguments.


.. literalinclude:: ../dist/portable-gcc-compatible/Hacl_Ed25519.h
    :language: c
    :start-after: SNIPPET_START: Hacl_Ed25519_expand_keys
    :end-before: SNIPPET_END: Hacl_Ed25519_expand_keys

.. literalinclude:: ../dist/portable-gcc-compatible/Hacl_Ed25519.h
    :language: c
    :start-after: SNIPPET_START: Hacl_Ed25519_sign_expanded
    :end-before: SNIPPET_END: Hacl_Ed25519_sign_expanded




Other Signature Algorithms: ECDSA with P-256
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

A development branch includes a verified implementation of ECDSA
signatures with the P-256 elliptic curve, which has not yet been
merged to master. Contact the HACL* maintainers if you wish to use
this code.

