HMAC-DRBG (``EverCrypt_DRBG.h``)
--------------------------------

This API is:

- **agile**
- **multiplexing**: portable C (all); SHAEXT (SHA2-256)
- stateful

Possible values for the agility argument (``Hacl_Spec.h``) :

.. literalinclude:: ../dist/portable-gcc-compatible/Hacl_Spec.h
    :language: c
    :start-after: SNIPPET_START: Spec_Hash_Definitions_hash_alg
    :end-before: SNIPPET_END: Spec_Hash_Definitions_hash_alg

Supported values for the agility argument: SHA1; SHA2_256; SHA2_384; SHA2_512.

.. note::
  As always, the source is authoritative and you should check ``is_supported_alg``
  in ``EverCrypt.HMAC.fsti``.

Agile API
^^^^^^^^^

Non-agile API
^^^^^^^^^^^^^
