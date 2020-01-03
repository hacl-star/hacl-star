HKDF (``EverCrypt_HKDF.h``)
---------------------------

This API is:

- **agile**
- **multiplexing**: portable C (all); SHAEXT (SHA2-256)
- **NOT** stateful

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

The ``expand`` and ``extract`` functions are agile and multiplexing:

.. literalinclude:: ../dist/portable-gcc-compatible/EverCrypt_HKDF.h
    :language: c
    :start-after: SNIPPET_START: EverCrypt_HKDF_extract *
    :end-before: SNIPPET_END: EverCrypt_HKDF_extract

- ``prk`` is the output parameter
- ``ikm`` means "input key material"
- if ``saltlen`` approaches 4GB then you need to make sure it satisfies
  ``keysized`` in ``Spec.Agile.HMAC.fsti``
- if ``ikmlen`` approaches 4GB then you need to check the preconditions from
  ``extract_st``, in ``EverCrypt.HKDF.fsti``.

.. literalinclude:: ../dist/portable-gcc-compatible/EverCrypt_HKDF.h
    :language: c
    :start-after: SNIPPET_START: EverCrypt_HKDF_expand
    :end-before: SNIPPET_END: EverCrypt_HKDF_expand

- ``okm`` ("output key material") is the output parameter
- if ``prklen`` approaches 4GB then you need to make sure it satisfies
  ``keysized`` in ``Spec.Agile.HMAC.fsti``
- if ``infolen`` approaches 4GB then you need to check the precondition on
  ``infolen`` in ``expand_st``, in ``EverCrypt.HKDF.fsti``.

These functions dynamically dispatch onto one of the specialized, non-agile
versions below.  As such, the cost of agility is one test.

Non-agile API
^^^^^^^^^^^^^

The ``expand_*`` and ``extract_*`` functions are **non-agile** and multiplexing:

.. literalinclude:: ../dist/portable-gcc-compatible/EverCrypt_HKDF.h
    :language: c
    :start-after: SNIPPET_START: EverCrypt_HKDF_expand_sha2_512
    :end-before: SNIPPET_END: EverCrypt_HKDF_expand_sha2_512

.. literalinclude:: ../dist/portable-gcc-compatible/EverCrypt_HKDF.h
    :language: c
    :start-after: SNIPPET_START: EverCrypt_HKDF_extract_sha2_512
    :end-before: SNIPPET_END: EverCrypt_HKDF_extract_sha2_512

A non-agile, non-multiplexing copy of this API exists in ``Hacl_HKDF.h``.
