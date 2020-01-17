HMAC (``EverCrypt_HMAC.h``)
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

The ``compute`` function is agile and multiplexing:

.. literalinclude:: ../dist/portable-gcc-compatible/EverCrypt_HMAC.h
    :language: c
    :start-after: SNIPPET_START: EverCrypt_HMAC_compute *
    :end-before: SNIPPET_END: EverCrypt_HMAC_compute

It dynamically dispatches onto one of the specialized, non-agile versions below.
As such, the cost of agility is one test.

- The ``mac`` argument must have a suitable hash length for the choice of
  algorithm; see ``hash_length`` in ``Spec.Agile.Hash.fsti``
- If ``keylen`` approaches 4GB then you need to make sure it satisfies
  ``keysized`` in ``Spec.Agile.HMAC.fsti``
- If your ``datalen`` approaches 4GB then you need to check the refinement on
  the ``data`` parameter of ``compute_st``, in ``EverCrypt.HMAC.fsti``.

Non-agile API
^^^^^^^^^^^^^

The ``compute_*`` functions are **non-agile** and multiplexing:

.. literalinclude:: ../dist/portable-gcc-compatible/EverCrypt_HMAC.h
    :language: c
    :start-after: SNIPPET_START: EverCrypt_HMAC_compute_sha2_256
    :end-before: SNIPPET_END: EverCrypt_HMAC_compute_sha2_256

A non-agile, non-multiplexing copy of this API exists in ``Hacl_HMAC.h``.
