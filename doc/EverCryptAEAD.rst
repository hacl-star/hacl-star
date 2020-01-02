AEAD (``EverCrypt_AEAD.h``)
---------------------------

This API is:

- **agile**
- **multiplexing**: portable C (Chacha-Poly only); AVX (Chacha-Poly); AVX2
  (Chacha-Poly); ADX + BMI2 (AES128-GCM, AES256-GCM)
- **stateful**

Possible values for the agility argument (``Hacl_Spec.h``) :

.. literalinclude:: ../dist/portable-gcc-compatible/Hacl_Spec.h
    :language: c
    :start-after: SNIPPET_START: Spec_Agile_AEAD_alg
    :end-before: SNIPPET_END: Spec_Agile_AEAD_alg

Supported values for the agility argument: ``Spec_Agile_AEAD_AES128_GCM``,
``Spec_Agile_AEAD_AES256_GCM``, ``Spec_Agile_AEAD_CHACHA20_POLY1305``

State management
^^^^^^^^^^^^^^^^

Clients are first expected to allocate persistent state, which performs key
expansion and precomputes internal data for AES-GCM.

.. literalinclude:: ../dist/portable-gcc-compatible/EverCrypt_AEAD.h
    :language: c
    :start-after: SNIPPET_START: EverCrypt_AEAD_create_in
    :end-before: SNIPPET_END: EverCrypt_AEAD_create_in

The type ``EverCrypt_AEAD_state_s`` is a C abstract type which cannot be
allocated by clients, as is it an incomplete struct type. Therefore, the
expected usage for initialization is:

.. code-block:: c

  EverCrypt_AEAD_state_s *dst;
  EverCrypt_Error_error ret =
    EverCrypt_AEAD_create_in(Spec_Agile_AEAD_CHACHA20_POLY1305, &dst, key);

Possible error codes can be determined by looking at the original F* signature
for ``create_in``; at the time of writing, the function may return ``Success``,
or ``UnsupportedAlgorithm``. All other cases are eliminated via the ``_ ->
False`` in the post-condition.

``UnsupportedAlgorithm`` may be returned because of an unsupported algorithm
(e.g. AES-CCM) , or because no implementation is available for the target
platform (e.g. AES-GCM without ADX+BMI2).

State **must** be freed via the ``free`` function:

.. literalinclude:: ../dist/portable-gcc-compatible/EverCrypt_AEAD.h
    :language: c
    :start-after: SNIPPET_START: EverCrypt_AEAD_free
    :end-before: SNIPPET_END: EverCrypt_AEAD_free

Encryption and decryption
^^^^^^^^^^^^^^^^^^^^^^^^^

Both encryption and decryption take a piece of state which holds the key; a
piece of state may be reused as many times as desired.

Encryption has a substantial amount of preconditions; see ``encrypt_pre`` in
``EverCrypt.AEAD.fsti``, and :ref:`reading-preconditions` for a primer on
deciphering F* code.

At the time of writing, ``encrypt`` may return either ``Success`` or
``InvalidKey``. The latter is returned if and only if the ``s`` parameter is
``NULL``.

.. literalinclude:: ../dist/portable-gcc-compatible/EverCrypt_AEAD.h
    :language: c
    :start-after: SNIPPET_START: EverCrypt_AEAD_encrypt
    :end-before: SNIPPET_END: EverCrypt_AEAD_encrypt

.. note::

  There is no length parameter for the tag; looking at the source
  ``EverCrypt.AEAD.fsti``, one can see a precondition of the form ``B.length tag
  = tag_length a``, i.e. the length of the ``tag`` array must be of a suitable
  length for the algorithm ``a``. See ``Spec.Agile.AEAD.fsti`` for the
  definition of ``tag_length``. **Unverified clients are strongly encouraged
  to perform a run-time check!**

.. literalinclude:: ../dist/portable-gcc-compatible/EverCrypt_AEAD.h
    :language: c
    :start-after: SNIPPET_START: EverCrypt_AEAD_decrypt
    :end-before: SNIPPET_END: EverCrypt_AEAD_decrypt

