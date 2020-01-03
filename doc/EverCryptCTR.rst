CTR-mode encryption (``EverCrypt_CTR.h``)
-----------------------------------------

.. warning::

  **This API is a work-in-progress and is not fully verified.** If you need it
  for something serious, let us know and we'll prioritize.

  - It doesn't multiplex across all implementations of Chacha-Poly
  - It doesn't offer complete encryption, only block-by-block
  - It has no streaming API

This API is:

- **agile**
- **multiplexing**: portable C (Chacha-Poly); ADX + BMI2 (AES128-GCM, AES256-GCM)
- **stateful**

Possible values for the agility argument (``Hacl_Spec.h``) :

.. literalinclude:: ../dist/portable-gcc-compatible/Hacl_Spec.h
    :language: c
    :start-after: SNIPPET_START: Spec_Agile_Cipher_cipher_alg
    :end-before: SNIPPET_END: Spec_Agile_Cipher_cipher_alg

Supported values for the agility argument: all

State management
^^^^^^^^^^^^^^^^

Clients are first expected to allocate persistent state via ``create_in``, which
stores the expanded key along with the current value of the counter.

.. literalinclude:: ../dist/portable-gcc-compatible/EverCrypt_CTR.h
    :language: c
    :start-after: SNIPPET_START: EverCrypt_CTR_create_in
    :end-before: SNIPPET_END: EverCrypt_CTR_create_in

The expected usage for ``create_in`` is similar to ``EverCrypt_AEAD_create_in``,
except arbitrary-length IVs are not supported; IV lengths must satisfy the
``nounce_bound`` predicate from ``Spec.Agile.CTR.fsti``. Clients are also
expected to pass the initial value of the counter.

State can be reset to a different IV and counter value using the ``init``
function. (This function really should be called ``reset``.)

.. literalinclude:: ../dist/portable-gcc-compatible/EverCrypt_CTR.h
    :language: c
    :start-after: SNIPPET_START: EverCrypt_CTR_init
    :end-before: SNIPPET_END: EverCrypt_CTR_init

State **must** be called via ``free``.

CTR mode of operation
^^^^^^^^^^^^^^^^^^^^^

The ``update_block`` function encrypts a block-sized piece of data using the CTR
mode, and internally increments the state by one.

.. literalinclude:: ../dist/portable-gcc-compatible/EverCrypt_CTR.h
    :language: c
    :start-after: SNIPPET_START: EverCrypt_CTR_update_block
    :end-before: SNIPPET_END: EverCrypt_CTR_update_block


