Non-agile APIs
--------------

Not all algorithms have a corresponding agile API. For instance, there is no
``EverCrypt_ECDH.h`` yet. However, clients may still want to call, say
``Curve25519`` and enjoy the benefits of multiplexing.

To that end, EverCrypt features a variety of **non-agile**, **multiplexing**
APIs.

Chacha20-Poly1305
^^^^^^^^^^^^^^^^^

Multiplexes between: portable C, AVX, AVX2

Found in ``EverCrypt_Chacha20Poly1305.h``.

See :ref:`hacl-aead` for the API documentation, which is identical.

Curve25519
^^^^^^^^^^

Multiplexes between: portable C, ADX + BMI2

Found in ``EverCrypt_Curve25519.h``.

See :ref:`hacl-curve25519` for the API documentation, which is identical.

Poly1305
^^^^^^^^

Multiplexes between: portable C, AVX, AVX2, X64 assembly

Found in ``EverCrypt_Poly1305.h``.

.. literalinclude:: ../dist/portable-gcc-compatible/EverCrypt_Poly1305.h
    :language: c
    :start-after: SNIPPET_START: EverCrypt_Poly1305_poly1305
    :end-before: SNIPPET_END: EverCrypt_Poly1305_poly1305

- ``dst`` must be at least 16 bytes
- if ``len``, the length of ``src``, gets close to 4GB, you need to read the
  precondition in ``EverCrypt.Poly1305.fsti``
- ``key`` must be at least 32 bytes

Ed25519
^^^^^^^

Found in ``EverCrypt_Ed25519.h``.

.. note::

  This is just a placeholder and there is no multiplexing for this API yet.
