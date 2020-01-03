Non-agile APIs
--------------

Not all algorithms have a corresponding agile API. For instance, there is no
``EverCrypt_ECDH.h`` yet. However, clients may still want to call, say
``Ed25519`` and enjoy the benefits of multiplexing.

To that end, EverCrypt features a variety of **non-agile**, **multiplexing**
APIs.

Chacha20-Poly1305
^^^^^^^^^^^^^^^^^

Multiplexes between: portable C, AVX, AVX2

Found in ``EverCrypt_Chacha20Poly1305.h``.

See :ref:`hacl-aead` for the API documentation.

Curve25519
^^^^^^^^^^

Multiplexes between: portable C, ADX + BMI2

Found in ``EverCrypt_Curve25519.h``.

See :ref:`hacl-curve25519` for the API documentation.

Poly1305
^^^^^^^^

Multiplexes between: portable C, AVX, AVX2, X64 assembly

Found in ``EverCrypt_Poly1305.h``.

See :ref:`hacl-poly1305` for the API documentation.

Ed25519
^^^^^^^

Found in ``EverCrypt_Ed25519.h``.

.. note::

  This is just a placeholder and there is no multiplexing for this API yet.
