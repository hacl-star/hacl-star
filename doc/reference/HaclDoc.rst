HACL APIs
=========

Stream ciphers
--------------

Chacha20
^^^^^^^^

Chacha20 comes in three different variants.

The AVX variant is found in file ``Hacl_Chacha20_Vec128.h`` and exposes two
functions.

.. literalinclude:: ../../dist/portable-gcc-compatible/Hacl_Chacha20_Vec128.h
    :language: c
    :start-after: SNIPPET_START: Hacl_Chacha20_Vec128_chacha20_encrypt_128
    :end-before: SNIPPET_END: Hacl_Chacha20_Vec128_chacha20_encrypt_128

In addition to the encryption, there's also
``Hacl_Chacha20_Vec128_chacha20_decrypt_128`` but since they do exactly the same
thing I'm not sure why there's two variants.
