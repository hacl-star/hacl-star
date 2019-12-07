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


Randomness
-----------------

HACL* is equipped with a randomness function implemented with
platform dependant code for Unix and Windows.

.. literalinclude:: ../../dist/portable-gcc-compatible/Lib_RandomBuffer_System.h
    :language: c
    :start-after: SNIPPET_START: Lib_RandomBuffer_System_randombytes
    :end-before: SNIPPET_END: Lib_RandomBuffer_System_randombytes

It takes a pointer to a memory location and a number of random bytes
to be written from that location. Beware of not asking for more bytes
than owned.

Internally, ``read_random_bytes`` is implemented using
``CryptGenRandom`` for Microsoft Windows and using ``/dev/urandom``
for Unix platforms.

.. warning:: This file is handwritten and is part of the TCB, hence it
             should be minimally reviewed before being used.
