Randomness
-----------------

HACL* is equipped with a randomness function implemented with
platform dependant code for Unix and Windows.

.. literalinclude:: ../dist/portable-gcc-compatible/Lib_RandomBuffer_System.h
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
