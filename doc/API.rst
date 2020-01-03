Which API to use
----------------

HACL* APIs are specialized for a given architecture revision and do not have any
agility overhead. Consider, for instance, Chacha-Poly encryption from
``Hacl_Chacha20Poly1305_256.h``:

.. literalinclude:: ../dist/portable-gcc-compatible/Hacl_Chacha20Poly1305_256.h
    :language: c
    :start-after: SNIPPET_START: Hacl_Chacha20Poly1305_256_aead_encrypt
    :end-before: SNIPPET_END: Hacl_Chacha20Poly1305_256_aead_encrypt

In order to use this function, you must ascertain that the architecture you're
running on supports 256-bit vector instructions (AVX2 + SSE4); furthermore, your
code will have to be changed if you need another AEAD algorithm such as AES-GCM.
This is an efficient API, as it does not require any extra API calls and does
not allocate any intermediary state.

EverCrypt APIs, on the other hand, can do CPU detection for clients, via a helper
function found in ``EverCrypt_AutoConfig2.h``.

.. literalinclude:: ../dist/portable-gcc-compatible/EverCrypt_AutoConfig2.h
    :language: c
    :start-after: SNIPPET_START: EverCrypt_AutoConfig2_init
    :end-before: SNIPPET_END: EverCrypt_AutoConfig2_init

EverCrypt APIs are generally agile, i.e. clients only need to change one
argument to a function call in order to use a different algorithm; furthermore,
those APIs are multiplexing, i.e. they automatically pick the most suitable
implementation based ont he results of target CPU detection.

This means that the EverCrypt API for Chacha-Poly is found in
``EverCrypt_AEAD.h``; clients are expected to first allocate state, passing in
the desired AEAD algorithm as a parameter (agility):

.. literalinclude:: ../dist/portable-gcc-compatible/EverCrypt_AEAD.h
    :language: c
    :start-after: SNIPPET_START: EverCrypt_AEAD_create_in
    :end-before: SNIPPET_END: EverCrypt_AEAD_create_in

Then, will clients be able to encrypt:

.. literalinclude:: ../dist/portable-gcc-compatible/EverCrypt_AEAD.h
    :language: c
    :start-after: SNIPPET_START: EverCrypt_AEAD_encrypt
    :end-before: SNIPPET_END: EverCrypt_AEAD_encrypt

