Hashing: SHA-2, SHA-3
---------------------

SHA-2
^^^^^

HACL* implements the SHA-2 suite of hash functions
as described in the NIST publication `FIPS PUB 180-4: Secure Hash Standard  <https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf>`_. The API
for these hash functions is in the file ``Hacl_Hash.h``.

The types for SHA-256, SHA-384, and SHA-512 are as follows:

.. literalinclude:: ../dist/portable-gcc-compatible/Hacl_Hash.h
    :language: c
    :start-after: SNIPPET_START: Hacl_Hash_SHA2_hash_256
    :end-before: SNIPPET_END: Hacl_Hash_SHA2_hash_256

.. literalinclude:: ../dist/portable-gcc-compatible/Hacl_Hash.h
    :language: c
    :start-after: SNIPPET_START: Hacl_Hash_SHA2_hash_384
    :end-before: SNIPPET_END: Hacl_Hash_SHA2_hash_384

.. literalinclude:: ../dist/portable-gcc-compatible/Hacl_Hash.h
    :language: c
    :start-after: SNIPPET_START: Hacl_Hash_SHA2_hash_512
    :end-before: SNIPPET_END: Hacl_Hash_SHA2_hash_512

Each function takes a pointer as its first argument a pointer ``input``
to an array of bytes of length ``input_len`` (the second argument).
The last argument is a pointer ``dst`` to an array of bytes where
the result will be written. All pointers (``input``, ``dst``) must be
live (non-null, non-freed). For SHA-256, ``dst`` must point to an array
allocated with (at least) 32 bytes, for SHA-384, it must have 48 bytes, and for SHA-512 it must have 64 bytes. The ``input`` array is limited to 2^32 bytes.


SHA-3
^^^^^

HACL* also implements the SHA-3 suite of hash algorithms
described in the NIST publication `FIPS PUB 202: SHA-3 Standard  <https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf>`_. The API for
these hash functions is in the file ``Hacl_SHA3.h``.

.. literalinclude:: ../dist/portable-gcc-compatible/Hacl_SHA3.h
    :language: c
    :start-after: SNIPPET_START: Hacl_SHA3_sha3_256
    :end-before: SNIPPET_END: Hacl_SHA3_sha3_256

.. literalinclude:: ../dist/portable-gcc-compatible/Hacl_SHA3.h
    :language: c
    :start-after: SNIPPET_START: Hacl_SHA3_sha3_384
    :end-before: SNIPPET_END: Hacl_SHA3_sha3_384

.. literalinclude:: ../dist/portable-gcc-compatible/Hacl_SHA3.h
    :language: c
    :start-after: SNIPPET_START: Hacl_SHA3_sha3_512
    :end-before: SNIPPET_END: Hacl_SHA3_sha3_512

The API is a little different than SHA-2 in that the first argument
is now the length of the input ``inputByteLen`` and the second
argument is a pointer to the ``input`` array. The last argument
is the ``ouput`` of the hash function. The size of ``output``
matches that of SHA-2 (32/48/64 bytes.)

SHAKE
^^^^^

In addition to the above functions, ``Hacl_SHA3.h`` also provides
the general ``keccak`` function and the two SHAKE constructions
that can produce arbitrary size digests and hence also take
an ``outputByteLen`` as argument. These functions expect the
``output`` array to have at least ``outputByteLen`` bytes

.. literalinclude:: ../dist/portable-gcc-compatible/Hacl_SHA3.h
    :language: c
    :start-after: SNIPPET_START: Hacl_SHA3_shake128_hacl
    :end-before: SNIPPET_END: Hacl_SHA3_shake128_hacl

.. literalinclude:: ../dist/portable-gcc-compatible/Hacl_SHA3.h
    :language: c
    :start-after: SNIPPET_START: Hacl_SHA3_shake256_hacl
    :end-before: SNIPPET_END: Hacl_SHA3_shake256_hacl


Other Hash Functions: Blake-2, MD5, SHA-1
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

A development branch of HACL* contains verified implementations of Blake2s and Blake2b. Contact the HACL* maintainers if you wish to use these implementations.

HACL* also includes implementations of MD5 and SHA1 for backwards compatibility, but we strongly recommend against using these algorithms.


