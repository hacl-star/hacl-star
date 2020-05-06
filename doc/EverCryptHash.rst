Hashing (``EverCrypt_Hash.h``)
------------------------------

This API is:

- **agile**
- **multiplexing**: portable C (all); SHAEXT (SHA2-224, SHA2-256)
- **stateful**

Possible values for the agility argument (``Hacl_Spec.h``) :

.. literalinclude:: ../dist/portable-gcc-compatible/Hacl_Spec.h
    :language: c
    :start-after: SNIPPET_START: Spec_Hash_Definitions_hash_alg
    :end-before: SNIPPET_END: Spec_Hash_Definitions_hash_alg

Supported values for the agility argument: all

Block-based API
^^^^^^^^^^^^^^^

The block-based functions require the client to follow this exact state
machine:

1. one call to ``EverCrypt_Hash_create_in``
2. one call to ``EverCrypt_Hash_init``
3. any number of calls to: ``EverCrypt_Hash_update`` (passing data **exactly** of
   the right block size for the chosen algorithm) or
   ``EverCrypt_Hash_update_multi`` (passing a multiple of the block size)
4. one call to ``EverCrypt_Hash_update_last`` (data strictly smaller than the
   block size)
5. one call to ``EverCrypt_Hash_finish``
6. one call to ``EverCrypt_Hash_free``

Clients may jump to state 2 at any point before state 6.

As evidenced by the state machine, this API requires clients to buffer data and
chunk it along the block size ("block-based"). Furthermore, this API does
not allow feeding more data into the hash function after ``update_last`` has
been called: the client must either proceed with ``finish`` or reset the state
with ``init``.

.. warning::

  This API is error-prone and is not recommended for unverified clients. We
  advise clients use the streaming API described below.

Streaming API
^^^^^^^^^^^^^

The streaming hash API wraps the block-based API with an internal buffer
(at the expense of an extra indirection) and relieves the client from having to
perform modulo computations and block-size management. Furthermore, the
block-based API allows extracting intermediary hashes without invalidating the
state, meaning clients can compute a hash, then later feed more data into the
hash function (at the expense of a state copy).

Clients can allocate state via ``create_in``. This is a non-faillible function
and as such does not return an error code. This is possible because i) we always
have a fallback portable C implementation available for all algorithms and ii)
we do not yet model allocation failures.

.. literalinclude:: ../dist/portable-gcc-compatible/EverCrypt_Hash.h
    :language: c
    :start-after: SNIPPET_START: EverCrypt_Hash_Incremental_create_in
    :end-before: SNIPPET_END: EverCrypt_Hash_Incremental_create_in

Clients can feed an arbitrary amount of data via ``update``:

.. literalinclude:: ../dist/portable-gcc-compatible/EverCrypt_Hash.h
    :language: c
    :start-after: SNIPPET_START: EverCrypt_Hash_Incremental_update
    :end-before: SNIPPET_END: EverCrypt_Hash_Incremental_update

A hash can be extracted at any time by the client without invalidating the
state:

.. literalinclude:: ../dist/portable-gcc-compatible/EverCrypt_Hash.h
    :language: c
    :start-after: SNIPPET_START: EverCrypt_Hash_Incremental_finish
    :end-before: SNIPPET_END: EverCrypt_Hash_Incremental_finish

Once done, clients should use ``free`` which frees all internal buffers and
underlying block-based state:

.. literalinclude:: ../dist/portable-gcc-compatible/EverCrypt_Hash.h
    :language: c
    :start-after: SNIPPET_START: EverCrypt_Hash_Incremental_free
    :end-before: SNIPPET_END: EverCrypt_Hash_Incremental_free

.. note::

  There is no streaming HACL* API for hashes, i.e. clients must go through
  agility and multiplexing to enjoy the streaming hash API.

One-shot API
^^^^^^^^^^^^

If all data is available at once, clients can use the (slightly more efficient),
agile, multiplexing ``EverCrypt_Hash_hash`` function.

.. literalinclude:: ../dist/portable-gcc-compatible/EverCrypt_Hash.h
    :language: c
    :start-after: SNIPPET_START: EverCrypt_Hash_hash *
    :end-before: SNIPPET_END: EverCrypt_Hash_hash

This function merely dispatches onto one of the numerous non-agile specialized
variants. As such, the cost of agility is one test.

For SHA2-256 and SHA2-224, the EverCrypt API provides non-agile, multiplexing
variants:

.. literalinclude:: ../dist/portable-gcc-compatible/EverCrypt_Hash.h
    :language: c
    :start-after: SNIPPET_START: EverCrypt_Hash_hash_256
    :end-before: SNIPPET_END: EverCrypt_Hash_hash_256

For other hash algorithms, for which only one implementation (portable C) is
currently available, clients can use the non-agile, non-multiplexing HACL Hash
API.
