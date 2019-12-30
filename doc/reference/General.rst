General recommendations
=======================

Finding the source
------------------

Looking at the original F* files allows the user to identify any preconditions or
remarks that may have been left in there (work is in progress to forward
source-level comments to the generated C code). Indeed, our C code is generated;
as such, some information is lost in the translation process.

.. note::

  It is almost always a good idea to look at F* interface files (``.fsti``) rather
  than implementations (``.fst``). These typically have the most up-to-date
  comments, as well as a wealth of information regarding preconditions, such as
  length of arrays, disjointness, etc. that C clients MUST obey.

There are some general rules for mapping a ``.h`` file to an ``.fsti`` file.

- Files that start with ``Hacl_`` are found in the ``code/`` subdirectory; for
  instance, ``Hacl_HKDF.h`` comes from ``code/hkdf/Hacl.HKDF.fsti``. Some ``.h``
  files may combine multiple source F* files (known as "bundling"); for
  instance, ``Hacl_Hash.h`` combines all files from ``code/hash`` along with
  ``code/sha3``.
- Files that start with ``Lib_`` are found in the ``lib/c`` directory; they are
  hand-written and are assumed to faithfully implement a given F* signature;
  these should be carefully reviewed before any integration. In particular,
  for zero-ing out memory and randomness, we only have basic implementations;
  pull requests welcome.
- Files that start with ``EverCrypt_`` are found in the ``providers/evercrypt``
  directory.

In case finding a particular declaration is important: if a function is named
``Foo_Bar_baz``, then you want to find ``Foo.Bar.fst{,i}``.

Which API to use
----------------

HACL* APIs are specialized for a given architecture revision and do not have any
agility overhead. Consider, for instance, Chacha-Poly encryption from
``Hacl_Chacha20Poly1305_256.h``:

.. literalinclude:: ../../dist/portable-gcc-compatible/Hacl_Chacha20Poly1305_256.h
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

.. literalinclude:: ../../dist/portable-gcc-compatible/EverCrypt_AutoConfig2.h
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

.. literalinclude:: ../../dist/portable-gcc-compatible/EverCrypt_AEAD.h
    :language: c
    :start-after: SNIPPET_START: EverCrypt_AEAD_create_in
    :end-before: SNIPPET_END: EverCrypt_AEAD_create_in

Then, will clients be able to encrypt:

.. literalinclude:: ../../dist/portable-gcc-compatible/EverCrypt_AEAD.h
    :language: c
    :start-after: SNIPPET_START: EverCrypt_AEAD_encrypt
    :end-before: SNIPPET_END: EverCrypt_AEAD_encrypt
