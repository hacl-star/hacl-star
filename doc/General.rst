Digging into the F* source code
===============================

Most users will only ever want to obtain the C or assembly
implementations of various crypto algorithms, but expert
users may want to look at or modify the F* sources.

Finding the F* source
---------------------

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

.. _reading-preconditions:

Reading F* preconditions
------------------------

It is important to be able to read *some* amount of F* code in order to
successfully use an API. For instance, looking at AEAD encryption, there are
various pre-conditions that client must satisfy, related to liveness,
disjointness and array lengths. We expect unverified C clients to abide by these
preconditions; otherwise, none of our verification guarantees hold! As such, it
is up to the user to read the preconditions and make sure they are satisfied.

As an example, consider ``EverCrypt_AEAD_encrypt``. Per the section above, we
look up ``providers/evercrypt/EverCrypt.AEAD.fsti``. The ``encrypt_pre``
definition lists all the properties that must hold for a call to ``encrypt`` to
be valid.

.. literalinclude:: ../providers/evercrypt/EverCrypt.AEAD.fsti
    :start-after: SNIPPET_START: encrypt_pre
    :end-before: SNIPPET_END: encrypt_pre

Here are some examples:

- ``B.length`` denotes the length of a C array; we see that ``iv_len`` **must**
  be the length of the pointer ``iv``, and that this length must be strictly
  positive
- ``loc_disjoint`` or ``B.disjoint`` state that memory chunks **shall** not overlap;
  we see that no overlap is tolerated between ``cipher`` and ``tag``, but that
  ``plain`` and ``cipher`` must be either the same pointer, or non-overlapping
  memory allocations
- ``all_live`` means that all of the pointers in the list **must** be valid
  allocations that have not yet been freed

A few lines below, we see from the signature of ``encrypt`` that the only two
possible errors are ``Success`` and ``InvalidKey``.

Static vs. run-time checks
--------------------------

We sometimes perform additional run-time checks for violations of the API that
are ruled out for verified clients; for instance, continuing with the
``encrypt`` example, we **do** perform a check at run-time for zero-length IVs,
even though no F* client would be allowed to do that.

C clients should not rely on those details, since i) this is best-effort and we
do not offer any guarantee as to which preconditions we check for and ii) the
error that is returned is not captured in the post-condition, since it cannot
happen for verified clients.

