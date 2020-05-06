CPU autodetection (``EverCrypt_AutoConfig2.h``)
-----------------------------------------------

Clients of EverCrypt **should** call the ``init`` function in order to detect
the target CPU EverCrypt is running on. Failure to do so will result in the
EverCrypt APIs always picking a slow, fallback implementation for all
algorithms.

.. literalinclude:: ../dist/portable-gcc-compatible/EverCrypt_AutoConfig2.h
    :language: c
    :start-after: SNIPPET_START: EverCrypt_AutoConfig2_init
    :end-before: SNIPPET_END: EverCrypt_AutoConfig2_init

After CPU autodetection has run, clients may choose to forbid EverCrypt from
relying on a specific CPU feature. This can be achieved via the various
``disable_*`` functions, e.g.

.. literalinclude:: ../dist/portable-gcc-compatible/EverCrypt_AutoConfig2.h
    :language: c
    :start-after: SNIPPET_START: EverCrypt_AutoConfig2_disable_avx2
    :end-before: SNIPPET_END: EverCrypt_AutoConfig2_disable_avx2

.. note::

  The ``EverCrypt_AutoConfig2_disable_{hacl,vale,openssl,bcrypt}`` functions are
  only exposed for internal testing and should not be called by end-users.

