.. _hacl-aead:

AEAD: Chacha20-Poly1305
-----------------------

HACL* implements the Chacha20-Poly1305 Authenticated Encryption
with Associated Data (AEAD) construction
specified in `IETF RFC 8439 <https://tools.ietf.org/html/rfc8439>`_.
The library includes three implementations of this construction,
all with the same API, but meant for use on different platforms:

- ``Hacl_AEAD_Chacha20Poly1305.h`` contains a portable C implementation that can
  be compiled and run on any 32-bit platform
- ``Hacl_AEAD_Chacha20Poly1305_Simd128.h`` contains a 128-bit vectorized C
  implementation that can be compiled and run on any platform that supports the
  Intel AVX instruction set. On a development branch, we also support the ARM
  Neon instruction set.
- ``Hacl_AEAD_Chacha20Poly1305_Simd256.h`` contains a 256-bit vectorized C
  implementation that can be compiled and run on any platform that supports the
  Intel AVX2 instruction set.

All three versions provide a similar API for AEAD encryption and decryption:

AEAD Encryption
^^^^^^^^^^^^^^^

.. literalinclude:: ../dist/portable-gcc-compatible/Hacl_AEAD_Chacha20Poly1305.h
    :language: c
    :start-after: SNIPPET_START: Hacl_AEAD_Chacha20Poly1305_encrypt
    :end-before: SNIPPET_END: Hacl_AEAD_Chacha20Poly1305_encrypt

The argument ``key`` is a pointer to the AEAD key (an array of 32 bytes);
``nonce`` is a pointer to the AEAD nonce (12 bytes); ``input`` is the input
array of length ``input_len``; ``data`` is the associated data array of length
``data_len``; the output ciphertext also has ``input_len`` bytes and is stored
in ``output``; the output tag has 16 bytes and is stored in ``tag``;

The types of the encryption functions for the other two versions are identical,
except that they are called ``Hacl_AEAD_Chacha20Poly1305_Simd128_encrypt`` and
``Hacl_AEAD_Chacha20Poly1305_Simd256_encrypt``.


AEAD Decryption
^^^^^^^^^^^^^^^

The AEAD decryption function has the following type:

.. literalinclude:: ../dist/portable-gcc-compatible/Hacl_AEAD_Chacha20Poly1305.h
    :language: c
    :start-after: SNIPPET_START: Hacl_AEAD_Chacha20Poly1305_decrypt
    :end-before: SNIPPET_END: Hacl_AEAD_Chacha20Poly1305_decrypt

The arguments ``key``, ``nonce``, ``data``, and ``data_len`` are the same as in
encryption. The argument ``input`` is the length of the input ciphertext
``input``; and ``tag`` holds the input tag. If decryption succeeds, the
resulting plaintext is stored in ``output`` and the function returns the success
code 0. If decryption fails, the array ``output`` remains unchanged and the
function returns the error code 1.

The types of the decryption functions for the other two versions are identical,
except that they are called ``Hacl_AEAD_Chacha20Poly1305_Simd128_decrypt`` and
``Hacl_AEAD_Chacha20Poly1305_Simd256_decrypt``.

Chacha20 and Poly1305
^^^^^^^^^^^^^^^^^^^^^

The implementation of each version of Chacha20Poly1305 relies
internally on corresponding implementations of the Chacha20 cipher and
Poly1305 MAC.  The APIs for these constructions can be found in their
own header files (e.g. ``Hacl_Chacha20_Vec256.h``). Developers can directly
use these APIs to build other constructions based on Chacha20 or Poly1305,
but we do not recommend their use outside the AEAD API.
