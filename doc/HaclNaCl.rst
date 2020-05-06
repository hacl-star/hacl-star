.. _hacl-nacl:

NaCl API: Box and SecretBox
---------------------------

HACL* implements the Box and SecretBox API of `NaCl <http://nacl.cr.yp.to/>`_
in a way that is compatible with `libsodium <https://github.com/jedisct1/libsodium>`_.
The functions of this API are in ``Hacl_NaCl.h``.


Public-Key Encryption: Box
^^^^^^^^^^^^^^^^^^^^^^^^^^

The simplest API for Box encryption and decryption is as follows:

.. literalinclude:: ../dist/portable-gcc-compatible/Hacl_NaCl.h
    :language: c
    :start-after: SNIPPET_START: Hacl_NaCl_crypto_box_easy
    :end-before: SNIPPET_END: Hacl_NaCl_crypto_box_easy

The encryption function ``Hacl_NaCl_crypto_box_easy`` takes as its arguments
an output array ``c`` of length ``mlen+16`` bytes, an input array
``m`` of length ``mlen`` bytes, a nonce ``n1`` of length 24 bytes,
the Curve25519 private key ``sk`` of the sender (32 bytes), and the
Curve25519 public key ``pk`` of the recipient (32 bytes).
The function returns 0 on success and -1 (i.e. ``0xffffffff``)  on failure.

.. literalinclude:: ../dist/portable-gcc-compatible/Hacl_NaCl.h
    :language: c
    :start-after: SNIPPET_START: Hacl_NaCl_crypto_box_open_easy
    :end-before: SNIPPET_END: Hacl_NaCl_crypto_box_open_easy

The corresponding decryption function ``Hacl_NaCl_crypto_box_open_easy`` takes the
dual arguments: an input array ``c`` of length ``clen>16`` bytes, an output array
``m`` of length ``clen-16`` bytes, a nonce ``n1`` of length 24 bytes,
the Curve25519 public key ``pk`` of the sender (32 bytes), and the
Curve25519 private key ``sk`` of the recipient (32 bytes).
The function retuens 0 on success and -1 (i.e. ``0xffffffff``)  on failure.

``Hacl_NaCl.h`` also contains two other APIs for Box:

- ``Hacl_NaCl_crypto_box_detached`` and ``Hacl_NaCl_crypto_box_open_detached`` store the
  16-byte authentication tag in in a separate buffer called ``tag``
- To share the expensive X25519 ECDH computation across multiple invocations between
  the same sender and recipient keys, callers can first call ``Hacl_NaCl_crypto_box_beforenm``
  and then use the result to call ``Hacl_NaCl_crypto_box_detached_afternm`` or ``Hacl_NaCl_crypto_box_easy_afternm``
  multiple times.


Symmetric Encryption: SecretBox
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The NaCl API also provides a symmetric encryption primive with the following "easy" API:

.. literalinclude:: ../dist/portable-gcc-compatible/Hacl_NaCl.h
    :language: c
    :start-after: SNIPPET_START: Hacl_NaCl_crypto_secretbox_easy
    :end-before: SNIPPET_END: Hacl_NaCl_crypto_secretbox_easy

.. literalinclude:: ../dist/portable-gcc-compatible/Hacl_NaCl.h
    :language: c
    :start-after: SNIPPET_START: Hacl_NaCl_crypto_secretbox_open_easy
    :end-before: SNIPPET_END: Hacl_NaCl_crypto_secretbox_open_easy

The main difference from the Box API is that these functions take a shared symmetric key ``k`` as
input (instead of Curve25519 keys for the sender and recipient.)
As with Box, there is a separate ``detached`` version of this API.
