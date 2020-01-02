Legacy EverCrypt headers (``EverCrypt.h``, ``EverCrypt_Hacl.h``, ``EverCrypt_Vale.h``)
--------------------------------------------------------------------------------------

.. warning::

  These are UNVERIFIED, legacy APIs and should not be used. In addition,
  ``EverCrypt.h`` relies on OpenSSL or BCrypt under the hood and is only there
  to support the needs of miTLS as we finish implementing remaining algorithms
  in EverCrypt.

If you were previously using ``EverCrypt.h``:

- Users of AES-GCM should use ``EverCrypt_AEAD.h`` instead with a suitable
  algorithm parameter.
- Users of AES-CTR should use ``EverCrypt_CTR.h``
- Users of randomness should use ``Lib.System.RandomBuffer`` combined with
  ``EverCrypt.HMAC.DRBG``
