/* MIT License
 *
 * Copyright (c) 2016-2020 INRIA, CMU and Microsoft Corporation
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */


#include "EverCrypt_HKDF.h"



void
EverCrypt_HKDF_expand_sha1(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
)
{
  uint32_t tlen = (uint32_t)20U;
  uint32_t n = len / tlen;
  uint8_t *output = okm;
  KRML_CHECK_SIZE(sizeof (uint8_t), tlen + infolen + (uint32_t)1U);
  uint8_t text[tlen + infolen + (uint32_t)1U];
  memset(text, 0U, (tlen + infolen + (uint32_t)1U) * sizeof (uint8_t));
  uint8_t *text0 = text + tlen;
  uint8_t *tag = text;
  uint8_t *ctr = text + tlen + infolen;
  memcpy(text + tlen, info, infolen * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < n; i++)
  {
    ctr[0U] = (uint8_t)(i + (uint32_t)1U);
    if (i == (uint32_t)0U)
    {
      EverCrypt_HMAC_compute_sha1(tag, prk, prklen, text0, infolen + (uint32_t)1U);
    }
    else
    {
      EverCrypt_HMAC_compute_sha1(tag, prk, prklen, text, tlen + infolen + (uint32_t)1U);
    }
    memcpy(output + i * tlen, tag, tlen * sizeof (uint8_t));
  }
  if (n * tlen < len)
  {
    ctr[0U] = (uint8_t)(n + (uint32_t)1U);
    if (n == (uint32_t)0U)
    {
      EverCrypt_HMAC_compute_sha1(tag, prk, prklen, text0, infolen + (uint32_t)1U);
    }
    else
    {
      EverCrypt_HMAC_compute_sha1(tag, prk, prklen, text, tlen + infolen + (uint32_t)1U);
    }
    uint8_t *block = okm + n * tlen;
    memcpy(block, tag, (len - n * tlen) * sizeof (uint8_t));
  }
}

void
EverCrypt_HKDF_extract_sha1(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
)
{
  EverCrypt_HMAC_compute_sha1(prk, salt, saltlen, ikm, ikmlen);
}

void
EverCrypt_HKDF_expand_sha2_256(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
)
{
  uint32_t tlen = (uint32_t)32U;
  uint32_t n = len / tlen;
  uint8_t *output = okm;
  KRML_CHECK_SIZE(sizeof (uint8_t), tlen + infolen + (uint32_t)1U);
  uint8_t text[tlen + infolen + (uint32_t)1U];
  memset(text, 0U, (tlen + infolen + (uint32_t)1U) * sizeof (uint8_t));
  uint8_t *text0 = text + tlen;
  uint8_t *tag = text;
  uint8_t *ctr = text + tlen + infolen;
  memcpy(text + tlen, info, infolen * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < n; i++)
  {
    ctr[0U] = (uint8_t)(i + (uint32_t)1U);
    if (i == (uint32_t)0U)
    {
      EverCrypt_HMAC_compute_sha2_256(tag, prk, prklen, text0, infolen + (uint32_t)1U);
    }
    else
    {
      EverCrypt_HMAC_compute_sha2_256(tag, prk, prklen, text, tlen + infolen + (uint32_t)1U);
    }
    memcpy(output + i * tlen, tag, tlen * sizeof (uint8_t));
  }
  if (n * tlen < len)
  {
    ctr[0U] = (uint8_t)(n + (uint32_t)1U);
    if (n == (uint32_t)0U)
    {
      EverCrypt_HMAC_compute_sha2_256(tag, prk, prklen, text0, infolen + (uint32_t)1U);
    }
    else
    {
      EverCrypt_HMAC_compute_sha2_256(tag, prk, prklen, text, tlen + infolen + (uint32_t)1U);
    }
    uint8_t *block = okm + n * tlen;
    memcpy(block, tag, (len - n * tlen) * sizeof (uint8_t));
  }
}

void
EverCrypt_HKDF_extract_sha2_256(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
)
{
  EverCrypt_HMAC_compute_sha2_256(prk, salt, saltlen, ikm, ikmlen);
}

void
EverCrypt_HKDF_expand_sha2_384(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
)
{
  uint32_t tlen = (uint32_t)48U;
  uint32_t n = len / tlen;
  uint8_t *output = okm;
  KRML_CHECK_SIZE(sizeof (uint8_t), tlen + infolen + (uint32_t)1U);
  uint8_t text[tlen + infolen + (uint32_t)1U];
  memset(text, 0U, (tlen + infolen + (uint32_t)1U) * sizeof (uint8_t));
  uint8_t *text0 = text + tlen;
  uint8_t *tag = text;
  uint8_t *ctr = text + tlen + infolen;
  memcpy(text + tlen, info, infolen * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < n; i++)
  {
    ctr[0U] = (uint8_t)(i + (uint32_t)1U);
    if (i == (uint32_t)0U)
    {
      EverCrypt_HMAC_compute_sha2_384(tag, prk, prklen, text0, infolen + (uint32_t)1U);
    }
    else
    {
      EverCrypt_HMAC_compute_sha2_384(tag, prk, prklen, text, tlen + infolen + (uint32_t)1U);
    }
    memcpy(output + i * tlen, tag, tlen * sizeof (uint8_t));
  }
  if (n * tlen < len)
  {
    ctr[0U] = (uint8_t)(n + (uint32_t)1U);
    if (n == (uint32_t)0U)
    {
      EverCrypt_HMAC_compute_sha2_384(tag, prk, prklen, text0, infolen + (uint32_t)1U);
    }
    else
    {
      EverCrypt_HMAC_compute_sha2_384(tag, prk, prklen, text, tlen + infolen + (uint32_t)1U);
    }
    uint8_t *block = okm + n * tlen;
    memcpy(block, tag, (len - n * tlen) * sizeof (uint8_t));
  }
}

void
EverCrypt_HKDF_extract_sha2_384(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
)
{
  EverCrypt_HMAC_compute_sha2_384(prk, salt, saltlen, ikm, ikmlen);
}

void
EverCrypt_HKDF_expand_sha2_512(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
)
{
  uint32_t tlen = (uint32_t)64U;
  uint32_t n = len / tlen;
  uint8_t *output = okm;
  KRML_CHECK_SIZE(sizeof (uint8_t), tlen + infolen + (uint32_t)1U);
  uint8_t text[tlen + infolen + (uint32_t)1U];
  memset(text, 0U, (tlen + infolen + (uint32_t)1U) * sizeof (uint8_t));
  uint8_t *text0 = text + tlen;
  uint8_t *tag = text;
  uint8_t *ctr = text + tlen + infolen;
  memcpy(text + tlen, info, infolen * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < n; i++)
  {
    ctr[0U] = (uint8_t)(i + (uint32_t)1U);
    if (i == (uint32_t)0U)
    {
      EverCrypt_HMAC_compute_sha2_512(tag, prk, prklen, text0, infolen + (uint32_t)1U);
    }
    else
    {
      EverCrypt_HMAC_compute_sha2_512(tag, prk, prklen, text, tlen + infolen + (uint32_t)1U);
    }
    memcpy(output + i * tlen, tag, tlen * sizeof (uint8_t));
  }
  if (n * tlen < len)
  {
    ctr[0U] = (uint8_t)(n + (uint32_t)1U);
    if (n == (uint32_t)0U)
    {
      EverCrypt_HMAC_compute_sha2_512(tag, prk, prklen, text0, infolen + (uint32_t)1U);
    }
    else
    {
      EverCrypt_HMAC_compute_sha2_512(tag, prk, prklen, text, tlen + infolen + (uint32_t)1U);
    }
    uint8_t *block = okm + n * tlen;
    memcpy(block, tag, (len - n * tlen) * sizeof (uint8_t));
  }
}

void
EverCrypt_HKDF_extract_sha2_512(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
)
{
  EverCrypt_HMAC_compute_sha2_512(prk, salt, saltlen, ikm, ikmlen);
}

void
EverCrypt_HKDF_expand_blake2s(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
)
{
  uint32_t tlen = (uint32_t)32U;
  uint32_t n = len / tlen;
  uint8_t *output = okm;
  KRML_CHECK_SIZE(sizeof (uint8_t), tlen + infolen + (uint32_t)1U);
  uint8_t text[tlen + infolen + (uint32_t)1U];
  memset(text, 0U, (tlen + infolen + (uint32_t)1U) * sizeof (uint8_t));
  uint8_t *text0 = text + tlen;
  uint8_t *tag = text;
  uint8_t *ctr = text + tlen + infolen;
  memcpy(text + tlen, info, infolen * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < n; i++)
  {
    ctr[0U] = (uint8_t)(i + (uint32_t)1U);
    if (i == (uint32_t)0U)
    {
      EverCrypt_HMAC_compute_blake2s(tag, prk, prklen, text0, infolen + (uint32_t)1U);
    }
    else
    {
      EverCrypt_HMAC_compute_blake2s(tag, prk, prklen, text, tlen + infolen + (uint32_t)1U);
    }
    memcpy(output + i * tlen, tag, tlen * sizeof (uint8_t));
  }
  if (n * tlen < len)
  {
    ctr[0U] = (uint8_t)(n + (uint32_t)1U);
    if (n == (uint32_t)0U)
    {
      EverCrypt_HMAC_compute_blake2s(tag, prk, prklen, text0, infolen + (uint32_t)1U);
    }
    else
    {
      EverCrypt_HMAC_compute_blake2s(tag, prk, prklen, text, tlen + infolen + (uint32_t)1U);
    }
    uint8_t *block = okm + n * tlen;
    memcpy(block, tag, (len - n * tlen) * sizeof (uint8_t));
  }
}

void
EverCrypt_HKDF_extract_blake2s(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
)
{
  EverCrypt_HMAC_compute_blake2s(prk, salt, saltlen, ikm, ikmlen);
}

void
EverCrypt_HKDF_expand_blake2b(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
)
{
  uint32_t tlen = (uint32_t)64U;
  uint32_t n = len / tlen;
  uint8_t *output = okm;
  KRML_CHECK_SIZE(sizeof (uint8_t), tlen + infolen + (uint32_t)1U);
  uint8_t text[tlen + infolen + (uint32_t)1U];
  memset(text, 0U, (tlen + infolen + (uint32_t)1U) * sizeof (uint8_t));
  uint8_t *text0 = text + tlen;
  uint8_t *tag = text;
  uint8_t *ctr = text + tlen + infolen;
  memcpy(text + tlen, info, infolen * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < n; i++)
  {
    ctr[0U] = (uint8_t)(i + (uint32_t)1U);
    if (i == (uint32_t)0U)
    {
      EverCrypt_HMAC_compute_blake2b(tag, prk, prklen, text0, infolen + (uint32_t)1U);
    }
    else
    {
      EverCrypt_HMAC_compute_blake2b(tag, prk, prklen, text, tlen + infolen + (uint32_t)1U);
    }
    memcpy(output + i * tlen, tag, tlen * sizeof (uint8_t));
  }
  if (n * tlen < len)
  {
    ctr[0U] = (uint8_t)(n + (uint32_t)1U);
    if (n == (uint32_t)0U)
    {
      EverCrypt_HMAC_compute_blake2b(tag, prk, prklen, text0, infolen + (uint32_t)1U);
    }
    else
    {
      EverCrypt_HMAC_compute_blake2b(tag, prk, prklen, text, tlen + infolen + (uint32_t)1U);
    }
    uint8_t *block = okm + n * tlen;
    memcpy(block, tag, (len - n * tlen) * sizeof (uint8_t));
  }
}

void
EverCrypt_HKDF_extract_blake2b(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
)
{
  EverCrypt_HMAC_compute_blake2b(prk, salt, saltlen, ikm, ikmlen);
}

void
EverCrypt_HKDF_expand(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
)
{
  switch (a)
  {
    case Spec_Hash_Definitions_SHA1:
      {
        EverCrypt_HKDF_expand_sha1(okm, prk, prklen, info, infolen, len);
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        EverCrypt_HKDF_expand_sha2_256(okm, prk, prklen, info, infolen, len);
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        EverCrypt_HKDF_expand_sha2_384(okm, prk, prklen, info, infolen, len);
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        EverCrypt_HKDF_expand_sha2_512(okm, prk, prklen, info, infolen, len);
        break;
      }
    case Spec_Hash_Definitions_Blake2S:
      {
        EverCrypt_HKDF_expand_blake2s(okm, prk, prklen, info, infolen, len);
        break;
      }
    case Spec_Hash_Definitions_Blake2B:
      {
        EverCrypt_HKDF_expand_blake2b(okm, prk, prklen, info, infolen, len);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

void
EverCrypt_HKDF_extract(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
)
{
  switch (a)
  {
    case Spec_Hash_Definitions_SHA1:
      {
        EverCrypt_HKDF_extract_sha1(prk, salt, saltlen, ikm, ikmlen);
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        EverCrypt_HKDF_extract_sha2_256(prk, salt, saltlen, ikm, ikmlen);
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        EverCrypt_HKDF_extract_sha2_384(prk, salt, saltlen, ikm, ikmlen);
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        EverCrypt_HKDF_extract_sha2_512(prk, salt, saltlen, ikm, ikmlen);
        break;
      }
    case Spec_Hash_Definitions_Blake2S:
      {
        EverCrypt_HKDF_extract_blake2s(prk, salt, saltlen, ikm, ikmlen);
        break;
      }
    case Spec_Hash_Definitions_Blake2B:
      {
        EverCrypt_HKDF_extract_blake2b(prk, salt, saltlen, ikm, ikmlen);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

KRML_DEPRECATED("expand")

void
EverCrypt_HKDF_hkdf_expand(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
)
{
  EverCrypt_HKDF_expand(a, okm, prk, prklen, info, infolen, len);
}

KRML_DEPRECATED("extract")

void
EverCrypt_HKDF_hkdf_extract(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
)
{
  EverCrypt_HKDF_extract(a, prk, salt, saltlen, ikm, ikmlen);
}

