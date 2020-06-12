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


#include "Hacl_HKDF.h"

void
Hacl_HKDF_expand_sha2_256(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
)
{
  uint32_t tlen = (uint32_t)32U;
  uint32_t n1 = len / tlen;
  uint8_t *output = okm;
  KRML_CHECK_SIZE(sizeof (uint8_t), tlen + infolen + (uint32_t)1U);
  uint8_t *text = alloca((tlen + infolen + (uint32_t)1U) * sizeof (uint8_t));
  memset(text, 0U, (tlen + infolen + (uint32_t)1U) * sizeof (text[0U]));
  uint8_t *text0 = text + tlen;
  uint8_t *tag = text;
  uint8_t *ctr = text + tlen + infolen;
  memcpy(text + tlen, info, infolen * sizeof (info[0U]));
  for (uint32_t i = (uint32_t)0U; i < n1; i++)
  {
    ctr[0U] = (uint8_t)(i + (uint32_t)1U);
    if (i == (uint32_t)0U)
    {
      Hacl_HMAC_compute_sha2_256(tag, prk, prklen, text0, infolen + (uint32_t)1U);
    }
    else
    {
      Hacl_HMAC_compute_sha2_256(tag, prk, prklen, text, tlen + infolen + (uint32_t)1U);
    }
    memcpy(output + i * tlen, tag, tlen * sizeof (tag[0U]));
  }
  if (n1 * tlen < len)
  {
    ctr[0U] = (uint8_t)(n1 + (uint32_t)1U);
    if (n1 == (uint32_t)0U)
    {
      Hacl_HMAC_compute_sha2_256(tag, prk, prklen, text0, infolen + (uint32_t)1U);
    }
    else
    {
      Hacl_HMAC_compute_sha2_256(tag, prk, prklen, text, tlen + infolen + (uint32_t)1U);
    }
    uint8_t *block = okm + n1 * tlen;
    memcpy(block, tag, (len - n1 * tlen) * sizeof (tag[0U]));
  }
}

void
Hacl_HKDF_extract_sha2_256(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
)
{
  Hacl_HMAC_compute_sha2_256(prk, salt, saltlen, ikm, ikmlen);
}

void
Hacl_HKDF_expand_sha2_512(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
)
{
  uint32_t tlen = (uint32_t)64U;
  uint32_t n1 = len / tlen;
  uint8_t *output = okm;
  KRML_CHECK_SIZE(sizeof (uint8_t), tlen + infolen + (uint32_t)1U);
  uint8_t *text = alloca((tlen + infolen + (uint32_t)1U) * sizeof (uint8_t));
  memset(text, 0U, (tlen + infolen + (uint32_t)1U) * sizeof (text[0U]));
  uint8_t *text0 = text + tlen;
  uint8_t *tag = text;
  uint8_t *ctr = text + tlen + infolen;
  memcpy(text + tlen, info, infolen * sizeof (info[0U]));
  for (uint32_t i = (uint32_t)0U; i < n1; i++)
  {
    ctr[0U] = (uint8_t)(i + (uint32_t)1U);
    if (i == (uint32_t)0U)
    {
      Hacl_HMAC_compute_sha2_512(tag, prk, prklen, text0, infolen + (uint32_t)1U);
    }
    else
    {
      Hacl_HMAC_compute_sha2_512(tag, prk, prklen, text, tlen + infolen + (uint32_t)1U);
    }
    memcpy(output + i * tlen, tag, tlen * sizeof (tag[0U]));
  }
  if (n1 * tlen < len)
  {
    ctr[0U] = (uint8_t)(n1 + (uint32_t)1U);
    if (n1 == (uint32_t)0U)
    {
      Hacl_HMAC_compute_sha2_512(tag, prk, prklen, text0, infolen + (uint32_t)1U);
    }
    else
    {
      Hacl_HMAC_compute_sha2_512(tag, prk, prklen, text, tlen + infolen + (uint32_t)1U);
    }
    uint8_t *block = okm + n1 * tlen;
    memcpy(block, tag, (len - n1 * tlen) * sizeof (tag[0U]));
  }
}

void
Hacl_HKDF_extract_sha2_512(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
)
{
  Hacl_HMAC_compute_sha2_512(prk, salt, saltlen, ikm, ikmlen);
}

