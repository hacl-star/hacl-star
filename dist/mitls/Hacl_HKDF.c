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
  uint32_t n = len / tlen;
  uint8_t *output;
  if (okm == NULL)
  {
    output = NULL;
  }
  else
  {
    output = okm;
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), tlen + infolen + (uint32_t)1U);
  uint8_t *text = alloca((tlen + infolen + (uint32_t)1U) * sizeof (uint8_t));
  memset(text, 0U, (tlen + infolen + (uint32_t)1U) * sizeof (text[0U]));
  uint8_t *text0 = text + tlen;
  uint8_t *tag;
  if (text == NULL)
  {
    tag = NULL;
  }
  else
  {
    tag = text;
  }
  uint8_t *ctr;
  if (text == NULL)
  {
    ctr = NULL;
  }
  else
  {
    ctr = text + tlen + infolen;
  }
  uint8_t *uu____0;
  if (text == NULL)
  {
    uu____0 = NULL;
  }
  else
  {
    uu____0 = text + tlen;
  }
  bool uu____1 = info == NULL;
  if (!(uu____1 || uu____0 == NULL))
  {
    memcpy(uu____0, info, infolen * sizeof (info[0U]));
  }
  for (uint32_t i = (uint32_t)0U; i < n; i++)
  {
    uint8_t *block;
    if (output == NULL)
    {
      block = NULL;
    }
    else
    {
      block = output + i * tlen;
    }
    ctr[0U] = (uint8_t)(i + (uint32_t)1U);
    if (i == (uint32_t)0U)
    {
      Hacl_HMAC_compute_sha2_256(tag, prk, prklen, text0, infolen + (uint32_t)1U);
    }
    else
    {
      Hacl_HMAC_compute_sha2_256(tag, prk, prklen, text, tlen + infolen + (uint32_t)1U);
    }
    uint8_t *uu____2;
    if (output == NULL)
    {
      uu____2 = NULL;
    }
    else
    {
      uu____2 = output + i * tlen;
    }
    bool uu____3 = tag == NULL;
    if (!(uu____3 || uu____2 == NULL))
    {
      memcpy(uu____2, tag, tlen * sizeof (tag[0U]));
    }
  }
  if (n * tlen < len)
  {
    ctr[0U] = (uint8_t)(n + (uint32_t)1U);
    if (n == (uint32_t)0U)
    {
      Hacl_HMAC_compute_sha2_256(tag, prk, prklen, text0, infolen + (uint32_t)1U);
    }
    else
    {
      Hacl_HMAC_compute_sha2_256(tag, prk, prklen, text, tlen + infolen + (uint32_t)1U);
    }
    uint8_t *block = okm + n * tlen;
    memcpy(block, tag, (len - n * tlen) * sizeof (tag[0U]));
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
  uint32_t n = len / tlen;
  uint8_t *output;
  if (okm == NULL)
  {
    output = NULL;
  }
  else
  {
    output = okm;
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), tlen + infolen + (uint32_t)1U);
  uint8_t *text = alloca((tlen + infolen + (uint32_t)1U) * sizeof (uint8_t));
  memset(text, 0U, (tlen + infolen + (uint32_t)1U) * sizeof (text[0U]));
  uint8_t *text0 = text + tlen;
  uint8_t *tag;
  if (text == NULL)
  {
    tag = NULL;
  }
  else
  {
    tag = text;
  }
  uint8_t *ctr;
  if (text == NULL)
  {
    ctr = NULL;
  }
  else
  {
    ctr = text + tlen + infolen;
  }
  uint8_t *uu____0;
  if (text == NULL)
  {
    uu____0 = NULL;
  }
  else
  {
    uu____0 = text + tlen;
  }
  bool uu____1 = info == NULL;
  if (!(uu____1 || uu____0 == NULL))
  {
    memcpy(uu____0, info, infolen * sizeof (info[0U]));
  }
  for (uint32_t i = (uint32_t)0U; i < n; i++)
  {
    uint8_t *block;
    if (output == NULL)
    {
      block = NULL;
    }
    else
    {
      block = output + i * tlen;
    }
    ctr[0U] = (uint8_t)(i + (uint32_t)1U);
    if (i == (uint32_t)0U)
    {
      Hacl_HMAC_compute_sha2_512(tag, prk, prklen, text0, infolen + (uint32_t)1U);
    }
    else
    {
      Hacl_HMAC_compute_sha2_512(tag, prk, prklen, text, tlen + infolen + (uint32_t)1U);
    }
    uint8_t *uu____2;
    if (output == NULL)
    {
      uu____2 = NULL;
    }
    else
    {
      uu____2 = output + i * tlen;
    }
    bool uu____3 = tag == NULL;
    if (!(uu____3 || uu____2 == NULL))
    {
      memcpy(uu____2, tag, tlen * sizeof (tag[0U]));
    }
  }
  if (n * tlen < len)
  {
    ctr[0U] = (uint8_t)(n + (uint32_t)1U);
    if (n == (uint32_t)0U)
    {
      Hacl_HMAC_compute_sha2_512(tag, prk, prklen, text0, infolen + (uint32_t)1U);
    }
    else
    {
      Hacl_HMAC_compute_sha2_512(tag, prk, prklen, text, tlen + infolen + (uint32_t)1U);
    }
    uint8_t *block = okm + n * tlen;
    memcpy(block, tag, (len - n * tlen) * sizeof (tag[0U]));
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

