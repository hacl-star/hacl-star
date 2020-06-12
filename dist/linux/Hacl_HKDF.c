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

void Hacl_HKDF_expand_sha2_256(u8 *okm, u8 *prk, u32 prklen, u8 *info, u32 infolen, u32 len)
{
  u32 tlen = (u32)32U;
  u32 n1 = len / tlen;
  u8 *output = okm;
  KRML_CHECK_SIZE(sizeof (u8), tlen + infolen + (u32)1U);
  {
    u8 text[tlen + infolen + (u32)1U];
    memset(text, 0U, (tlen + infolen + (u32)1U) * sizeof (text[0U]));
    {
      u8 *text0 = text + tlen;
      u8 *tag = text;
      u8 *ctr = text + tlen + infolen;
      memcpy(text + tlen, info, infolen * sizeof (info[0U]));
      {
        u32 i;
        for (i = (u32)0U; i < n1; i++)
        {
          ctr[0U] = (u8)(i + (u32)1U);
          if (i == (u32)0U)
            Hacl_HMAC_compute_sha2_256(tag, prk, prklen, text0, infolen + (u32)1U);
          else
            Hacl_HMAC_compute_sha2_256(tag, prk, prklen, text, tlen + infolen + (u32)1U);
          memcpy(output + i * tlen, tag, tlen * sizeof (tag[0U]));
        }
      }
      if (n1 * tlen < len)
      {
        ctr[0U] = (u8)(n1 + (u32)1U);
        if (n1 == (u32)0U)
          Hacl_HMAC_compute_sha2_256(tag, prk, prklen, text0, infolen + (u32)1U);
        else
          Hacl_HMAC_compute_sha2_256(tag, prk, prklen, text, tlen + infolen + (u32)1U);
        {
          u8 *block = okm + n1 * tlen;
          memcpy(block, tag, (len - n1 * tlen) * sizeof (tag[0U]));
        }
      }
    }
  }
}

void Hacl_HKDF_extract_sha2_256(u8 *prk, u8 *salt, u32 saltlen, u8 *ikm, u32 ikmlen)
{
  Hacl_HMAC_compute_sha2_256(prk, salt, saltlen, ikm, ikmlen);
}

void Hacl_HKDF_expand_sha2_512(u8 *okm, u8 *prk, u32 prklen, u8 *info, u32 infolen, u32 len)
{
  u32 tlen = (u32)64U;
  u32 n1 = len / tlen;
  u8 *output = okm;
  KRML_CHECK_SIZE(sizeof (u8), tlen + infolen + (u32)1U);
  {
    u8 text[tlen + infolen + (u32)1U];
    memset(text, 0U, (tlen + infolen + (u32)1U) * sizeof (text[0U]));
    {
      u8 *text0 = text + tlen;
      u8 *tag = text;
      u8 *ctr = text + tlen + infolen;
      memcpy(text + tlen, info, infolen * sizeof (info[0U]));
      {
        u32 i;
        for (i = (u32)0U; i < n1; i++)
        {
          ctr[0U] = (u8)(i + (u32)1U);
          if (i == (u32)0U)
            Hacl_HMAC_compute_sha2_512(tag, prk, prklen, text0, infolen + (u32)1U);
          else
            Hacl_HMAC_compute_sha2_512(tag, prk, prklen, text, tlen + infolen + (u32)1U);
          memcpy(output + i * tlen, tag, tlen * sizeof (tag[0U]));
        }
      }
      if (n1 * tlen < len)
      {
        ctr[0U] = (u8)(n1 + (u32)1U);
        if (n1 == (u32)0U)
          Hacl_HMAC_compute_sha2_512(tag, prk, prklen, text0, infolen + (u32)1U);
        else
          Hacl_HMAC_compute_sha2_512(tag, prk, prklen, text, tlen + infolen + (u32)1U);
        {
          u8 *block = okm + n1 * tlen;
          memcpy(block, tag, (len - n1 * tlen) * sizeof (tag[0U]));
        }
      }
    }
  }
}

void Hacl_HKDF_extract_sha2_512(u8 *prk, u8 *salt, u32 saltlen, u8 *ikm, u32 ikmlen)
{
  Hacl_HMAC_compute_sha2_512(prk, salt, saltlen, ikm, ikmlen);
}

