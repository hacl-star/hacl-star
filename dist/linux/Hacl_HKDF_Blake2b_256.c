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


#include "Hacl_HKDF_Blake2b_256.h"

void
Hacl_HKDF_Blake2b_256_expand_blake2b_256(
  u8 *okm,
  u8 *prk,
  u32 prklen,
  u8 *info,
  u32 infolen,
  u32 len
)
{
  u32 tlen = (u32)64U;
  u32 n = len / tlen;
  u8 *output = okm;
  KRML_CHECK_SIZE(sizeof (u8), tlen + infolen + (u32)1U);
  {
    u8 text[tlen + infolen + (u32)1U];
    memset(text, 0U, (tlen + infolen + (u32)1U) * sizeof (u8));
    {
      u8 *text0 = text + tlen;
      u8 *tag = text;
      u8 *ctr = text + tlen + infolen;
      memcpy(text + tlen, info, infolen * sizeof (u8));
      {
        u32 i;
        for (i = (u32)0U; i < n; i++)
        {
          ctr[0U] = (u8)(i + (u32)1U);
          if (i == (u32)0U)
            Hacl_HMAC_Blake2b_256_compute_blake2b_256(tag, prk, prklen, text0, infolen + (u32)1U);
          else
            Hacl_HMAC_Blake2b_256_compute_blake2b_256(tag,
              prk,
              prklen,
              text,
              tlen + infolen + (u32)1U);
          memcpy(output + i * tlen, tag, tlen * sizeof (u8));
        }
      }
      if (n * tlen < len)
      {
        ctr[0U] = (u8)(n + (u32)1U);
        if (n == (u32)0U)
          Hacl_HMAC_Blake2b_256_compute_blake2b_256(tag, prk, prklen, text0, infolen + (u32)1U);
        else
          Hacl_HMAC_Blake2b_256_compute_blake2b_256(tag,
            prk,
            prklen,
            text,
            tlen + infolen + (u32)1U);
        {
          u8 *block = okm + n * tlen;
          memcpy(block, tag, (len - n * tlen) * sizeof (u8));
        }
      }
    }
  }
}

void
Hacl_HKDF_Blake2b_256_extract_blake2b_256(u8 *prk, u8 *salt, u32 saltlen, u8 *ikm, u32 ikmlen)
{
  Hacl_HMAC_Blake2b_256_compute_blake2b_256(prk, salt, saltlen, ikm, ikmlen);
}

