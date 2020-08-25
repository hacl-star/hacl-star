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


#include "Hacl_NaCl.h"

static void secretbox_init(u8 *xkeys, u8 *k, u8 *n)
{
  u8 *subkey = xkeys;
  u8 *aekey = xkeys + (u32)32U;
  u8 *n0 = n;
  u8 *n1 = n + (u32)16U;
  Hacl_Salsa20_hsalsa20(subkey, k, n0);
  Hacl_Salsa20_salsa20_key_block0(aekey, subkey, n1);
}

static void secretbox_detached(u32 mlen, u8 *c, u8 *tag, u8 *k, u8 *n, u8 *m)
{
  u8 xkeys[96U] = { 0U };
  u8 *mkey;
  secretbox_init(xkeys, k, n);
  mkey = xkeys + (u32)32U;
  {
    u8 *n1 = n + (u32)16U;
    u8 *subkey = xkeys;
    u8 *ekey0 = xkeys + (u32)64U;
    u32 mlen0;
    if (mlen <= (u32)32U)
      mlen0 = mlen;
    else
      mlen0 = (u32)32U;
    {
      u32 mlen1 = mlen - mlen0;
      u8 *m0 = m;
      u8 *m1 = m + mlen0;
      u8 block0[32U] = { 0U };
      u8 *c0;
      u8 *c1;
      memcpy(block0, m0, mlen0 * sizeof (u8));
      {
        u32 i;
        for (i = (u32)0U; i < (u32)32U; i++)
        {
          u8 *os = block0;
          u8 x = block0[i] ^ ekey0[i];
          os[i] = x;
        }
      }
      c0 = c;
      c1 = c + mlen0;
      memcpy(c0, block0, mlen0 * sizeof (u8));
      Hacl_Salsa20_salsa20_encrypt(mlen1, c1, m1, subkey, n1, (u32)1U);
      Hacl_Poly1305_32_poly1305_mac(tag, mlen, c, mkey);
    }
  }
}

static u32 secretbox_open_detached(u32 mlen, u8 *m, u8 *k, u8 *n, u8 *c, u8 *tag)
{
  u8 xkeys[96U] = { 0U };
  u8 *mkey;
  secretbox_init(xkeys, k, n);
  mkey = xkeys + (u32)32U;
  {
    u8 tag_[16U] = { 0U };
    Hacl_Poly1305_32_poly1305_mac(tag_, mlen, c, mkey);
    {
      u8 res0 = (u8)255U;
      u8 z;
      u32 res;
      {
        u32 i;
        for (i = (u32)0U; i < (u32)16U; i++)
        {
          u8 uu____0 = FStar_UInt8_eq_mask(tag[i], tag_[i]);
          res0 = uu____0 & res0;
        }
      }
      z = res0;
      if (z == (u8)255U)
      {
        u8 *subkey = xkeys;
        u8 *ekey0 = xkeys + (u32)64U;
        u8 *n1 = n + (u32)16U;
        u32 mlen0;
        if (mlen <= (u32)32U)
          mlen0 = mlen;
        else
          mlen0 = (u32)32U;
        {
          u32 mlen1 = mlen - mlen0;
          u8 *c0 = c;
          u8 *c1 = c + mlen0;
          u8 block0[32U] = { 0U };
          memcpy(block0, c0, mlen0 * sizeof (u8));
          {
            u32 i;
            for (i = (u32)0U; i < (u32)32U; i++)
            {
              u8 *os = block0;
              u8 x = block0[i] ^ ekey0[i];
              os[i] = x;
            }
          }
          {
            u8 *m0 = m;
            u8 *m1 = m + mlen0;
            memcpy(m0, block0, mlen0 * sizeof (u8));
            Hacl_Salsa20_salsa20_decrypt(mlen1, m1, c1, subkey, n1, (u32)1U);
            res = (u32)0U;
          }
        }
      }
      else
        res = (u32)0xffffffffU;
      return res;
    }
  }
}

static void secretbox_easy(u32 mlen, u8 *c, u8 *k, u8 *n, u8 *m)
{
  u8 *tag = c;
  u8 *cip = c + (u32)16U;
  secretbox_detached(mlen, cip, tag, k, n, m);
}

static u32 secretbox_open_easy(u32 mlen, u8 *m, u8 *k, u8 *n, u8 *c)
{
  u8 *tag = c;
  u8 *cip = c + (u32)16U;
  return secretbox_open_detached(mlen, m, k, n, cip, tag);
}

static inline u32 box_beforenm(u8 *k, u8 *pk, u8 *sk)
{
  u8 n0[16U] = { 0U };
  bool r = Hacl_Curve25519_51_ecdh(k, sk, pk);
  if (r)
  {
    Hacl_Salsa20_hsalsa20(k, k, n0);
    return (u32)0U;
  }
  return (u32)0xffffffffU;
}

static inline u32 box_detached_afternm(u32 mlen, u8 *c, u8 *tag, u8 *k, u8 *n, u8 *m)
{
  secretbox_detached(mlen, c, tag, k, n, m);
  return (u32)0U;
}

static inline u32 box_detached(u32 mlen, u8 *c, u8 *tag, u8 *sk, u8 *pk, u8 *n, u8 *m)
{
  u8 k[32U] = { 0U };
  u32 r = box_beforenm(k, pk, sk);
  if (r == (u32)0U)
    return box_detached_afternm(mlen, c, tag, k, n, m);
  return (u32)0xffffffffU;
}

static inline u32 box_open_detached_afternm(u32 mlen, u8 *m, u8 *k, u8 *n, u8 *c, u8 *tag)
{
  return secretbox_open_detached(mlen, m, k, n, c, tag);
}

static inline u32 box_open_detached(u32 mlen, u8 *m, u8 *pk, u8 *sk, u8 *n, u8 *c, u8 *tag)
{
  u8 k[32U] = { 0U };
  u32 r = box_beforenm(k, pk, sk);
  if (r == (u32)0U)
    return box_open_detached_afternm(mlen, m, k, n, c, tag);
  return (u32)0xffffffffU;
}

static inline u32 box_easy_afternm(u32 mlen, u8 *c, u8 *k, u8 *n, u8 *m)
{
  u8 *tag = c;
  u8 *cip = c + (u32)16U;
  u32 res = box_detached_afternm(mlen, cip, tag, k, n, m);
  return res;
}

static inline u32 box_easy(u32 mlen, u8 *c, u8 *sk, u8 *pk, u8 *n, u8 *m)
{
  u8 *tag = c;
  u8 *cip = c + (u32)16U;
  u32 res = box_detached(mlen, cip, tag, sk, pk, n, m);
  return res;
}

static inline u32 box_open_easy_afternm(u32 mlen, u8 *m, u8 *k, u8 *n, u8 *c)
{
  u8 *tag = c;
  u8 *cip = c + (u32)16U;
  return box_open_detached_afternm(mlen, m, k, n, cip, tag);
}

static inline u32 box_open_easy(u32 mlen, u8 *m, u8 *pk, u8 *sk, u8 *n, u8 *c)
{
  u8 *tag = c;
  u8 *cip = c + (u32)16U;
  return box_open_detached(mlen, m, pk, sk, n, cip, tag);
}

u32 Hacl_NaCl_crypto_secretbox_detached(u8 *c, u8 *tag, u8 *m, u32 mlen, u8 *n, u8 *k)
{
  secretbox_detached(mlen, c, tag, k, n, m);
  return (u32)0U;
}

u32 Hacl_NaCl_crypto_secretbox_open_detached(u8 *m, u8 *c, u8 *tag, u32 mlen, u8 *n, u8 *k)
{
  return secretbox_open_detached(mlen, m, k, n, c, tag);
}

u32 Hacl_NaCl_crypto_secretbox_easy(u8 *c, u8 *m, u32 mlen, u8 *n, u8 *k)
{
  secretbox_easy(mlen, c, k, n, m);
  return (u32)0U;
}

u32 Hacl_NaCl_crypto_secretbox_open_easy(u8 *m, u8 *c, u32 clen, u8 *n, u8 *k)
{
  return secretbox_open_easy(clen - (u32)16U, m, k, n, c);
}

u32 Hacl_NaCl_crypto_box_beforenm(u8 *k, u8 *pk, u8 *sk)
{
  return box_beforenm(k, pk, sk);
}

u32 Hacl_NaCl_crypto_box_detached_afternm(u8 *c, u8 *tag, u8 *m, u32 mlen, u8 *n, u8 *k)
{
  return box_detached_afternm(mlen, c, tag, k, n, m);
}

u32 Hacl_NaCl_crypto_box_detached(u8 *c, u8 *tag, u8 *m, u32 mlen, u8 *n, u8 *pk, u8 *sk)
{
  return box_detached(mlen, c, tag, sk, pk, n, m);
}

u32 Hacl_NaCl_crypto_box_open_detached_afternm(u8 *m, u8 *c, u8 *tag, u32 mlen, u8 *n, u8 *k)
{
  return box_open_detached_afternm(mlen, m, k, n, c, tag);
}

u32 Hacl_NaCl_crypto_box_open_detached(u8 *m, u8 *c, u8 *tag, u32 mlen, u8 *n, u8 *pk, u8 *sk)
{
  return box_open_detached(mlen, m, pk, sk, n, c, tag);
}

u32 Hacl_NaCl_crypto_box_easy_afternm(u8 *c, u8 *m, u32 mlen, u8 *n, u8 *k)
{
  return box_easy_afternm(mlen, c, k, n, m);
}

u32 Hacl_NaCl_crypto_box_easy(u8 *c, u8 *m, u32 mlen, u8 *n, u8 *pk, u8 *sk)
{
  return box_easy(mlen, c, sk, pk, n, m);
}

u32 Hacl_NaCl_crypto_box_open_easy_afternm(u8 *m, u8 *c, u32 clen, u8 *n, u8 *k)
{
  return box_open_easy_afternm(clen - (u32)16U, m, k, n, c);
}

u32 Hacl_NaCl_crypto_box_open_easy(u8 *m, u8 *c, u32 clen, u8 *n, u8 *pk, u8 *sk)
{
  return box_open_easy(clen - (u32)16U, m, pk, sk, n, c);
}

