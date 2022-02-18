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

#include "internal/Hacl_Kremlib.h"

static void secretbox_init(uint8_t *xkeys, uint8_t *k, uint8_t *n)
{
  uint8_t *subkey = xkeys;
  uint8_t *aekey = xkeys + (uint32_t)32U;
  uint8_t *n0 = n;
  uint8_t *n1 = n + (uint32_t)16U;
  Hacl_Salsa20_hsalsa20(subkey, k, n0);
  Hacl_Salsa20_salsa20_key_block0(aekey, subkey, n1);
}

static void
secretbox_detached(uint32_t mlen, uint8_t *c, uint8_t *tag, uint8_t *k, uint8_t *n, uint8_t *m)
{
  uint8_t xkeys[96U] = { 0U };
  secretbox_init(xkeys, k, n);
  uint8_t *mkey = xkeys + (uint32_t)32U;
  uint8_t *n1 = n + (uint32_t)16U;
  uint8_t *subkey = xkeys;
  uint8_t *ekey0 = xkeys + (uint32_t)64U;
  uint32_t mlen0;
  if (mlen <= (uint32_t)32U)
  {
    mlen0 = mlen;
  }
  else
  {
    mlen0 = (uint32_t)32U;
  }
  uint32_t mlen1 = mlen - mlen0;
  uint8_t *m0 = m;
  uint8_t *m1 = m + mlen0;
  uint8_t block0[32U] = { 0U };
  memcpy(block0, m0, mlen0 * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)32U; i++)
  {
    uint8_t *os = block0;
    uint8_t x = block0[i] ^ ekey0[i];
    os[i] = x;
  }
  uint8_t *c0 = c;
  uint8_t *c1 = c + mlen0;
  memcpy(c0, block0, mlen0 * sizeof (uint8_t));
  Hacl_Salsa20_salsa20_encrypt(mlen1, c1, m1, subkey, n1, (uint32_t)1U);
  Hacl_Poly1305_32_poly1305_mac(tag, mlen, c, mkey);
}

static uint32_t
secretbox_open_detached(
  uint32_t mlen,
  uint8_t *m,
  uint8_t *k,
  uint8_t *n,
  uint8_t *c,
  uint8_t *tag
)
{
  uint8_t xkeys[96U] = { 0U };
  secretbox_init(xkeys, k, n);
  uint8_t *mkey = xkeys + (uint32_t)32U;
  uint8_t tag_[16U] = { 0U };
  Hacl_Poly1305_32_poly1305_mac(tag_, mlen, c, mkey);
  uint8_t res = (uint8_t)255U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint8_t uu____0 = FStar_UInt8_eq_mask(tag[i], tag_[i]);
    res = uu____0 & res;
  }
  uint8_t z = res;
  if (z == (uint8_t)255U)
  {
    uint8_t *subkey = xkeys;
    uint8_t *ekey0 = xkeys + (uint32_t)64U;
    uint8_t *n1 = n + (uint32_t)16U;
    uint32_t mlen0;
    if (mlen <= (uint32_t)32U)
    {
      mlen0 = mlen;
    }
    else
    {
      mlen0 = (uint32_t)32U;
    }
    uint32_t mlen1 = mlen - mlen0;
    uint8_t *c0 = c;
    uint8_t *c1 = c + mlen0;
    uint8_t block0[32U] = { 0U };
    memcpy(block0, c0, mlen0 * sizeof (uint8_t));
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)32U; i++)
    {
      uint8_t *os = block0;
      uint8_t x = block0[i] ^ ekey0[i];
      os[i] = x;
    }
    uint8_t *m0 = m;
    uint8_t *m1 = m + mlen0;
    memcpy(m0, block0, mlen0 * sizeof (uint8_t));
    Hacl_Salsa20_salsa20_decrypt(mlen1, m1, c1, subkey, n1, (uint32_t)1U);
    return (uint32_t)0U;
  }
  return (uint32_t)0xffffffffU;
}

static void secretbox_easy(uint32_t mlen, uint8_t *c, uint8_t *k, uint8_t *n, uint8_t *m)
{
  uint8_t *tag = c;
  uint8_t *cip = c + (uint32_t)16U;
  secretbox_detached(mlen, cip, tag, k, n, m);
}

static uint32_t
secretbox_open_easy(uint32_t mlen, uint8_t *m, uint8_t *k, uint8_t *n, uint8_t *c)
{
  uint8_t *tag = c;
  uint8_t *cip = c + (uint32_t)16U;
  return secretbox_open_detached(mlen, m, k, n, cip, tag);
}

static inline uint32_t box_beforenm(uint8_t *k, uint8_t *pk, uint8_t *sk)
{
  uint8_t n0[16U] = { 0U };
  bool r = Hacl_Curve25519_51_ecdh(k, sk, pk);
  if (r)
  {
    Hacl_Salsa20_hsalsa20(k, k, n0);
    return (uint32_t)0U;
  }
  return (uint32_t)0xffffffffU;
}

static inline uint32_t
box_detached_afternm(
  uint32_t mlen,
  uint8_t *c,
  uint8_t *tag,
  uint8_t *k,
  uint8_t *n,
  uint8_t *m
)
{
  secretbox_detached(mlen, c, tag, k, n, m);
  return (uint32_t)0U;
}

static inline uint32_t
box_detached(
  uint32_t mlen,
  uint8_t *c,
  uint8_t *tag,
  uint8_t *sk,
  uint8_t *pk,
  uint8_t *n,
  uint8_t *m
)
{
  uint8_t k[32U] = { 0U };
  uint32_t r = box_beforenm(k, pk, sk);
  if (r == (uint32_t)0U)
  {
    return box_detached_afternm(mlen, c, tag, k, n, m);
  }
  return (uint32_t)0xffffffffU;
}

static inline uint32_t
box_open_detached_afternm(
  uint32_t mlen,
  uint8_t *m,
  uint8_t *k,
  uint8_t *n,
  uint8_t *c,
  uint8_t *tag
)
{
  return secretbox_open_detached(mlen, m, k, n, c, tag);
}

static inline uint32_t
box_open_detached(
  uint32_t mlen,
  uint8_t *m,
  uint8_t *pk,
  uint8_t *sk,
  uint8_t *n,
  uint8_t *c,
  uint8_t *tag
)
{
  uint8_t k[32U] = { 0U };
  uint32_t r = box_beforenm(k, pk, sk);
  if (r == (uint32_t)0U)
  {
    return box_open_detached_afternm(mlen, m, k, n, c, tag);
  }
  return (uint32_t)0xffffffffU;
}

static inline uint32_t
box_easy_afternm(uint32_t mlen, uint8_t *c, uint8_t *k, uint8_t *n, uint8_t *m)
{
  uint8_t *tag = c;
  uint8_t *cip = c + (uint32_t)16U;
  uint32_t res = box_detached_afternm(mlen, cip, tag, k, n, m);
  return res;
}

static inline uint32_t
box_easy(uint32_t mlen, uint8_t *c, uint8_t *sk, uint8_t *pk, uint8_t *n, uint8_t *m)
{
  uint8_t *tag = c;
  uint8_t *cip = c + (uint32_t)16U;
  uint32_t res = box_detached(mlen, cip, tag, sk, pk, n, m);
  return res;
}

static inline uint32_t
box_open_easy_afternm(uint32_t mlen, uint8_t *m, uint8_t *k, uint8_t *n, uint8_t *c)
{
  uint8_t *tag = c;
  uint8_t *cip = c + (uint32_t)16U;
  return box_open_detached_afternm(mlen, m, k, n, cip, tag);
}

static inline uint32_t
box_open_easy(uint32_t mlen, uint8_t *m, uint8_t *pk, uint8_t *sk, uint8_t *n, uint8_t *c)
{
  uint8_t *tag = c;
  uint8_t *cip = c + (uint32_t)16U;
  return box_open_detached(mlen, m, pk, sk, n, cip, tag);
}

uint32_t
Hacl_NaCl_crypto_secretbox_detached(
  uint8_t *c,
  uint8_t *tag,
  uint8_t *m,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *k
)
{
  secretbox_detached(mlen, c, tag, k, n, m);
  return (uint32_t)0U;
}

uint32_t
Hacl_NaCl_crypto_secretbox_open_detached(
  uint8_t *m,
  uint8_t *c,
  uint8_t *tag,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *k
)
{
  return secretbox_open_detached(mlen, m, k, n, c, tag);
}

uint32_t
Hacl_NaCl_crypto_secretbox_easy(uint8_t *c, uint8_t *m, uint32_t mlen, uint8_t *n, uint8_t *k)
{
  secretbox_easy(mlen, c, k, n, m);
  return (uint32_t)0U;
}

uint32_t
Hacl_NaCl_crypto_secretbox_open_easy(
  uint8_t *m,
  uint8_t *c,
  uint32_t clen,
  uint8_t *n,
  uint8_t *k
)
{
  return secretbox_open_easy(clen - (uint32_t)16U, m, k, n, c);
}

uint32_t Hacl_NaCl_crypto_box_beforenm(uint8_t *k, uint8_t *pk, uint8_t *sk)
{
  return box_beforenm(k, pk, sk);
}

uint32_t
Hacl_NaCl_crypto_box_detached_afternm(
  uint8_t *c,
  uint8_t *tag,
  uint8_t *m,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *k
)
{
  return box_detached_afternm(mlen, c, tag, k, n, m);
}

uint32_t
Hacl_NaCl_crypto_box_detached(
  uint8_t *c,
  uint8_t *tag,
  uint8_t *m,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *pk,
  uint8_t *sk
)
{
  return box_detached(mlen, c, tag, sk, pk, n, m);
}

uint32_t
Hacl_NaCl_crypto_box_open_detached_afternm(
  uint8_t *m,
  uint8_t *c,
  uint8_t *tag,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *k
)
{
  return box_open_detached_afternm(mlen, m, k, n, c, tag);
}

uint32_t
Hacl_NaCl_crypto_box_open_detached(
  uint8_t *m,
  uint8_t *c,
  uint8_t *tag,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *pk,
  uint8_t *sk
)
{
  return box_open_detached(mlen, m, pk, sk, n, c, tag);
}

uint32_t
Hacl_NaCl_crypto_box_easy_afternm(
  uint8_t *c,
  uint8_t *m,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *k
)
{
  return box_easy_afternm(mlen, c, k, n, m);
}

uint32_t
Hacl_NaCl_crypto_box_easy(
  uint8_t *c,
  uint8_t *m,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *pk,
  uint8_t *sk
)
{
  return box_easy(mlen, c, sk, pk, n, m);
}

uint32_t
Hacl_NaCl_crypto_box_open_easy_afternm(
  uint8_t *m,
  uint8_t *c,
  uint32_t clen,
  uint8_t *n,
  uint8_t *k
)
{
  return box_open_easy_afternm(clen - (uint32_t)16U, m, k, n, c);
}

uint32_t
Hacl_NaCl_crypto_box_open_easy(
  uint8_t *m,
  uint8_t *c,
  uint32_t clen,
  uint8_t *n,
  uint8_t *pk,
  uint8_t *sk
)
{
  return box_open_easy(clen - (uint32_t)16U, m, pk, sk, n, c);
}

