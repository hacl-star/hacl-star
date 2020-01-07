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


#include "EverCrypt_Ed25519.h"

void EverCrypt_Ed25519_sign(u8 *signature, u8 *secret1, u32 len, u8 *msg)
{
  Hacl_Ed25519_sign(signature, secret1, len, msg);
}

bool EverCrypt_Ed25519_verify(u8 *output, u32 len, u8 *msg, u8 *signature)
{
  return Hacl_Ed25519_verify(output, len, msg, signature);
}

void EverCrypt_Ed25519_secret_to_public(u8 *output, u8 *secret1)
{
  Hacl_Ed25519_secret_to_public(output, secret1);
}

void EverCrypt_Ed25519_expand_keys(u8 *ks, u8 *secret1)
{
  Hacl_Ed25519_expand_keys(ks, secret1);
}

void EverCrypt_Ed25519_sign_expanded(u8 *signature, u8 *ks, u32 len, u8 *msg)
{
  Hacl_Ed25519_sign_expanded(signature, ks, len, msg);
}

