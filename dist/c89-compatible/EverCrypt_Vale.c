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


#include "EverCrypt_Vale.h"

uint8_t *__proj__Mkgcm_args__item__plain(gcm_args projectee)
{
  return projectee.plain;
}

uint64_t __proj__Mkgcm_args__item__plain_len(gcm_args projectee)
{
  return projectee.plain_len;
}

uint8_t *__proj__Mkgcm_args__item__aad(gcm_args projectee)
{
  return projectee.aad;
}

uint64_t __proj__Mkgcm_args__item__aad_len(gcm_args projectee)
{
  return projectee.aad_len;
}

uint8_t *__proj__Mkgcm_args__item__iv(gcm_args projectee)
{
  return projectee.iv;
}

uint8_t *__proj__Mkgcm_args__item__expanded_key(gcm_args projectee)
{
  return projectee.expanded_key;
}

uint8_t *__proj__Mkgcm_args__item__cipher(gcm_args projectee)
{
  return projectee.cipher;
}

uint8_t *__proj__Mkgcm_args__item__tag(gcm_args projectee)
{
  return projectee.tag;
}

