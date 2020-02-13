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

#include "evercrypt_targetconfig.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"

#ifndef __MerkleTree_New_Low_Hashfunctions_H
#define __MerkleTree_New_Low_Hashfunctions_H

#include "Hacl_Spec.h"
#include "EverCrypt_Hash.h"
#include "MerkleTree_New_Low_Datastructures.h"


uint8_t
*LowStar_Regional_rg_alloc___uint8_t__uint32_t(
  LowStar_Regional_regional__uint32_t__uint8_t_ rg
);

uint8_t *MerkleTree_New_Low_Hashfunctions_init_hash(uint32_t hsz);

void MerkleTree_New_Low_Hashfunctions_free_hash(uint32_t hsz, uint8_t *h1);

void
MerkleTree_New_Low_Hashfunctions_sha256_compress(uint8_t *src1, uint8_t *src2, uint8_t *dst);

#define __MerkleTree_New_Low_Hashfunctions_H_DEFINED
#endif
