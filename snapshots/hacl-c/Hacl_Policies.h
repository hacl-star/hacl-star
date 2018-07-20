/* MIT License
 *
 * Copyright (c) 2016-2018 INRIA and Microsoft Corporation
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



#ifndef __Hacl_Policies_H
#define __Hacl_Policies_H


#include "kremlib.h"

extern FStar_UInt128_uint128 FStar_Int_Cast_Full_uint64_to_uint128(uint64_t x0);

uint8_t Hacl_Policies_declassify_u8(uint8_t x);

uint32_t Hacl_Policies_declassify_u32(uint32_t x);

uint64_t Hacl_Policies_declassify_u64(uint64_t x);

FStar_UInt128_uint128 Hacl_Policies_declassify_u128(FStar_UInt128_uint128 x);

uint8_t Hacl_Policies_cmp_bytes_(uint8_t *b1, uint8_t *b2, uint32_t len, uint8_t *tmp);

uint8_t Hacl_Policies_cmp_bytes(uint8_t *b1, uint8_t *b2, uint32_t len);

#define __Hacl_Policies_H_DEFINED
#endif
