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

#ifndef __Hacl_P256_ECDSA_H
#define __Hacl_P256_ECDSA_H

#include "Hacl_P256.h"


/* SNIPPET_START: Hacl_P256_ECDSA_ecp256dh_i */

uint64_t Hacl_P256_ECDSA_ecp256dh_i(uint8_t *result, uint8_t *scalar);

/* SNIPPET_END: Hacl_P256_ECDSA_ecp256dh_i */

/* SNIPPET_START: Hacl_P256_ECDSA_ecp256dh_r */

/*
  This code is not side channel resistant on pub_key
*/
uint64_t Hacl_P256_ECDSA_ecp256dh_r(uint8_t *result, uint8_t *pubKey, uint8_t *scalar);

/* SNIPPET_END: Hacl_P256_ECDSA_ecp256dh_r */

#define __Hacl_P256_ECDSA_H_DEFINED
#endif
