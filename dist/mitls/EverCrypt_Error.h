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


#ifndef __EverCrypt_Error_H
#define __EverCrypt_Error_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "evercrypt_targetconfig.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"




#define EverCrypt_Error_Success 0
#define EverCrypt_Error_UnsupportedAlgorithm 1
#define EverCrypt_Error_InvalidKey 2
#define EverCrypt_Error_AuthenticationFailure 3
#define EverCrypt_Error_InvalidIVLength 4
#define EverCrypt_Error_DecodeError 5

typedef uint8_t EverCrypt_Error_error_code;

bool EverCrypt_Error_uu___is_Success(EverCrypt_Error_error_code projectee);

bool EverCrypt_Error_uu___is_UnsupportedAlgorithm(EverCrypt_Error_error_code projectee);

bool EverCrypt_Error_uu___is_InvalidKey(EverCrypt_Error_error_code projectee);

bool EverCrypt_Error_uu___is_AuthenticationFailure(EverCrypt_Error_error_code projectee);

bool EverCrypt_Error_uu___is_InvalidIVLength(EverCrypt_Error_error_code projectee);

bool EverCrypt_Error_uu___is_DecodeError(EverCrypt_Error_error_code projectee);

#if defined(__cplusplus)
}
#endif

#define __EverCrypt_Error_H_DEFINED
#endif
