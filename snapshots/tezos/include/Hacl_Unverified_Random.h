/* MIT License
 *
 * Copyright (c) 2016-2017 INRIA and Microsoft Corporation
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
#ifndef __HACL_UNVERIFIED_RANDOM
#define __HACL_UNVERIFIED_RANDOM

#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>

#if ((defined(_WIN32) || defined(_WIN64)) && (! (defined(__CYGWIN__))))
#define HACL_IS_WINDOWS 1
#else
#define HACL_IS_WINDOWS 0
#endif

bool read_random_bytes(uint64_t len, uint8_t * buf);
void * hacl_aligned_malloc(size_t alignment, size_t size);
void hacl_aligned_free(void * ptr);

void randombytes(uint8_t * x,uint64_t len);

#endif // __HACL_UNVERIFIED_RANDOM

