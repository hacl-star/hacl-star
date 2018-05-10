/*

Copyright (c) 2014, Intel Corporation
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions
are met:

    * Redistributions of source code must retain the above copyright 
      notice, this list of conditions and the following disclaimer.  

    * Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.

    * Neither the name of Intel Corporation nor the names of its
      contributors may be used to endorse or promote products derived from
      this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED
TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*/

#ifndef __DRNG__H
#define __DRNG__H

#include <stdint.h> /* Gets us convenient typedefs */

/*
 * These are bits that are OR'd together. A value of -1 indicates support
 * has not been checked yet.
 */

#define DRNG_NO_SUPPORT	0x0		/* A convenience symbol */
#define DRNG_HAS_RDRAND	0x1
#define DRNG_HAS_RDSEED	0x2

int get_drng_support (void);

/*
 * The recommended number of RDRAND retries is 10. This number is not
 * arbitrary, but rather based on a binomial probability argument
 * and represents a guarantee of sorts by the DRNG designers. The odds
 * of 10 failures in a row are astronomically small.
 */

#define RDRAND_RETRIES 10

/* RDRAND primitives */

int rdrand16_step (uint16_t *rand);
int rdrand32_step (uint32_t *rand);
#ifdef __x86_64__
int rdrand64_step (uint64_t *rand);
#endif

/* Higher level RDRAND funcs */

int rdrand16_retry (unsigned int retries, uint16_t *rand);
int rdrand32_retry (unsigned int retries, uint32_t *rand);
#ifdef __x86_64__
int rdrand64_retry (unsigned int retries, uint64_t *rand);
#endif

unsigned int rdrand_get_n_uints (unsigned int n, uint32_t *dest);

#ifdef __x86_64__
unsigned int rdrand_get_bytes (unsigned int n, unsigned char *dest);
#endif

/* RDSEED primitives */

int rdseed16_step (uint16_t *seed);
int rdseed32_step (uint32_t *seed);
#ifdef __x86_64__
int rdseed64_step (uint64_t *seed);
#endif

#endif

