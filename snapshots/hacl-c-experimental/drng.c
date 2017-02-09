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

#include "cpuid.h"
#include "drng.h"

#include <stdio.h>
#include <string.h>
#include <stdint.h>	/* This gives us convenient typedefs */

int get_drng_support ()
{
	static int drng_features= -1;

	/* So we don't call cpuid multiple times for the same information */

	if ( drng_features == -1 ) {
		drng_features= DRNG_NO_SUPPORT;

#ifdef __i386__
		/* Older 32-bit processors may not even have cpuid (and they
		 * will also not have a DRNG). */

		if ( ! _have_cpuid() ) return DRNG_NO_SUPPORT;
#endif

		if ( _is_intel_cpu() ) {
			cpuid_t info;

			cpuid(&info, 1, 0);

			if ( (info.ecx & 0x40000000) == 0x40000000 ) {
				drng_features|= DRNG_HAS_RDRAND;
			}

			cpuid(&info, 7, 0);

			if ( (info.ebx & 0x40000) == 0x40000 ) {
				drng_features|= DRNG_HAS_RDSEED;
			}
		} 
	}

	return drng_features;
}

/*-------------------------------------------------------------
 * RDRAND primitives
 *-------------------------------------------------------------*/

#ifdef HAVE_RDRAND
int rdrand16_step (uint16_t *rand)
{
	unsigned char ok;

	asm volatile ("rdrand %0; setc %1"
		: "=r" (*rand), "=qm" (ok));

	return (int) ok;
}

int rdrand32_step (uint32_t *rand)
{
	unsigned char ok;

	asm volatile ("rdrand %0; setc %1"
		: "=r" (*rand), "=qm" (ok));

	return (int) ok;
}

#  ifdef __x86_64__
int rdrand64_step (uint64_t *rand)
{
	unsigned char ok;

	asm volatile ("rdrand %0; setc %1"
		: "=r" (*rand), "=qm" (ok));

	return (int) ok;
}
#  endif
#else

/* If our compiler is too old, we need to use byte code. */

int rdrand16_step (uint16_t *rand)
{
	unsigned char ok;

	/* rdrand dx */
	asm volatile(".byte 0x0f,0xc7,0xf0; setc %1"
		: "=a" (*rand), "=qm" (ok)
		:
		: "dx"
	);

	return ok;
}

int rdrand32_step (uint32_t *rand)
{
	unsigned char ok;
	
	/* rdrand edx */
	asm volatile(".byte 0x0f,0xc7,0xf0; setc %1"
		: "=a" (*rand), "=qm" (ok)
		:
		: "edx"
	);

	return ok;
}

#  ifdef __x86_64__
int rdrand64_step (uint64_t *rand)
{
	unsigned char ok;
	
	/* rdrand edx */
	asm volatile(".byte 0x48,0x0f,0xc7,0xf0; setc %1"
		: "=a" (*rand), "=qm" (ok)
		:
		: "rdx"
	);

	return ok;
}
#  endif

#endif

/*-------------------------------------------------------------
 * Higher-order RDRAND functions 
 *-------------------------------------------------------------*/

int rdrand16_retry (unsigned int retries, uint16_t *rand)
{
	unsigned int count= 0;

	while ( count <= retries ) {
		if ( rdrand16_step(rand) ) {
			return 1;
		}

		++count;
	}

	return 0;
}

int rdrand32_retry (unsigned int retries, uint32_t *rand)
{
	unsigned int count= 0;

	while ( count <= retries ) {
		if ( rdrand32_step(rand) ) {
			return 1;
		}

		++count;
	}

	return 0;
}

#ifdef __x86_64__

int rdrand64_retry (unsigned int retries, uint64_t *rand)
{
	unsigned int count= 0;

	while ( count <= retries ) {
		if ( rdrand64_step(rand) ) {
			return 1;
		}

		++count;
	}

	return 0;
}

/* Get n 32-bit uints using 64-bit rands */

unsigned int rdrand_get_n_uints (unsigned int n, unsigned int *dest)
{
	unsigned int i;
	uint64_t *qptr= (uint64_t *) dest;
	unsigned int total_uints= 0;
	unsigned int qwords= n/2;

	for (i= 0; i< qwords; ++i, ++qptr) {
		if ( rdrand64_retry(RDRAND_RETRIES, qptr) ) {
			total_uints+= 2;
		} else {
			return total_uints;
		}
	}

	/* Fill the residual */

	if ( n%2 ) {
		unsigned int *uptr= (unsigned int *) qptr;

		if ( rdrand32_step(uptr) ) {
			++total_uints;
		}
	}

	return total_uints;
}

#else

/* Get n 32-bit uints */

unsigned int rdrand_get_n_uints (unsigned int n, unsigned int *dest)
{
	unsigned int i;
	uint32_t *lptr= (uint32_t *) dest;

	for (i= 0; i< n; ++i, ++dest) {
		if ( ! rdrand32_step(dest) ) {
			return i;
		}
	}

	return n;
}
#endif

#ifdef __x86_64__

unsigned int rdrand_get_bytes (unsigned int n, unsigned char *dest)
{
	unsigned char *headstart, *tailstart;
	uint64_t *blockstart;
	unsigned int count, ltail, lhead, lblock;
	uint64_t i, temprand;

	/* Get the address of the first 64-bit aligned block in the
	 * destination buffer. */

	headstart= dest;
	if ( ( (uint64_t)headstart % (uint64_t)8 ) == 0 ) {

		blockstart= (uint64_t *)headstart;
		lblock= n;
		lhead= 0;
	} else {
		blockstart= (uint64_t *) 
			( ((uint64_t)headstart & ~(uint64_t)7) + (uint64_t)8 );

		lblock= n - (8 - (unsigned int) ( (uint64_t)headstart & (uint64_t)8 ));

		lhead= (unsigned int) ( (uint64_t)blockstart - (uint64_t)headstart );
	}

	/* Compute the number of 64-bit blocks and the remaining number
	 * of bytes (the tail) */

	ltail= n-lblock-lhead;
	count= lblock/8;	/* The number 64-bit rands needed */

	if ( ltail ) {
		tailstart= (unsigned char *)( (uint64_t) blockstart + (uint64_t) lblock );
	}

	/* Populate the starting, mis-aligned section (the head) */

	if ( lhead ) {
		if ( ! rdrand64_retry(RDRAND_RETRIES, &temprand) ) {
			return 0;
		}

		memcpy(headstart, &temprand, lhead);
	}

	/* Populate the central, aligned block */

	for (i= 0; i< count; ++i, ++blockstart) {
		if ( ! rdrand64_retry(RDRAND_RETRIES, blockstart) ) {
			return i*8+lhead;
		}
	}

	/* Populate the tail */

	if ( ltail ) {
		if ( ! rdrand64_retry(RDRAND_RETRIES, &temprand) ) {
			return count*8+lhead;
		}

		memcpy(tailstart, &temprand, ltail);
	}

	return n;
}

#else

unsigned int rdrand_get_bytes (unsigned int n, unsigned char *dest)
{
	unsigned char *headstart, *tailstart;
	uint32_t *blockstart;
	unsigned int count, ltail, lhead, lblock;
	uint32_t i, temprand;

	/* Get the address of the first 32-bit aligned block in the
	 * destination buffer. */

	headstart= dest;
	if ( ( (uint32_t)headstart % (uint32_t)4 ) == 0 ) {

		blockstart= (uint32_t *)headstart;
		lblock= n;
		lhead= 0;
	} else {
		blockstart= (uint32_t *) 
			( ((uint32_t)headstart & ~(uint32_t)3) + (uint32_t)4 );

		lblock= n - (8 - (unsigned int) ( (uint32_t)headstart & (uint32_t)4 ));

		lhead= (unsigned int) ( (uint32_t)blockstart - (uint32_t)headstart );
	}

	/* Compute the number of 32-bit blocks and the remaining number
	 * of bytes (the tail) */

	ltail= n-lblock-lhead;
	count= lblock/4;	/* The number 32-bit rands needed */

	if ( ltail ) {
		tailstart= (unsigned char *)( (uint32_t) blockstart + (uint32_t) lblock );
	}

	/* Populate the starting, mis-aligned section (the head) */

	if ( lhead ) {
		if ( ! rdrand32_retry(RDRAND_RETRIES, &temprand) ) {
			return 0;
		}

		memcpy(headstart, &temprand, lhead);
	}

	/* Populate the central, aligned block */

	for (i= 0; i< count; ++i, ++blockstart) {
		if ( ! rdrand32_retry(RDRAND_RETRIES, blockstart) ) {
			return i*4+lhead;
		}
	}

	/* Populate the tail */

	if ( ltail ) {
		if ( ! rdrand32_retry(RDRAND_RETRIES, &temprand) ) {
			return count*4+lhead;
		}

		memcpy(tailstart, &temprand, ltail);
	}

	return n;
}

#endif


/*-------------------------------------------------------------
 * RDSEED primitives 
 *-------------------------------------------------------------*/

#ifdef HAVE_RDSEED
int rdseed16_step (uint16_t *seed)
{
	unsigned char ok;

	asm volatile ("rdseed %0; setc %1"
		: "=r" (*seed), "=qm" (ok));

	return (int) ok;
}

int rdseed32_step (uint32_t *seed)
{
	unsigned char ok;

	asm volatile ("rdseed %0; setc %1"
		: "=r" (*seed), "=qm" (ok));

	return (int) ok;
}

#  ifdef __x86_64__

int rdseed64_step (uint64_t *seed)
{
	unsigned char ok;

	asm volatile ("rdseed %0; setc %1"
		: "=r" (*seed), "=qm" (ok));

	return (int) ok;
}

#  endif
#else

/* If our compiler is too old we have to use byte code */

int rdseed16_step (uint16_t *seed)
{
	unsigned char ok;

	/* rdseed dx */
	asm volatile(".byte 0x0f,0xc7,0xf8; setc %1"
		: "=a" (*seed), "=qm" (ok)
		:
		: "dx"
	);

	return ok;
}

int rdseed32_step (uint32_t *seed)
{
	unsigned char ok;
	
	/* rdseed edx */
	asm volatile(".byte 0x0f,0xc7,0xf8; setc %1"
		: "=a" (*seed), "=qm" (ok)
		:
		: "edx"
	);

	return ok;
}

#  ifdef __x86_64__
int rdseed64_step (uint64_t *seed)
{
	unsigned char ok;
	
	/* rdseed edx */
	asm volatile(".byte 0x48,0x0f,0xc7,0xf8; setc %1"
		: "=a" (*seed), "=qm" (ok)
		:
		: "rdx"
	);

	return ok;
}
#  endif

#endif

