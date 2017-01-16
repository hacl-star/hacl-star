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
#include <string.h>
#include <stdint.h>

int _is_intel_cpu ()
{
	static int intel_cpu= -1;
	cpuid_t info;

	/* So we don't call cpuid multiple times for the same information */

	if ( intel_cpu == -1 ) {
		cpuid(&info, 0, 0);

		if (
			memcmp((char *) &info.ebx, "Genu", 4) ||
			memcmp((char *) &info.edx, "ineI", 4) ||
			memcmp((char *) &info.ecx, "ntel", 4)
		) {
			intel_cpu= 0;
		} else {
			intel_cpu= 1;
		}
	}

	return intel_cpu;
}

#ifdef __i386__
int _have_cpuid ()
{
	/*
	 * cpuid availability is determined by setting and clearing the 
	 * ID flag (bit 21) in the EFLAGS register. If we can do that, we
	 * have cpuid. This is only necessary on 32-bit processors.
	 */

	uint32_t fbefore, fafter;

	asm(" 					;\
		pushf				;\
		pushf				;\
		pop %0				;\
		mov %0,%1			;\
		xor $0x40000,%1		;\
		push %1				;\
		popf				;\
		pushf				;\
		pop %1				;\
		popf				"
	: "=&r" (fbefore), "=&r" (fafter)
	);

	return (0x40000 & (fbefore^fafter));
}
#endif

void cpuid (cpuid_t *info, unsigned int leaf, unsigned int subleaf)
{
#ifdef __i386__
	/* Can't use %ebx when compiling with -fPIC (or -fPIE) */

	asm volatile("	 	;\
		mov %%ebx,%0 	;\
		cpuid 			;\
		xchgl %%ebx,%0	"
	:	"=r" (info->ebx), "=a" (info->eax), "=c" (info->ecx), "=d" (info->edx)
	:	"a" (leaf), "c" (subleaf)
	);

#else

	asm volatile("cpuid"
	: "=a" (info->eax), "=b" (info->ebx), "=c" (info->ecx), "=d" (info->edx)
	: "a" (leaf), "c" (subleaf)
	);

#endif
}

