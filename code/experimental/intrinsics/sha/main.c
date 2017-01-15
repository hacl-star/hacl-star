/*******************************************************************************
* Copyright (c) 2013, Intel Corporation 
* 
* All rights reserved. 
* 
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are
* met: 
* 
* * Redistributions of source code must retain the above copyright
*   notice, this list of conditions and the following disclaimer.  
* 
* * Redistributions in binary form must reproduce the above copyright
*   notice, this list of conditions and the following disclaimer in the
*   documentation and/or other materials provided with the
*   distribution. 
* 
* * Neither the name of the Intel Corporation nor the names of its
*   contributors may be used to endorse or promote products derived from
*   this software without specific prior written permission. 
* 
* 
* THIS SOFTWARE IS PROVIDED BY INTEL CORPORATION ""AS IS"" AND ANY
* EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
* IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
* PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL INTEL CORPORATION OR
* CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
* PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
* PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
********************************************************************************
*
* Provides example usage for the Intel SHA Extensions
* Uses the one-block message known answer vectors provided in Appendixes A 
* and B of the FIPS 180-2 Secure Hash Standard from NIST
* http://csrc.nist.gov/publications/fips/fips180-2/fips180-2.pdf 
* 
********************************************************************************
* Author: Sean Gulley <sean.m.gulley@intel.com>
* Date:   July 2013
*******************************************************************************/

#include <stdint.h>
#include <stdio.h>

/* sha*_update function can be a linked in intrinsic or asm function */
extern void   sha1_update(uint32_t *digest, const void *data, 
                          uint32_t  numBlocks);
extern void sha256_update(uint32_t *digest, const void *data, 
                          uint32_t  numBlocks);

const uint32_t shaShortMsgKAV[16] = {
   0x80636261, 0x00000000, 0x00000000, 0x00000000,
   0x00000000, 0x00000000, 0x00000000, 0x00000000,
   0x00000000, 0x00000000, 0x00000000, 0x00000000,
   0x00000000, 0x00000000, 0x00000000, 0x18000000
};

/* Initial hash and final digest values */ 
const uint32_t sha1InitialDigest[5] = {
   0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0
};

const uint32_t sha1ShortMsgDigestKAV[5] = {
   0xa9993e36, 0x4706816a, 0xba3e2571, 0x7850c26c, 0x9cd0d89d
};

const uint32_t sha256InitialDigest[8] = {
   0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
   0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
};

const uint32_t sha256ShortMsgDigestKAV[8] = {
   0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223,
   0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad
};

/* Check the CPUID bit for the availability of the Intel SHA Extensions */
int check_for_intel_sha_extensions() {
   int a, b, c, d;

   /* Look for CPUID.7.0.EBX[29] 
    * EAX = 7, ECX = 0 */
   a = 7;
   c = 0;

   asm volatile ("cpuid"
                 :"=a"(a), "=b"(b), "=c"(c), "=d"(d)
                 :"a"(a), "c"(c)
                );

   /* SHA feature bit is EBX[29] */
   return ((b >> 29) & 1);
}

int test_sha(const uint32_t  digestSize, const uint32_t *initialDigest,
             const uint32_t *finalDigest, 
             void (*update)(uint32_t*, const void*, uint32_t)) {
   uint32_t digest[8] __attribute__((aligned (16)));
   uint32_t i;
   int result = 0;

   /* Initialize hash values */
   for (i=0; i<digestSize; i++) {
      digest[i] = initialDigest[i];
   }

   /* Process one-block message */ 
   (*update)(digest, shaShortMsgKAV, 1);

   /* Check final digest values against known answer */ 
   for (i=0; i<digestSize; i++) {
      if (finalDigest[i] != digest[i]) {
         printf("ERR %08X != %08X\n", digest[i], finalDigest[i]);
         result++;
      }
   }

   return result;
}

int main() {
   int sha1Result;
   int sha256Result;

   if (0 == check_for_intel_sha_extensions()) {
      printf("Intel SHA Extensions are not enabled on this processor\n");
      return 1;
   }

   printf("Testing Intel SHA Extensions\n");

   sha1Result = test_sha(5, sha1InitialDigest, 
                         sha1ShortMsgDigestKAV, sha1_update); 

   printf("SHA-1 Test %s\n", (0 == sha1Result) ? "PASS" : "FAIL");

   sha256Result = test_sha(8, sha256InitialDigest, 
                           sha256ShortMsgDigestKAV, sha256_update); 

   printf("SHA-256 Test %s\n", (0 == sha256Result) ? "PASS" : "FAIL");


   return (sha1Result + sha256Result) ;
}

