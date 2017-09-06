/*
// SHA-256 a.k.a. SHA-2; computation over whole blocks only.
// Wrapper around Intel SHA-512 ASM implementation
//
// Written by Romain Dolbeau (romain@dolbeau.org)
//
// This is free and unencumbered software released into the public domain.
//
// Anyone is free to copy, modify, publish, use, compile, sell, or
// distribute this software, either in source code form or as a compiled
// binary, for any purpose, commercial or non-commercial, and by any
// means.
//
// In jurisdictions that recognize copyright laws, the author or authors
// of this software dedicate any and all copyright interest in the
// software to the public domain. We make this dedication for the benefit
// of the public at large and to the detriment of our heirs and
// successors. We intend this dedication to be an overt act of
// relinquishment in perpetuity of all present and future rights to this
// software under copyright law.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
// IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY CLAIM, DAMAGES OR
// OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
// ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
// OTHER DEALINGS IN THE SOFTWARE.
//
// For more information, please refer to <http://unlicense.org/>
//
// The authors knows of no intellectual property claims relevant to this work.
*/

#include "crypto_hashblocks.h"


void sha512_rorx(const void* M, void* D, unsigned long L);
int crypto_hashblocks(unsigned char *statebytes,const unsigned char *in,unsigned long long inlen) {
	unsigned long num = (inlen & ~127ull)/128;
	inlen -= num * 128ull;
	int i;
	for (i = 0 ; i < 16 ; i++)
		((unsigned long long*)statebytes)[i] = __builtin_bswap64(((unsigned long long*)statebytes)[i]);
	sha512_rorx(in, statebytes, num);
	        for (i = 0 ; i < 16 ; i++)
                ((unsigned long long*)statebytes)[i] = __builtin_bswap64(((unsigned long long*)statebytes)[i]);
	return inlen;
}
