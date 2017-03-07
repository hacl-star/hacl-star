#ifndef __Chacha20_H
#define __Chacha20_H

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "Chacha20_state.h"

int chacha20_init_block(unsigned char* out, chacha20_state st, const unsigned char* k, const unsigned char* n, unsigned int ctr);

int chacha20_continue(        
	unsigned char *out,
        const unsigned char *in,
        unsigned long long inlen,
        chacha20_state st);

int crypto_stream(
                                  unsigned char *out,
                                  unsigned long long outlen,
                                  const unsigned char *n,
                                  const unsigned char *k
		  );


int crypto_stream_xor(
        unsigned char *out,
        const unsigned char *in,
        unsigned long long inlen,
        const unsigned char *n,
        const unsigned char *k
		      );

int crypto_stream_xor_ic(
        unsigned char *out,
        const unsigned char *in,
        unsigned long long inlen,
        const unsigned char *n,
        const unsigned char *k,
	unsigned int ctr
		      );
#endif
