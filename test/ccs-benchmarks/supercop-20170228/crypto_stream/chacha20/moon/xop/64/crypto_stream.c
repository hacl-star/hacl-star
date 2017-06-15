#define chacha_fn chacha_xop

#include "crypto_stream.h"
#include <stddef.h>

extern void chacha_fn(const unsigned char *k, const unsigned char *n, const unsigned char *in, unsigned char *out, size_t inlen, size_t rounds);

int crypto_stream_xor(unsigned char *out, const unsigned char *in, unsigned long long inlen, const unsigned char *n, const unsigned char *k) {
	chacha_fn(k, n, in, out, (size_t)inlen, 20);
	return 0;
}

int crypto_stream(unsigned char *out, unsigned long long outlen, const unsigned char *n, const unsigned char *k) {
	chacha_fn(k, n, NULL, out, (size_t)outlen, 20);
	return 0;
}
