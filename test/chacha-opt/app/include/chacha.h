#ifndef CHACHA_H
#define CHACHA_H

#include <stddef.h>

#if !defined(LIB_PUBLIC)
	#define LIB_PUBLIC
#endif

#if defined(__cplusplus)
extern "C" {
#endif

typedef struct chacha_state_t {
	unsigned char opaque[128];
} chacha_state;

typedef struct chacha_key_t {
	unsigned char b[32];
} chacha_key;

typedef struct chacha_iv_t {
	unsigned char b[8];
} chacha_iv;

typedef struct chacha_iv24_t {
	unsigned char b[24];
} chacha_iv24;

LIB_PUBLIC void hchacha(const unsigned char key[32], const unsigned char iv[16], unsigned char out[32], size_t rounds);

LIB_PUBLIC void chacha_init(chacha_state *S, const chacha_key *key, const chacha_iv *iv, size_t rounds);
LIB_PUBLIC void xchacha_init(chacha_state *S, const chacha_key *key, const chacha_iv24 *iv, size_t rounds);
LIB_PUBLIC size_t chacha_update(chacha_state *S, const unsigned char *in, unsigned char *out, size_t inlen);
LIB_PUBLIC size_t chacha_final(chacha_state *S, unsigned char *out);

LIB_PUBLIC void chacha(const chacha_key *key, const chacha_iv *iv, const unsigned char *in, unsigned char *out, size_t inlen, size_t rounds);
LIB_PUBLIC void xchacha(const chacha_key *key, const chacha_iv24 *iv, const unsigned char *in, unsigned char *out, size_t inlen, size_t rounds);

LIB_PUBLIC int chacha_startup(void);

#if defined(UTILITIES)
void chacha_fuzz(void);
void chacha_bench(void);
#endif

#if defined(__cplusplus)
}
#endif

#endif /* CHACHA_H */

