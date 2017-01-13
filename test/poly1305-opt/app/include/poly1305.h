#ifndef POLY1305_H
#define POLY1305_H

#include <stddef.h>

#if !defined(LIB_PUBLIC)
#define LIB_PUBLIC
#endif

#if defined(__cplusplus)
extern "C" {
#endif

typedef struct poly1305_state {
	unsigned char opaque[320];
} poly1305_state;

typedef struct poly1305_key {
	unsigned char b[32];
} poly1305_key;

LIB_PUBLIC void poly1305_init(poly1305_state *S, const poly1305_key *key);
LIB_PUBLIC void poly1305_init_ext(poly1305_state *S, const poly1305_key *key, size_t bytes_hint);
LIB_PUBLIC void poly1305_update(poly1305_state *S, const unsigned char *in, size_t inlen);
LIB_PUBLIC void poly1305_finish(poly1305_state *S, unsigned char *mac);

LIB_PUBLIC void poly1305_auth(unsigned char *mac, const unsigned char *in, size_t inlen, const poly1305_key *key);

LIB_PUBLIC int poly1305_startup(void);

#if defined(UTILITIES)
void poly1305_fuzz(void);
void poly1305_bench(void);
#endif

#if defined(__cplusplus)
}
#endif

#endif /* POLY1305_H */

