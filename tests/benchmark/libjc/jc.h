#ifndef _LIBJC_H_
#define _LIBJC_H_

#ifdef __cplusplus
extern "C" {
#endif

extern void libjc_avx_poly1305_avx(uint64_t *out, uint64_t *in, uint64_t inlen, uint64_t *k);
extern void libjc_avx2_poly1305_avx2(uint64_t *out, uint64_t *in, uint64_t inlen, uint64_t *k);
extern void poly1305_ref3(uint64_t *out, uint64_t *in, uint64_t inlen, uint64_t *k);

void libjc_avx_chacha20_avx(uint64_t *output, uint64_t *plain, uint32_t len, uint64_t *key, uint64_t *nonce, uint32_t counter);
void libjc_avx2_chacha20_avx2(uint64_t *output, uint64_t *plain, uint32_t len, uint64_t *key, uint64_t *nonce, uint32_t counter);
void chacha20_ref(uint64_t *output, uint64_t *plain, uint32_t len, uint64_t *key, uint64_t *nonce, uint32_t counter);

#ifdef __cplusplus
}
#endif

#endif