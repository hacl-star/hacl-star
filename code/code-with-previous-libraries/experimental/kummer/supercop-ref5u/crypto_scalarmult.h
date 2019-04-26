#ifndef crypto_scalarmult_kummer_H
#define crypto_scalarmult_kummer_H

#define crypto_scalarmult_kummer_avx2int_SCALARBYTES 32
#define crypto_scalarmult_kummer_avx2int_BYTES 48
 
#ifdef __cplusplus
extern "C" {
#endif
extern int crypto_scalarmult_kummer_avx2int(unsigned char *,const unsigned char *,const unsigned char *);
extern int crypto_scalarmult_kummer_avx2int_base(unsigned char *,const unsigned char *);
#ifdef __cplusplus
}
#endif

#define crypto_scalarmult_kummer crypto_scalarmult_kummer_avx2int
#define crypto_scalarmult_kummer_base crypto_scalarmult_kummer_avx2int_base
#define crypto_scalarmult_kummer_BYTES crypto_scalarmult_kummer_avx2int_BYTES
#define crypto_scalarmult_kummer_SCALARBYTES crypto_scalarmult_kummer_avx2int_SCALARBYTES
#define crypto_scalarmult_kummer_IMPLEMENTATION "crypto_scalarmult/kummer/avx2int"
#ifndef crypto_scalarmult_kummer_avx2int_VERSION
#define crypto_scalarmult_kummer_avx2int_VERSION "-"
#endif
#define crypto_scalarmult_kummer_VERSION crypto_scalarmult_kummer_avx2int_VERSION

#endif
