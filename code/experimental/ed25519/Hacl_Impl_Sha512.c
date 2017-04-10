#include <sodium.h>

void Hacl_Impl_Sha512_sha512(unsigned char *out, unsigned char *in, unsigned int len){
  crypto_hash_sha512(out, in, len);
}
