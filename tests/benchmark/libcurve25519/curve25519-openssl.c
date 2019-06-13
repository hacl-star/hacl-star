#include <stdint.h>

extern void X25519(uint8_t sec[32], uint8_t* priv, uint8_t* pub);

void curve25519_openssl(uint8_t *shared, uint8_t *my_priv, uint8_t *their_pub){
  X25519(shared, my_priv, their_pub);
}
