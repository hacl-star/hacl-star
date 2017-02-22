#ifndef __Hacl_CP_H
#define __Hacl_CP_H

#include "kremlib.h"
#include "testlib.h"
#include "Chacha20.h"
#include "Poly1305_64_blocks.h"

void
Hacl_AEAD_Chacha20Poly1305_encrypt(
  uint8_t *c,
  uint8_t *mac,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *aad,
  uint64_t aadlen,
  uint8_t *n,
  uint8_t *k
				   );


#endif
