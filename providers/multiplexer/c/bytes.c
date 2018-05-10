#include "kremlin/fstar_bytes.h"
#include "kremlib.h"
#include "EverCrypt_Bytes.h"
#include "EverCrypt.h"

FStar_Bytes_bytes EverCrypt_Bytes_x25519(FStar_Bytes_bytes secret, FStar_Bytes_bytes base) {
  FStar_Bytes_bytes out = {
    .length = 32,
    .data = KRML_HOST_CALLOC(32, 1)
  };
  EverCrypt_x25519((uint8_t *) out.data, (uint8_t *) secret.data,  (uint8_t *) base.data);
  return out;
}
