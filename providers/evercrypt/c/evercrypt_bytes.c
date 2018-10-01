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

EverCrypt_Bytes_cipher_tag
EverCrypt_Bytes_chacha20_poly1305_encrypt(FStar_Bytes_bytes m,
                                          FStar_Bytes_bytes aad,
                                          FStar_Bytes_bytes k,
                                          FStar_Bytes_bytes n) {
  FStar_Bytes_bytes cipher = {
    .length = m.length,
    .data = KRML_HOST_CALLOC(m.length, 1)
  };
  FStar_Bytes_bytes tag = {
    .length = 16,
    .data = KRML_HOST_CALLOC(16, 1)
  };
  EverCrypt_Bytes_cipher_tag out = {
    .cipher = cipher,
    .tag = tag
  };
  EverCrypt_chacha20_poly1305_encrypt((uint8_t *) k.data,
                                      (uint8_t *) n.data,
                                      (uint8_t *) aad.data,
                                      aad.length,
                                      (uint8_t *) m.data,
                                      m.length,
                                      (uint8_t *) cipher.data,
                                      (uint8_t *) tag.data);
  return out;
}


EverCrypt_Bytes_maybe_plaintext
EverCrypt_Bytes_chacha20_poly1305_decrypt(FStar_Bytes_bytes cipher,
                                          FStar_Bytes_bytes tag,                               
                                          FStar_Bytes_bytes aad,
                                          FStar_Bytes_bytes k,
                                          FStar_Bytes_bytes n) {
  FStar_Bytes_bytes m = {
    .length = cipher.length,
    .data = KRML_HOST_CALLOC(cipher.length, 1)
  };
  uint32_t res =
    EverCrypt_chacha20_poly1305_decrypt((uint8_t *) k.data,
                                        (uint8_t *) n.data,
                                        (uint8_t *) aad.data,
                                        aad.length,
                                        (uint8_t *) m.data,
                                        m.length,
                                        (uint8_t *) cipher.data,
                                        (uint8_t *) tag.data);

  EverCrypt_Bytes_maybe_plaintext out;  
  if (res == 1) {
    out.tag = EverCrypt_Bytes_Correct;
    out._0  = m;
  }
  else {
    out.tag = EverCrypt_Bytes_Error;
  }
  
  return out;
}
