/*
 * Copied from the eSTREAM api/ecrypt-sync.h,
 * and then edited to provide the crypto_stream/crypto_stream_xor interface.
 */

#include "crypto_stream.h"
#include "e/ecrypt-sync.h"

#ifdef ECRYPT_USES_DEFAULT_ALL_IN_ONE

/*
 *  * Default implementation of all-in-one encryption/decryption of
 *   * (short) packets.
 *    */

#ifdef ECRYPT_HAS_SINGLE_PACKET_FUNCTION

void ECRYPT_process_packet(
  int action,
  ECRYPT_ctx* ctx,
  const u8* iv,
  const u8* input,
  u8* output,
  u32 msglen)
{
  ECRYPT_ivsetup(ctx, iv);

#ifdef ECRYPT_HAS_SINGLE_BYTE_FUNCTION
  ECRYPT_process_bytes(action, ctx, input, output, msglen);
#else
  if (action == 0)
    ECRYPT_encrypt_bytes(ctx, input, output, msglen);
  else
    ECRYPT_decrypt_bytes(ctx, input, output, msglen);
#endif
}

#else

void ECRYPT_encrypt_packet(
  ECRYPT_ctx* ctx,
  const u8* iv,
  const u8* plaintext,
  u8* ciphertext,
  u32 msglen)
{
  ECRYPT_ivsetup(ctx, iv);
  ECRYPT_encrypt_bytes(ctx, plaintext, ciphertext, msglen);
}

void ECRYPT_decrypt_packet(
  ECRYPT_ctx* ctx,
  const u8* iv,
  const u8* ciphertext,
  u8* plaintext,
  u32 msglen)
{
  ECRYPT_ivsetup(ctx, iv);
  ECRYPT_decrypt_bytes(ctx, ciphertext, plaintext, msglen);
}

#endif

#endif

static int flaginitialized = 0;

int crypto_stream(
  unsigned char *c,unsigned long long clen,
  const unsigned char *n,
  const unsigned char *k
)
{
#ifdef ECRYPT_GENERATES_KEYSTREAM
  ECRYPT_ctx ctx;
  if (!flaginitialized) { ECRYPT_init(); flaginitialized = 1; }
  ECRYPT_keysetup(&ctx,k,crypto_stream_KEYBYTES * 8,crypto_stream_NONCEBYTES * 8);
  ECRYPT_ivsetup(&ctx,n);
  while (clen > 65536) {
    ECRYPT_keystream_bytes(&ctx,c,65536);
    c += 65536; clen -= 65536;
  }
  ECRYPT_keystream_bytes(&ctx,c,clen);
  return 0;
#else
  ECRYPT_ctx ctx;
  unsigned long long i;
  if (!flaginitialized) { ECRYPT_init(); flaginitialized = 1; }
  ECRYPT_keysetup(&ctx,k,crypto_stream_KEYBYTES * 8,crypto_stream_NONCEBYTES * 8);
  ECRYPT_ivsetup(&ctx,n);
  for (i = 0;i < clen;++i) c[i] = 0;
  while (clen > 65536) {
    ECRYPT_encrypt_bytes(&ctx,c,c,65536);
    c += 65536; clen -= 65536;
  }
  ECRYPT_encrypt_bytes(&ctx,c,c,clen);
  return 0;
#endif
}

int crypto_stream_xor(
  unsigned char *c,
  const unsigned char *m,unsigned long long mlen,
  const unsigned char *n,
  const unsigned char *k
)
{
  ECRYPT_ctx ctx;
  if (!flaginitialized) { ECRYPT_init(); flaginitialized = 1; }
  ECRYPT_keysetup(&ctx,k,crypto_stream_KEYBYTES * 8,crypto_stream_NONCEBYTES * 8);
  ECRYPT_ivsetup(&ctx,n);
  while (mlen > 65536) {
    ECRYPT_encrypt_bytes(&ctx,m,c,65536);
    m += 65536; c += 65536; mlen -= 65536;
  }
  ECRYPT_encrypt_bytes(&ctx,m,c,mlen);
  return 0;
}
