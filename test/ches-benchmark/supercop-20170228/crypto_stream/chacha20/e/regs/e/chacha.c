/*
chacha-regs.c version 20080118
D. J. Bernstein
Public domain.
*/

#include "ecrypt-sync.h"

#define ROTATE(v,c) (ROTL32(v,c))
#define XOR(v,w) ((v) ^ (w))
#define PLUS(v,w) (U32V((v) + (w)))
#define PLUSONE(v) (PLUS((v),1))

#define QUARTERROUND(a,b,c,d) \
  a = PLUS(a,b); d = ROTATE(XOR(d,a),16); \
  c = PLUS(c,d); b = ROTATE(XOR(b,c),12); \
  a = PLUS(a,b); d = ROTATE(XOR(d,a), 8); \
  c = PLUS(c,d); b = ROTATE(XOR(b,c), 7);

static void salsa20_wordtobyte(u8 output[64],const u32 input[16])
{
  u32 x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15;
  int i;

  x0 = input[0];
  x1 = input[1];
  x2 = input[2];
  x3 = input[3];
  x4 = input[4];
  x5 = input[5];
  x6 = input[6];
  x7 = input[7];
  x8 = input[8];
  x9 = input[9];
  x10 = input[10];
  x11 = input[11];
  x12 = input[12];
  x13 = input[13];
  x14 = input[14];
  x15 = input[15];
  for (i = 20;i > 0;i -= 2) {
    QUARTERROUND( x0, x4, x8,x12)
    QUARTERROUND( x1, x5, x9,x13)
    QUARTERROUND( x2, x6,x10,x14)
    QUARTERROUND( x3, x7,x11,x15)
    QUARTERROUND( x0, x5,x10,x15)
    QUARTERROUND( x1, x6,x11,x12)
    QUARTERROUND( x2, x7, x8,x13)
    QUARTERROUND( x3, x4, x9,x14)
  }
  x0 = PLUS(x0,input[0]);
  x1 = PLUS(x1,input[1]);
  x2 = PLUS(x2,input[2]);
  x3 = PLUS(x3,input[3]);
  x4 = PLUS(x4,input[4]);
  x5 = PLUS(x5,input[5]);
  x6 = PLUS(x6,input[6]);
  x7 = PLUS(x7,input[7]);
  x8 = PLUS(x8,input[8]);
  x9 = PLUS(x9,input[9]);
  x10 = PLUS(x10,input[10]);
  x11 = PLUS(x11,input[11]);
  x12 = PLUS(x12,input[12]);
  x13 = PLUS(x13,input[13]);
  x14 = PLUS(x14,input[14]);
  x15 = PLUS(x15,input[15]);
  U32TO8_LITTLE(output + 0,x0);
  U32TO8_LITTLE(output + 4,x1);
  U32TO8_LITTLE(output + 8,x2);
  U32TO8_LITTLE(output + 12,x3);
  U32TO8_LITTLE(output + 16,x4);
  U32TO8_LITTLE(output + 20,x5);
  U32TO8_LITTLE(output + 24,x6);
  U32TO8_LITTLE(output + 28,x7);
  U32TO8_LITTLE(output + 32,x8);
  U32TO8_LITTLE(output + 36,x9);
  U32TO8_LITTLE(output + 40,x10);
  U32TO8_LITTLE(output + 44,x11);
  U32TO8_LITTLE(output + 48,x12);
  U32TO8_LITTLE(output + 52,x13);
  U32TO8_LITTLE(output + 56,x14);
  U32TO8_LITTLE(output + 60,x15);
}

void ECRYPT_init(void)
{
  return;
}

static const char sigma[16] = "expand 32-byte k";
static const char tau[16] = "expand 16-byte k";

void ECRYPT_keysetup(ECRYPT_ctx *x,const u8 *k,u32 kbits,u32 ivbits)
{
  const char *constants;

  x->input[4] = U8TO32_LITTLE(k + 0);
  x->input[5] = U8TO32_LITTLE(k + 4);
  x->input[6] = U8TO32_LITTLE(k + 8);
  x->input[7] = U8TO32_LITTLE(k + 12);
  if (kbits == 256) { /* recommended */
    k += 16;
    constants = sigma;
  } else { /* kbits == 128 */
    constants = tau;
  }
  x->input[8] = U8TO32_LITTLE(k + 0);
  x->input[9] = U8TO32_LITTLE(k + 4);
  x->input[10] = U8TO32_LITTLE(k + 8);
  x->input[11] = U8TO32_LITTLE(k + 12);
  x->input[0] = U8TO32_LITTLE(constants + 0);
  x->input[1] = U8TO32_LITTLE(constants + 4);
  x->input[2] = U8TO32_LITTLE(constants + 8);
  x->input[3] = U8TO32_LITTLE(constants + 12);
}

void ECRYPT_ivsetup(ECRYPT_ctx *x,const u8 *iv)
{
  x->input[12] = 0;
  x->input[13] = 0;
  x->input[14] = U8TO32_LITTLE(iv + 0);
  x->input[15] = U8TO32_LITTLE(iv + 4);
}

void ECRYPT_encrypt_bytes(ECRYPT_ctx *x,const u8 *m,u8 *c,u32 bytes)
{
  u8 output[64];
  int i;

  if (!bytes) return;
  for (;;) {
    salsa20_wordtobyte(output,x->input);
    x->input[12] = PLUSONE(x->input[12]);
    if (!x->input[12]) {
      x->input[13] = PLUSONE(x->input[13]);
      /* stopping at 2^70 bytes per nonce is user's responsibility */
    }
    if (bytes <= 64) {
      for (i = 0;i < bytes;++i) c[i] = m[i] ^ output[i];
      return;
    }
    for (i = 0;i < 64;++i) c[i] = m[i] ^ output[i];
    bytes -= 64;
    c += 64;
    m += 64;
  }
}

void ECRYPT_decrypt_bytes(ECRYPT_ctx *x,const u8 *c,u8 *m,u32 bytes)
{
  ECRYPT_encrypt_bytes(x,c,m,bytes);
}

void ECRYPT_keystream_bytes(ECRYPT_ctx *x,u8 *stream,u32 bytes)
{
  u32 i;
  for (i = 0;i < bytes;++i) stream[i] = 0;
  ECRYPT_encrypt_bytes(x,stream,stream,bytes);
}
