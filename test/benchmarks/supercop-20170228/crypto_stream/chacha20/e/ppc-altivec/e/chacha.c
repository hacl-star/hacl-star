/*
chacha-altivec.c version 20080120
D. J. Bernstein, with big contributions from Matthijs van Duin
Public domain.
*/

#include <altivec.h>
#include <string.h>
#include "ecrypt-sync.h"

void ECRYPT_init(void)
{
  return;
}

static const char sigma[16] = "expand 32-byte k";
static const char tau[16] = "expand 16-byte k";

void ECRYPT_keysetup(ECRYPT_ctx *x,const u8 *k,u32 kbits,u32 ivbits)
{
  const char *constants;

  memcpy(x->myaligned.input + 16,k,16);
  if (kbits == 256) { /* recommended */
    k += 16;
    constants = sigma;
  } else { /* kbits == 128 */
    constants = tau;
  }
  memcpy(x->myaligned.input + 32,k,16);
  memcpy(x->myaligned.input + 0,constants,16);
}

void ECRYPT_ivsetup(ECRYPT_ctx *x,const u8 *iv)
{
  memset(x->myaligned.input + 48,0,8);
  memcpy(x->myaligned.input + 56,iv,8);
}

typedef vector unsigned int vu32;
typedef vector unsigned char vu8;

static const u32 permutations[] __attribute__((aligned (16))) = {
  0x04050607, 0x08090A0B, 0x0C0D0E0F, 0x00010203
, 0x03020100, 0x17161514, 0x0B0A0908, 0x1F1E1D1C
} ;

void ECRYPT_encrypt_bytes(ECRYPT_ctx *x,const u8 *m,u8 *c,u32 bytes)
{
  const vu8  vrp1 = (vu8) vec_ld(0, permutations);
  const vu8  vrp2 = vec_perm(vrp1, vrp1, vrp1);
  const vu8  vrp3 = vec_perm(vrp2, vrp2, vrp1);
  const vu8  swapendian = (vu8) vec_ld(16, permutations);
  const vu32 vrr07 = vec_splat_u32( 7);
  const vu32 vrr08 = vec_splat_u32( 8);
  const vu32 vrr12 = vec_splat_u32(12);
  const vu32 vrr16 = vrr08 + vrr08;
  u8 *ctarget;
  vu32 tmp[4];
  vu32 x0;
  vu32 x1;
  vu32 x2;
  vu32 x3;
  vu32 y0;
  vu32 y1;
  vu32 y2;
  vu32 y3;
  int i;

  if (!bytes) return;

  for (;;) {
    if (bytes < 64) {
      for (i = 0;i < bytes;++i) ((char *) tmp)[i] = m[i];
      m = (char *) tmp;
      ctarget = c;
      c = (char *) tmp;
    }

    x0 = vec_ld( 0, (const u32 *) &x->myaligned.input);
    x1 = vec_ld(16, (const u32 *) &x->myaligned.input);
    x2 = vec_ld(32, (const u32 *) &x->myaligned.input);
    x3 = vec_ld(48, (const u32 *) &x->myaligned.input);
    x0 = vec_perm(x0,x0,swapendian);
    x1 = vec_perm(x1,x1,swapendian);
    x2 = vec_perm(x2,x2,swapendian);
    x3 = vec_perm(x3,x3,swapendian);
    y0 = x0;
    y1 = x1;
    y2 = x2;
    y3 = x3;

    if (!++x->myaligned.input[48])
    if (!++x->myaligned.input[49])
    if (!++x->myaligned.input[50])
    if (!++x->myaligned.input[51])
    if (!++x->myaligned.input[52])
    if (!++x->myaligned.input[53])
    if (!++x->myaligned.input[54])
    if (!++x->myaligned.input[55])
      ; /* stopping at 2^70 bytes per nonce is user's responsibility */

    for (i = 20;i > 0;i -= 2) {
      y0 += y1; y3 ^= y0; y3 = vec_rl(y3,vrr16);
      y2 += y3; y1 ^= y2; y1 = vec_rl(y1,vrr12);
      y0 += y1; y3 ^= y0; y3 = vec_rl(y3,vrr08);
      y2 += y3; y1 ^= y2; y1 = vec_rl(y1,vrr07);
      y0 = vec_perm(y0,y0,vrp3);
      y2 = vec_perm(y2,y2,vrp1);
      y3 = vec_perm(y3,y3,vrp2);
      y0 += y1; y3 ^= y0; y3 = vec_rl(y3,vrr16);
      y2 += y3; y1 ^= y2; y1 = vec_rl(y1,vrr12);
      y0 += y1; y3 ^= y0; y3 = vec_rl(y3,vrr08);
      y2 += y3; y1 ^= y2; y1 = vec_rl(y1,vrr07);
      y0 = vec_perm(y0,y0,vrp1);
      y2 = vec_perm(y2,y2,vrp3);
      y3 = vec_perm(y3,y3,vrp2);
    }
    x0 += y0;
    x1 += y1;
    x2 += y2;
    x3 += y3;
    x0 = vec_perm(x0,x0,swapendian);
    x1 = vec_perm(x1,x1,swapendian);
    x2 = vec_perm(x2,x2,swapendian);
    x3 = vec_perm(x3,x3,swapendian);
    y0 = vec_ld( 0, (u32 *) m) ^ x0;
    y1 = vec_ld(16, (u32 *) m) ^ x1;
    y2 = vec_ld(32, (u32 *) m) ^ x2;
    y3 = vec_ld(48, (u32 *) m) ^ x3;
    vec_st(y0,  0, (u32 *) c);
    vec_st(y1, 16, (u32 *) c);
    vec_st(y2, 32, (u32 *) c);
    vec_st(y3, 48, (u32 *) c);

    if (bytes <= 64) {
      if (bytes < 64) {
        for (i = 0;i < bytes;++i) ctarget[i] = c[i];
      }
      return;
    }
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
