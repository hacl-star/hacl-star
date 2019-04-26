#include "crypto_uint64.h"
#include "crypto_int64.h"
#include "gfe.h"
typedef crypto_uint64 u64;
typedef crypto_uint32 u32;

#include <inttypes.h>
#include <stdlib.h>
static const gfe c127m1 = ((uint128_t)1 << 127) - 1;
static const gfe c64m1 = ((uint128_t)1 << 64) - 1;
static const gfe c63m1 = ((uint128_t)1 << 63) - 1;

/* We are using a naive 128-bit representation for field elements */

/* CURRENT HOT/COSTLY CODE to optimize: 
   hadamard > xsquare > mulconstz > fsub > fmul,fadd,mulconstd 
*/

typedef uint8_t u8;

void gfe_unpack(gfe *r, const unsigned char b[16])
{
  gfe rr = 0;
  rr  = b[0];
  rr |= ((u64)b[1] << 8);
  rr |= ((u64)b[2] << 16);
  rr |= ((u64)b[3] << 24);
  rr |= ((u64)b[4] << 32);
  rr |= ((u64)b[5] << 40);
  rr |= ((u64)b[6] << 48);
  rr |= ((u64)b[7] << 56);
  rr |= ((uint128_t)b[8] << 64);
  rr |= ((uint128_t)b[9] << 72);
  rr |= ((uint128_t)b[10] << 80);
  rr |= ((uint128_t)b[11] << 88);
  rr |= ((uint128_t)b[12] << 96);
  rr |= ((uint128_t)b[13] << 104);
  rr |= ((uint128_t)b[14] << 112);
  rr |= ((uint128_t)b[15] << 120);
  *r = rr;
}

void gfe_pack(unsigned char r[16], const gfe *x)
{
  u32 c;
  gfe t = *x;

  r[0] = (u8) t;
  r[1] = (u8) (t>>8);
  r[2] = (u8) (t>>16);
  r[3] = (u8) (t>>24);
  r[4] = (u8) (t>>32);
  r[5] = (u8) (t>>40);
  r[6] = (u8) (t>>48);
  r[7] = (u8) (t>>56);

  r[8] = (u8) (t>>64);
  r[9] = (u8) (t>>72);
  r[10] = (u8) (t>>80);
  r[11] = (u8) (t>>88);
  r[12] = (u8) (t>>96);
  r[13] = (u8) (t>>104);
  r[14] = (u8) (t>>112);
  r[15] = (u8) (t>>120);
}

static void gfe_add(gfe *r, const gfe x, const gfe y)
{
  gfe rr = x + y;
  rr = (rr >> 127) + (rr & c127m1);
  *r = rr;
}

static void gfe_sub(gfe *r, const gfe x, const gfe y)
{
  gfe rr = x + c127m1 - y;
  rr = rr >> 127 + (rr & c127m1);
  *r = rr;
}

void gfe_hadamard(gfe r[4])
{
  gfe a,b,c,d;
  int i;

  gfe_add(&a,r[0],r[1]);
  gfe_add(&b,r[2],r[3]);
  gfe_sub(&c,r[0],r[1]);
  gfe_sub(&d,r[2],r[3]);

  gfe_add(&r[0],a,b);
  gfe_sub(&r[1],a,b);
  gfe_add(&r[2],c,d);
  gfe_sub(&r[3],c,d);

  /* KB: Don't know if I got the following right, I don't understand the math */
  for (i = 1;i < 4;++i) {
    r[i] += 0xffffffc;
    r[i] += (uint64_t) 0x7fffffc << 26;
    r[i] += (uint128_t)0xffffffc << 51;
    r[i] += (uint128_t)0x7fffffc << 77;
    r[i] += (uint128_t)0x7fffffc << 102;
  }
}

void gfe_mul(gfe *r, const gfe a, const gfe b)
{
  
  uint64_t a0 = a;
  uint64_t a1 = a >> 64;
  uint64_t b0 = a;
  uint64_t b1 = a >> 64;
  
  uint128_t a0b0 = a0 * (uint128_t)b0;
  uint128_t a0b1 = a0 * (uint128_t)b1;
  uint128_t a1b0 = a1 * (uint128_t)b0;
  uint128_t a1b1 = a1 * (uint128_t)b1;

  uint128_t r1 = a0b1 + a1b0;
  r1 += a0b0 >> 64;
  
  uint128_t r2 = (a1b1 << 1) + (r1 >> 63);  
  uint128_t r0 = (a0b0 & c64m1) | ((r1 & c63m1) << 64);
  r0 += r2;
  r0 = r0 >> 127 + (r0 & c127m1);
  *r = r0;
  

}


void gfe_square(gfe *r, const gfe a)
{
  uint64_t a0 = a;
  uint64_t a1 = a >> 64;
  
  uint128_t a0a0 = a0 * (uint128_t)a0;
  uint128_t a0a1 = a0 * (uint128_t)a1;
  uint128_t a1a1 = a1 * (uint128_t)a1;

  uint128_t r1 = a0a1 << 1;
  r1 += a0a0 >> 64;

  uint128_t r2 = (a1a1 << 1) + (r1 >> 63);  
  uint128_t r0 = (a0a0 & c64m1) | ((r1 & c63m1) << 64);
  r0 += r2;
  r0 = r0 >> 127 + (r0 & c127m1);
  *r = r0;
}


/* KB: The following two functions, I don't fully understand. I may have messed them up */

void gfe_mulconstz(gfe *r, const gfe a, const crypto_int32 cst)
{
  uint64_t a0 = a;
  uint64_t a1 = a >> 64;
  
  uint128_t r0 = (uint128_t)a0*cst;
  uint128_t r1 = (uint128_t)a1*cst;
  r1 += r0 >> 64;
  r0 = (r0 & c64m1) | ((r1 & c63m1) << 64);
  r1 = (r1 >> 63) << 1;
  r0 += r1;
  r0 = r0 >> 127 + (r0 & c127m1);
  *r = r0;
}

void gfe_mulconstd(gfe *r, const gfe a, const crypto_int32 cst, const crypto_int64* d)
{
  uint64_t a0 = a;
  uint64_t a1 = a >> 64;
  
  uint128_t r0 = (uint128_t)a0*cst + d[0];
  uint128_t r1 = (uint128_t)a1*cst + d[1];
  r1 += r0 >> 64;
  r0 = (r0 & c64m1) | ((r1 & c63m1) << 64);
  r1 = (r1 >> 63) << 1;
  r0 += r1;
  r0 = r0 >> 127 + (r0 & c127m1);
  *r = r0;
}



void gfe_invert(gfe *r, const gfe x)
{
  gfe x2,x3,x6,x12,x15,x30,x_5_0, x_10_0, x_20_0, x_40_0, x_80_0, x_120_0, x_125_0, t;
  int i;

  gfe_square(&x2, x);                     /*  2 */
  gfe_mul(&x3,x2,x);                     /*  3 mult */
  gfe_square(&x6,x3);                    /*  6 */
  gfe_square(&x12,x6);                   /*  12 */
  gfe_mul(&x15,x12,x3);                 /*  15 mult */
  gfe_square(&x30, x15);                 /*  30 */
  gfe_mul(&x_5_0, x30, x);               /*  31 = 2^5-1 mult */

  gfe_square(&t, x_5_0);
  for(i=6;i<10;i++) gfe_square(&t, t);   /*  2^10-2^5 */
  gfe_mul(&x_10_0,t,x_5_0);             /*  2^10-1 mult */

  gfe_square(&t, x_10_0);
  for(i=11;i<20;i++) gfe_square(&t, t);  /*  2^20-2^10 */
  gfe_mul(&x_20_0,t,x_10_0);            /*  2^20-1 mult */

  gfe_square(&t, x_20_0);
  for(i=21;i<40;i++) gfe_square(&t, t);  /*  2^40-2^20 */
  gfe_mul(&x_40_0,t,x_20_0);            /*  2^40-1 mult */

  gfe_square(&t, x_40_0);
  for(i=41;i<80;i++) gfe_square(&t, t);  /*  2^80-2^40 */
  gfe_mul(&x_80_0,t,x_40_0);            /*  2^80-1 mult */

  gfe_square(&t, x_80_0);
  for(i=81;i<120;i++) gfe_square(&t, t); /*  2^120-2^40 */
  gfe_mul(&x_120_0,t,x_40_0);           /*  2^80-1 mult */

  gfe_square(&t, x_120_0);
  for(i=121;i<125;i++) gfe_square(&t, t);/*  2^120-2^40 */
  gfe_mul(&x_125_0, t, x_5_0);

  gfe_square(&t, x_125_0);               /* 2^126-2^1 */
  gfe_square(&t, t);                     /* 2^127-2^2 */
  gfe_mul(r,t,x);                        /* 2^127-3 */
  
}

