#include "smult.h"
#include "gfe.h"


static void cswap4x(gfe *x, gfe *y, int b)
{
  crypto_uint32 db = -b;
  crypto_uint32 t;
  int i,j;
  for(i=0;i<4;i++)
    for(j=0;j<5;j++) {
      t = x[i].v[j] ^ y[i].v[j];
      t &= db;
      x[i].v[j] ^= t;
      y[i].v[j] ^= t;
    }
}
  
static const crypto_int32 bbccdd = -114;
static const crypto_int32 aaccdd = 57;
static const crypto_int32 aabbdd = 66;
static const crypto_int32 aabbcc = 418;

static const crypto_int32 BBCCDD = -833;
static const crypto_int32 AACCDD = 2499;
static const crypto_int32 AABBDD = 1617;
static const crypto_int32 AABBCC = 561;

static const gfe aa = {{0x3fffff4,0x1ffffff,0x3ffffff,0x1ffffff,0x1ffffff}}; /* -11 */
static const gfe bb = {{22,0,0,0,0}};
static const gfe cc = {{19,0,0,0,0}};
static const gfe dd = {{3,0,0,0,0}};

static const crypto_int64 bigoffset[5] = {0xffffffc000,0x7fffffc000,0xffffffc000,0x7fffffc000,0x7fffffc000};
static const crypto_int64 zero[5] = {0,0,0,0,0};

int crypto_scalarmult(unsigned char *q, const unsigned char *n, const unsigned char *p)
{
  gfe work[12];
  gfe yz,yzt,r,tr;
  int i,j;
  int bit;
  int prevbit;
  int swap;

  gfe_unpack(&work[1], p);    /* xy1 */
  gfe_unpack(&work[2], p+16); /* xz1 */
  gfe_unpack(&work[3], p+32); /* xt1 */

  work[4] = aa;
  work[5] = bb;
  work[6] = cc;
  work[7] = dd;

  gfe_mul(&work[11], &work[ 1], &work[2]); /* xy1 * xz1 */
  gfe_mul(&work[10], &work[ 1], &work[3]); /* xy1 * xt1 */
  gfe_mul(&work[ 9], &work[ 2], &work[3]); /* xz1 * xt1 */
  gfe_mul(&work[ 8], &work[11], &work[3]); /* t3  * xt1 */

  prevbit = 0;
  j=2;
  for(i=31;i>=0;i--) {
    for(;j>=0;j--) {
      bit = (n[i]>>j) & 1;
      swap = bit ^ prevbit;
      prevbit = bit;
      cswap4x(work+4,work+8,swap);

      gfe_hadamard(work+8);
      gfe_hadamard(work+4);
      
      gfe_mul(work+ 8,work+ 8,work+4);
      gfe_mul(work+ 9,work+ 9,work+5);
      gfe_mul(work+10,work+10,work+6);
      gfe_mul(work+11,work+11,work+7);
     
      gfe_square(work+4,work+4);
      gfe_square(work+5,work+5);
      gfe_square(work+6,work+6);
      gfe_square(work+7,work+7);
    
      gfe_mulconst(work+ 8,work+ 8,BBCCDD,bigoffset);
      gfe_mulconst(work+ 9,work+ 9,AACCDD,zero);
      gfe_mulconst(work+10,work+10,AABBDD,zero);
      gfe_mulconst(work+11,work+11,AABBCC,zero);
    
      gfe_mulconst(work+ 4,work+ 4,BBCCDD,bigoffset);
      gfe_mulconst(work+ 5,work+ 5,AACCDD,zero);
      gfe_mulconst(work+ 6,work+ 6,AABBDD,zero);
      gfe_mulconst(work+ 7,work+ 7,AABBCC,zero);
    
      gfe_hadamard(work+8);
      gfe_hadamard(work+4);
    
      gfe_square(work+ 8,work+ 8);
      gfe_square(work+ 9,work+ 9);
      gfe_square(work+10,work+10);
      gfe_square(work+11,work+11);
      
      gfe_square(work+4,work+4);
      gfe_square(work+5,work+5);
      gfe_square(work+6,work+6);
      gfe_square(work+7,work+7);
      
      gfe_mul(work+ 9,work+ 9,work+1);
      gfe_mul(work+10,work+10,work+2);
      gfe_mul(work+11,work+11,work+3);
      
      gfe_mulconst(work+ 4,work+ 4,bbccdd,bigoffset);
      gfe_mulconst(work+ 5,work+ 5,aaccdd,zero);
      gfe_mulconst(work+ 6,work+ 6,aabbdd,zero);
      gfe_mulconst(work+ 7,work+ 7,aabbcc,zero);
    }
    j = 7;
  }
  cswap4x(work+4,work+8,bit);

  gfe_mul(&yz,work+5,work+6);
  gfe_mul(&yzt,&yz,work+7);
  gfe_invert(&r,&yzt);
  gfe_mul(&r,&r,work+4);
  gfe_mul(&tr,&r,work+7);
  gfe_mul(work+6,work+6,&tr);
  gfe_pack(q,work+6);
  gfe_mul(work+5,work+5,&tr);
  gfe_pack(q+16,work+5);
  gfe_mul(&yz, &yz ,&r);
  gfe_pack(q+32,&yz);
 
  return 0;
}


