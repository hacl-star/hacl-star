#include "smult.h"
#include "gfe.h"


static void cswap4x(gfe *x, gfe *y, int b)
{
  crypto_uint32 db = -b;
  uint128_t t = *x ^ *y;
  t &= db;
  *x = *x ^ t;
  *y = *x ^ t;
}
  
static const crypto_int32 bbccdd = -114;
static const crypto_int32 aaccdd = 57;
static const crypto_int32 aabbdd = 66;
static const crypto_int32 aabbcc = 418;

static const crypto_int32 BBCCDD = -833;
static const crypto_int32 AACCDD = 2499;
static const crypto_int32 AABBDD = 1617;
static const crypto_int32 AABBCC = 561;

/* KB: I am not sure about the following values, I may have mangled them */

static const gfe aa = ((uint128_t)1 << 127) - 12;
static const gfe bb = (uint128_t) 22;
static const gfe cc = (uint128_t) 19;
static const gfe dd = (uint128_t) 3;

static const crypto_int64 bigoffset[2] = 
  {0xffffff7fffffcfff,0xfffc7fffffc7fffd};

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

  gfe_mul(&work[11], work[ 1], work[2]); /* xy1 * xz1 */
  gfe_mul(&work[10], work[ 1], work[3]); /* xy1 * xt1 */
  gfe_mul(&work[ 9], work[ 2], work[3]); /* xz1 * xt1 */
  gfe_mul(&work[ 8], work[11], work[3]); /* t3  * xt1 */

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
      
      gfe_mul(work+ 8,work[8], work[4]);
      gfe_mul(work+ 9,work[9], work[5]);
      gfe_mul(work+10,work[10],work[6]);
      gfe_mul(work+11,work[11],work[7]);
     
      gfe_square(work+4,work[4]);
      gfe_square(work+5,work[5]);
      gfe_square(work+6,work[6]);
      gfe_square(work+7,work[7]);
    
      gfe_mulconstd(work+ 8,work[8],BBCCDD,bigoffset);
      gfe_mulconstz(work+ 9,work[9],AACCDD);
      gfe_mulconstz(work+10,work[10],AABBDD);
      gfe_mulconstz(work+11,work[11],AABBCC);
    
      gfe_mulconstd(work+ 4,work[4],BBCCDD,bigoffset);
      gfe_mulconstz(work+ 5,work[5],AACCDD);
      gfe_mulconstz(work+ 6,work[6],AABBDD);
      gfe_mulconstz(work+ 7,work[7],AABBCC);
    
      gfe_hadamard(work+8);
      gfe_hadamard(work+4);
    
      gfe_square(work+ 8,work[8]);
      gfe_square(work+ 9,work[9]);
      gfe_square(work+10,work[10]);
      gfe_square(work+11,work[11]);
      
      gfe_square(work+4,work[4]);
      gfe_square(work+5,work[5]);
      gfe_square(work+6,work[6]);
      gfe_square(work+7,work[7]);
      
      gfe_mul(work+ 9,work[9],work[1]);
      gfe_mul(work+10,work[10],work[2]);
      gfe_mul(work+11,work[11],work[3]);
      
      gfe_mulconstd(work+ 4,work[4],bbccdd,bigoffset);
      gfe_mulconstz(work+ 5,work[5],aaccdd);
      gfe_mulconstz(work+ 6,work[6],aabbdd);
      gfe_mulconstz(work+ 7,work[7],aabbcc);
    }
    j = 7;
  }
  cswap4x(work+4,work+8,bit);

  gfe_mul(&yz,work[5],work[6]);
  gfe_mul(&yzt,yz,work[7]);
  gfe_invert(&r,yzt);
  gfe_mul(&r,r,work[4]);
  gfe_mul(&tr,r,work[7]);
  gfe_mul(work+6,work[6],tr);
  gfe_pack(q,&work[6]);
  gfe_mul(work+5,work[5],tr);
  gfe_pack(q+16,&work[5]);
  gfe_mul(&yz, yz ,r);
  gfe_pack(q+32,&yz);
 
  return 0;
}


