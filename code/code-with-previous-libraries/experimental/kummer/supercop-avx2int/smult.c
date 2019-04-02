#include "smult.h"
#include "gfe.h"
#include "gfe4x.h"
#include "crypto_uint64.h"

static const vec mask25 = {0x1ffffff,0x1ffffff,0x1ffffff,0x1ffffff};
static const vec mask26 = {0x3ffffff,0x3ffffff,0x3ffffff,0x3ffffff};

void gfe4x_from_gfe(gfe4x *y,const gfe *x)
{
  int i;

  for (i = 0;i < 5;++i) {
    0[(crypto_uint64 *) &y->v[i]] = x[0].v[i];
    1[(crypto_uint64 *) &y->v[i]] = x[1].v[i];
    2[(crypto_uint64 *) &y->v[i]] = x[2].v[i];
    3[(crypto_uint64 *) &y->v[i]] = x[3].v[i];
  }
}

void gfe4x_to_gfe(const gfe4x *y,gfe *x)
{
  int i;

  for (i = 0;i < 5;++i) {
    x[0].v[i] = 0[(crypto_uint64 *) &y->v[i]];
    x[1].v[i] = 1[(crypto_uint64 *) &y->v[i]];
    x[2].v[i] = 2[(crypto_uint64 *) &y->v[i]];
    x[3].v[i] = 3[(crypto_uint64 *) &y->v[i]];
  }
}

inline void gfe4x_mulconst(gfe4x *r, const gfe4x *a, const vec *b)
{
  vec t0, t1, t2, t3, t4;
  t0 = _mm256_mul_epi32(a->v[0],*b);
  t1 = _mm256_mul_epi32(a->v[1],*b);
    t1 = _mm256_add_epi64(t1,_mm256_srli_epi64(t0,26)); t0 &= mask26;
  t2 = _mm256_mul_epi32(a->v[2],*b);
  t3 = _mm256_mul_epi32(a->v[3],*b);
  t4 = _mm256_mul_epi32(a->v[4],*b);
    t3 = _mm256_add_epi64(t3,_mm256_srli_epi64(t2,26)); t2 &= mask26;
    t0 = _mm256_add_epi64(t0,_mm256_srli_epi64(t4,25)); t4 &= mask25;
    t4 = _mm256_add_epi64(t4,_mm256_srli_epi64(t3,25)); t3 &= mask25;
    t2 = _mm256_add_epi64(t2,_mm256_srli_epi64(t1,25)); t1 &= mask25;

  r->v[0] = t0;
  r->v[1] = t1;
  r->v[2] = t2;
  r->v[3] = t3;
  r->v[4] = t4;
}

inline void gfe4x_mul(gfe4x *r, const gfe4x *a, const gfe4x *b)
{
  vec a0, a1, a2, a3, a4;
  vec b0, b1, b2, b3, b4;
  vec _2a1, _2a2, _2a3, _2a4;
  vec a0b0, a0b1, a0b2, a0b3, a0b4;
  vec a1b0, a1b1, a1b2, a1b3, a1b4;
  vec a2b0, a2b1, a2b2, a2b3, a2b4;
  vec a3b0, a3b1, a3b2, a3b3, a3b4;
  vec a4b0, a4b1, a4b2, a4b3, a4b4;
  vec t0, t1, t2, t3, t4;

  a0 = a->v[0];
  b0 = b->v[0];
    a0b0 = _mm256_mul_epu32(a0,b0);
  b1 = b->v[1];
    a0b1 = _mm256_mul_epu32(a0,b1);
  b2 = b->v[2];
    a0b2 = _mm256_mul_epu32(a0,b2);
  b3 = b->v[3];
    a0b3 = _mm256_mul_epu32(a0,b3);
  b4 = b->v[4];
    a0b4 = _mm256_mul_epu32(a0,b4);

  a1 = a->v[1];
    a1b0 = _mm256_mul_epu32(a1,b0);
      t1 = _mm256_add_epi64(a0b1,a1b0);
    a1b2 = _mm256_mul_epu32(a1,b2);
      t3 = _mm256_add_epi64(a0b3,a1b2);
  _2a1 = _mm256_add_epi64(a1,a1);
    a1b4 = _mm256_mul_epu32(_2a1,b4);
      t0 = _mm256_add_epi64(a0b0,a1b4);
    a1b1 = _mm256_mul_epu32(_2a1,b1);
      t2 = _mm256_add_epi64(a0b2,a1b1);
    a1b3 = _mm256_mul_epu32(_2a1,b3);
      t4 = _mm256_add_epi64(a0b4,a1b3);

  a2 = a->v[2];
    a2b4 = _mm256_mul_epu32(a2,b4);
      t1 = _mm256_add_epi64(t1,a2b4);
    a2b0 = _mm256_mul_epu32(a2,b0);
      t2 = _mm256_add_epi64(t2,a2b0);
    a2b1 = _mm256_mul_epu32(a2,b1);
      t3 = _mm256_add_epi64(t3,a2b1);
    a2b2 = _mm256_mul_epu32(a2,b2);
      t4 = _mm256_add_epi64(t4,a2b2);
  _2a2 = _mm256_add_epi64(a2,a2);
    a2b3 = _mm256_mul_epu32(_2a2,b3);
      t0 = _mm256_add_epi64(t0,a2b3);

  a3 = a->v[3];
    a3b0 = _mm256_mul_epu32(a3,b0);
      t3 = _mm256_add_epi64(t3,a3b0);
  _2a3 = _mm256_add_epi64(a3,a3);
    a3b2 = _mm256_mul_epu32(_2a3,b2);
      t0 = _mm256_add_epi64(t0,a3b2);
    a3b3 = _mm256_mul_epu32(_2a3,b3);
      t1 = _mm256_add_epi64(t1,a3b3);
    a3b4 = _mm256_mul_epu32(_2a3,b4);
      t2 = _mm256_add_epi64(t2,a3b4);
    a3b1 = _mm256_mul_epu32(_2a3,b1);
      t4 = _mm256_add_epi64(t4,a3b1);

  a4 = a->v[4];
    a4b4 = _mm256_mul_epu32(a4,b4);
      t3 = _mm256_add_epi64(t3,a4b4);
    a4b0 = _mm256_mul_epu32(a4,b0);
      t4 = _mm256_add_epi64(t4,a4b0);
        t4 = _mm256_add_epi64(t4,_mm256_srli_epi64(t3,25)); t3 &= mask25;
    a4b2 = _mm256_mul_epu32(a4,b2);
      t1 = _mm256_add_epi64(t1,a4b2);
  _2a4 = _mm256_add_epi64(a4,a4);
    a4b1 = _mm256_mul_epu32(_2a4,b1);
      t0 = _mm256_add_epi64(t0,a4b1);
        t0 = _mm256_add_epi64(t0,_mm256_srli_epi64(t4,25)); t4 &= mask25;
    a4b3 = _mm256_mul_epu32(_2a4,b3);
      t2 = _mm256_add_epi64(t2,a4b3);
        t1 = _mm256_add_epi64(t1,_mm256_srli_epi64(t0,26)); t0 &= mask26;
        t2 = _mm256_add_epi64(t2,_mm256_srli_epi64(t1,25)); t1 &= mask25;
        t3 = _mm256_add_epi64(t3,_mm256_srli_epi64(t2,26)); t2 &= mask26;
        t4 = _mm256_add_epi64(t4,_mm256_srli_epi64(t3,25)); t3 &= mask25;

  r->v[0] = t0;
  r->v[1] = t1;
  r->v[2] = t2;
  r->v[3] = t3;
  r->v[4] = t4;
}

inline void gfe4x_precompute(gfe4x *_2a, const gfe4x *a)
{
  int i;
  for (i = 1;i < 5;++i)
    _2a->v[i] = _mm256_add_epi64(a->v[i],a->v[i]);
}

inline void gfe4x_mulprecomputed(gfe4x *r, const gfe4x *a, const gfe4x *_2a, const gfe4x *b)
{
  vec a0, a1, a2, a3, a4;
  vec b0, b1, b2, b3, b4;
  vec _2a1, _2a2, _2a3, _2a4;
  vec a0b0, a0b1, a0b2, a0b3, a0b4;
  vec a1b0, a1b1, a1b2, a1b3, a1b4;
  vec a2b0, a2b1, a2b2, a2b3, a2b4;
  vec a3b0, a3b1, a3b2, a3b3, a3b4;
  vec a4b0, a4b1, a4b2, a4b3, a4b4;
  vec t0, t1, t2, t3, t4;

  a0 = a->v[0];
  b0 = b->v[0];
    a0b0 = _mm256_mul_epu32(a0,b0);
  b1 = b->v[1];
    a0b1 = _mm256_mul_epu32(a0,b1);
  b2 = b->v[2];
    a0b2 = _mm256_mul_epu32(a0,b2);
  b3 = b->v[3];
    a0b3 = _mm256_mul_epu32(a0,b3);
  b4 = b->v[4];
    a0b4 = _mm256_mul_epu32(a0,b4);

  a1 = a->v[1];
    a1b0 = _mm256_mul_epu32(a1,b0);
      t1 = _mm256_add_epi64(a0b1,a1b0);
    a1b2 = _mm256_mul_epu32(a1,b2);
      t3 = _mm256_add_epi64(a0b3,a1b2);
  _2a1 = _2a->v[1];
    a1b4 = _mm256_mul_epu32(_2a1,b4);
      t0 = _mm256_add_epi64(a0b0,a1b4);
    a1b1 = _mm256_mul_epu32(_2a1,b1);
      t2 = _mm256_add_epi64(a0b2,a1b1);
    a1b3 = _mm256_mul_epu32(_2a1,b3);
      t4 = _mm256_add_epi64(a0b4,a1b3);

  a2 = a->v[2];
    a2b4 = _mm256_mul_epu32(a2,b4);
      t1 = _mm256_add_epi64(t1,a2b4);
    a2b0 = _mm256_mul_epu32(a2,b0);
      t2 = _mm256_add_epi64(t2,a2b0);
    a2b1 = _mm256_mul_epu32(a2,b1);
      t3 = _mm256_add_epi64(t3,a2b1);
    a2b2 = _mm256_mul_epu32(a2,b2);
      t4 = _mm256_add_epi64(t4,a2b2);
  _2a2 = _2a->v[2];
    a2b3 = _mm256_mul_epu32(_2a2,b3);
      t0 = _mm256_add_epi64(t0,a2b3);

  a3 = a->v[3];
    a3b0 = _mm256_mul_epu32(a3,b0);
      t3 = _mm256_add_epi64(t3,a3b0);
  _2a3 = _2a->v[3];
    a3b2 = _mm256_mul_epu32(_2a3,b2);
      t0 = _mm256_add_epi64(t0,a3b2);
    a3b3 = _mm256_mul_epu32(_2a3,b3);
      t1 = _mm256_add_epi64(t1,a3b3);
    a3b4 = _mm256_mul_epu32(_2a3,b4);
      t2 = _mm256_add_epi64(t2,a3b4);
    a3b1 = _mm256_mul_epu32(_2a3,b1);
      t4 = _mm256_add_epi64(t4,a3b1);

  a4 = a->v[4];
    a4b4 = _mm256_mul_epu32(a4,b4);
      t3 = _mm256_add_epi64(t3,a4b4);
    a4b0 = _mm256_mul_epu32(a4,b0);
      t4 = _mm256_add_epi64(t4,a4b0);
        t4 = _mm256_add_epi64(t4,_mm256_srli_epi64(t3,25)); t3 &= mask25;
    a4b2 = _mm256_mul_epu32(a4,b2);
      t1 = _mm256_add_epi64(t1,a4b2);
  _2a4 = _2a->v[4];
    a4b1 = _mm256_mul_epu32(_2a4,b1);
      t0 = _mm256_add_epi64(t0,a4b1);
        t0 = _mm256_add_epi64(t0,_mm256_srli_epi64(t4,25)); t4 &= mask25;
    a4b3 = _mm256_mul_epu32(_2a4,b3);
      t2 = _mm256_add_epi64(t2,a4b3);
        t1 = _mm256_add_epi64(t1,_mm256_srli_epi64(t0,26)); t0 &= mask26;
        t2 = _mm256_add_epi64(t2,_mm256_srli_epi64(t1,25)); t1 &= mask25;
        t3 = _mm256_add_epi64(t3,_mm256_srli_epi64(t2,26)); t2 &= mask26;
        t4 = _mm256_add_epi64(t4,_mm256_srli_epi64(t3,25)); t3 &= mask25;

  r->v[0] = t0;
  r->v[1] = t1;
  r->v[2] = t2;
  r->v[3] = t3;
  r->v[4] = t4;
}

inline void gfe4x_square(gfe4x *r, const gfe4x *a)
{
  vec a0, a1, a2, a3, a4;
  vec _2a1, _2a2, _2a3, _2a4;
  vec a0a0, a0a1, a0a2, a0a3, a0a4;
  vec a1a1, a1a2, a1a3, a1a4;
  vec a2a2, a2a3, a2a4;
  vec a3a3, a3a4;
  vec a4a4;
  vec t0, t1, t2, t3, t4;

  a0 = a->v[0];
    a0a0 = _mm256_mul_epu32(a0,a0);
  a1 = a->v[1];
  _2a1 = _mm256_add_epi64(a1,a1);
    a1a1 = _mm256_mul_epu32(_2a1,a1);
    a0a1 = _mm256_mul_epu32(a0,_2a1);
  a2 = a->v[2];
    a2a2 = _mm256_mul_epu32(a2,a2);
    a1a2 = _mm256_mul_epu32(_2a1,a2);
  _2a2 = _mm256_add_epi64(a2,a2);
    a0a2 = _mm256_mul_epu32(a0,_2a2);
      t2 = _mm256_add_epi64(a0a2,a1a1);
  a3 = a->v[3];
  _2a3 = _mm256_add_epi64(a3,a3);
    a3a3 = _mm256_mul_epu32(_2a3,a3);
      t1 = _mm256_add_epi64(a0a1,a3a3);
    a0a3 = _mm256_mul_epu32(a0,_2a3);
      t3 = _mm256_add_epi64(a0a3,a1a2);
    a1a3 = _mm256_mul_epu32(_2a1,_2a3);
      t4 = _mm256_add_epi64(a2a2,a1a3);
    a2a3 = _mm256_mul_epu32(_2a2,_2a3);
      t0 = _mm256_add_epi64(a0a0,a2a3);
  a4 = a->v[4];
  _2a4 = _mm256_add_epi64(a4,a4);
    a1a4 = _mm256_mul_epu32(_2a1,_2a4);
      t0 = _mm256_add_epi64(t0,a1a4);
    a2a4 = _mm256_mul_epu32(_2a2,a4);
      t1 = _mm256_add_epi64(t1,a2a4);
        t1 = _mm256_add_epi64(t1,_mm256_srli_epi64(t0,26)); t0 &= mask26;
    a3a4 = _mm256_mul_epu32(_2a3,_2a4);
      t2 = _mm256_add_epi64(t2,a3a4);
        t2 = _mm256_add_epi64(t2,_mm256_srli_epi64(t1,25)); t1 &= mask25;
    a4a4 = _mm256_mul_epu32(a4,a4);
      t3 = _mm256_add_epi64(t3,a4a4);
        t3 = _mm256_add_epi64(t3,_mm256_srli_epi64(t2,26)); t2 &= mask26;
    a0a4 = _mm256_mul_epu32(a0,_2a4);
      t4 = _mm256_add_epi64(t4,a0a4);
        t4 = _mm256_add_epi64(t4,_mm256_srli_epi64(t3,25)); t3 &= mask25;
        t0 = _mm256_add_epi64(t0,_mm256_srli_epi64(t4,25)); t4 &= mask25;
        t1 = _mm256_add_epi64(t1,_mm256_srli_epi64(t0,26)); t0 &= mask26;

  r->v[0] = t0;
  r->v[1] = t1;
  r->v[2] = t2;
  r->v[3] = t3;
  r->v[4] = t4;
}

#define init(a0,a1,a2,a3,a4,a5,a6,a7) \
  { (a0)+(a1)*4294967296LL, \
    (a2)+(a3)*4294967296LL, \
    (a4)+(a5)*4294967296LL, \
    (a6)+(a7)*4294967296LL }
static const vec hadamardoffset[5] = {
  init(0xffffffc+1,0xffffffc+1,0xffffffc+2,0xffffffc+2,0xffffffc+2,0xffffffc+2,0xffffffc+1,0xffffffc+1)
, init(0x7fffffc+1,0x7fffffc+1,0x7fffffc+2,0x7fffffc+2,0x7fffffc+2,0x7fffffc+2,0x7fffffc+1,0x7fffffc+1)
, init(0xffffffc+1,0xffffffc+1,0xffffffc+2,0xffffffc+2,0xffffffc+2,0xffffffc+2,0xffffffc+1,0xffffffc+1)
, init(0x7fffffc+1,0x7fffffc+1,0x7fffffc+2,0x7fffffc+2,0x7fffffc+2,0x7fffffc+2,0x7fffffc+1,0x7fffffc+1)
, init(0x7fffffc+1,0x7fffffc+1,0x7fffffc+2,0x7fffffc+2,0x7fffffc+2,0x7fffffc+2,0x7fffffc+1,0x7fffffc+1)
} ;
static const vec minusplusplusminus = { -1,0,0,-1 };
static const vec plusminusminusplus = { 0,-1,-1,0 };

inline void gfe4x_hadamard(gfe4x *r,gfe4x *s)
{
  int i;

  for (i = 0;i < 5;++i) {
    vec z0123 = r->v[i] ^ _mm256_slli_epi64(s->v[i],32);
    vec z1032 = _mm256_shuffle_epi32(z0123,_MM_SHUFFLE(1,0,3,2));
    vec y0123 = _mm256_add_epi32(z1032,z0123 ^ minusplusplusminus);
    vec y0213 = _mm256_permute4x64_epi64(y0123,_MM_SHUFFLE(3,1,2,0));
    vec y2031 = _mm256_shuffle_epi32(y0213,_MM_SHUFFLE(1,0,3,2));
    vec out = _mm256_add_epi32(_mm256_add_epi32(y0213 ^ plusminusminusplus,y2031),hadamardoffset[i]);
    r->v[i] = out; /* skip mask with 4x 0xffffffff; output used only by mul_epu32 */
    s->v[i] = _mm256_srli_epi64(out,32);
  }
}

inline void gfe4x_select(gfe4x *r,const gfe4x *x,const gfe4x *y,int b)
{
  vec db = _mm256_set_epi32(-b,-b,-b,-b,-b,-b,-b,-b);
  int j;
  for(j=0;j<5;j++)
    r->v[j] = _mm256_blendv_epi8(x->v[j],y->v[j],db);
}

static const gfe aa = {{11,0,0,0,0}}; /* implicitly negated */
static const gfe bb = {{22,0,0,0,0}};
static const gfe cc = {{19,0,0,0,0}};
static const gfe dd = {{3,0,0,0,0}};
static const gfe minusone = {{0x3fffffe,0x1ffffff,0x3ffffff,0x1ffffff,0x1ffffff}};

static const vec abcd = {114,57,66,418}; /* implicitly negated */
static const vec ABCD = {833,2499,1617,561}; /* implicitly negated */

int crypto_scalarmult(unsigned char *q, const unsigned char *n, const unsigned char *p)
{
  gfe work[12];
  gfe yz,yzt,r,tr;
  int i,j;
  int bit;
  int prevbit;
  int swap;
  gfe4x input;
  gfe4x input2;
  gfe4x xyzt2;
  gfe4x xyzt3;
  gfe4x tmp;

  work[0] = minusone;
  gfe_unpack(&work[1], p);    /* xy1 */
  gfe_unpack(&work[2], p+16); /* xz1 */
  gfe_unpack(&work[3], p+32); /* xt1 */
  gfe4x_from_gfe(&input,work);
  gfe4x_precompute(&input2,&input);

  work[4] = aa;
  work[5] = bb;
  work[6] = cc;
  work[7] = dd;

  gfe_mul(&work[11], &work[ 1], &work[2]); /* xy1 * xz1 */
  gfe_mul(&work[10], &work[ 1], &work[3]); /* xy1 * xt1 */
  gfe_mul(&work[ 9], &work[ 2], &work[3]); /* xz1 * xt1 */
  gfe_mul(&work[ 8], &work[11], &work[3]); /* t3  * xt1 */

  gfe_mul(work+8,work+8,&minusone);

  gfe4x_from_gfe(&xyzt3,work + 8);
  gfe4x_from_gfe(&xyzt2,work + 4);

  prevbit = 0;
  j=2;
  for(i=31;i>=0;i--) {
    for(;j>=0;j--) {
      bit = (n[i]>>j) & 1;
      swap = bit ^ prevbit;
      prevbit = bit;

      gfe4x_hadamard(&xyzt3,&xyzt2);
      
      gfe4x_select(&tmp,&xyzt2,&xyzt3,swap);
      gfe4x_mul(&xyzt3,&xyzt3,&xyzt2);
      gfe4x_square(&xyzt2,&tmp);
      gfe4x_mulconst(&xyzt3,&xyzt3,&ABCD);
      gfe4x_mulconst(&xyzt2,&xyzt2,&ABCD);

      gfe4x_hadamard(&xyzt3,&xyzt2);

      gfe4x_square(&xyzt3,&xyzt3);
      gfe4x_square(&xyzt2,&xyzt2);
      gfe4x_mulprecomputed(&xyzt3,&input,&input2,&xyzt3);
      gfe4x_mulconst(&xyzt2,&xyzt2,&abcd);
    }
    j = 7;
  }

  gfe4x_select(&xyzt2,&xyzt2,&xyzt3,bit);
  gfe4x_to_gfe(&xyzt2,work + 4);

  gfe_mul(work+4,work+4,&minusone);

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
