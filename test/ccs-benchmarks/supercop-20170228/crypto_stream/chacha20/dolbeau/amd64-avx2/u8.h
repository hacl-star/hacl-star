/*
u8.h version $Date: 2014/09/24 12:09:52 $
D. J. Bernstein
Romain Dolbeau
Public domain.
*/

#define VEC8_ROT(a,imm) _mm256_or_si256(_mm256_slli_epi32(a,imm),_mm256_srli_epi32(a,(32-imm)))

/* implements a vector quarter round by-the-book (naive!) */
#define VEC8_QUARTERROUND_NAIVE(a,b,c,d)                                           \
  x_##a = _mm256_add_epi32(x_##a, x_##b); t_##a = _mm256_xor_si256(x_##d, x_##a); x_##d = VEC8_ROT(t_##a, 16); \
  x_##c = _mm256_add_epi32(x_##c, x_##d); t_##c = _mm256_xor_si256(x_##b, x_##c); x_##b = VEC8_ROT(t_##c, 12); \
  x_##a = _mm256_add_epi32(x_##a, x_##b); t_##a = _mm256_xor_si256(x_##d, x_##a); x_##d = VEC8_ROT(t_##a,  8); \
  x_##c = _mm256_add_epi32(x_##c, x_##d); t_##c = _mm256_xor_si256(x_##b, x_##c); x_##b = VEC8_ROT(t_##c,  7)

/* same, but replace 2 of the shift/shift/or "rotation" by byte shuffles (8 & 16) (better) */
#define VEC8_QUARTERROUND_SHUFFLE(a,b,c,d)                                \
   x_##a = _mm256_add_epi32(x_##a, x_##b); t_##a = _mm256_xor_si256(x_##d, x_##a); x_##d = _mm256_shuffle_epi8(t_##a, rot16); \
   x_##c = _mm256_add_epi32(x_##c, x_##d); t_##c = _mm256_xor_si256(x_##b, x_##c); x_##b = VEC8_ROT(t_##c, 12); \
   x_##a = _mm256_add_epi32(x_##a, x_##b); t_##a = _mm256_xor_si256(x_##d, x_##a); x_##d = _mm256_shuffle_epi8(t_##a, rot8); \
   x_##c = _mm256_add_epi32(x_##c, x_##d); t_##c = _mm256_xor_si256(x_##b, x_##c); x_##b = VEC8_ROT(t_##c,  7)

/* same, but replace 2 of the shift/shift/or "rotation" by byte & word shuffles (8 & 16) (not as good as previous) */
#define VEC8_QUARTERROUND_SHUFFLE2(a,b,c,d)                                \
  x_##a = _mm256_add_epi32(x_##a, x_##b); t_##a = _mm256_xor_si256(x_##d, x_##a); x_##d = _mm256_shufflehi_epi16(_mm256_shufflelo_epi16(t_##a,0xb1),0xb1); \
   x_##c = _mm256_add_epi32(x_##c, x_##d); t_##c = _mm256_xor_si256(x_##b, x_##c); x_##b = VEC8_ROT(t_##c, 12); \
   x_##a = _mm256_add_epi32(x_##a, x_##b); t_##a = _mm256_xor_si256(x_##d, x_##a); x_##d = _mm256_shuffle_epi8(t_##a, rot8); \
   x_##c = _mm256_add_epi32(x_##c, x_##d); t_##c = _mm256_xor_si256(x_##b, x_##c); x_##b = VEC8_ROT(t_##c,  7)

#define VEC8_QUARTERROUND(a,b,c,d) VEC8_QUARTERROUND_SHUFFLE(a,b,c,d)

/* #define VEC8_LINE1(a,b,c,d)                                             \ */
/*   x_##a = _mm256_add_epi32(x_##a, x_##b); t_##a = _mm256_xor_si256(x_##d, x_##a); x_##d = _mm256_shuffle_epi8(t_##a, rot16) */
/* #define VEC8_LINE2(a,b,c,d)                                             \ */
/*   x_##c = _mm256_add_epi32(x_##c, x_##d); t_##c = _mm256_xor_si256(x_##b, x_##c); x_##b = VEC8_ROT(t_##c, 12) */
/* #define VEC8_LINE3(a,b,c,d)                                             \ */
/*   x_##a = _mm256_add_epi32(x_##a, x_##b); t_##a = _mm256_xor_si256(x_##d, x_##a); x_##d = _mm256_shuffle_epi8(t_##a, rot8) */
/* #define VEC8_LINE4(a,b,c,d)                                             \ */
/*   x_##c = _mm256_add_epi32(x_##c, x_##d); t_##c = _mm256_xor_si256(x_##b, x_##c); x_##b = VEC8_ROT(t_##c,  7) */
/* not expliciting t_##X seems a bit faster... */
#define VEC8_LINE1(a,b,c,d)                                             \
  x_##a = _mm256_add_epi32(x_##a, x_##b); x_##d = _mm256_shuffle_epi8(_mm256_xor_si256(x_##d, x_##a), rot16)
#define VEC8_LINE2(a,b,c,d)                                             \
  x_##c = _mm256_add_epi32(x_##c, x_##d); x_##b = VEC8_ROT(_mm256_xor_si256(x_##b, x_##c), 12)
#define VEC8_LINE3(a,b,c,d)                                             \
  x_##a = _mm256_add_epi32(x_##a, x_##b); x_##d = _mm256_shuffle_epi8(_mm256_xor_si256(x_##d, x_##a), rot8)
#define VEC8_LINE4(a,b,c,d)                                             \
  x_##c = _mm256_add_epi32(x_##c, x_##d); x_##b = VEC8_ROT(_mm256_xor_si256(x_##b, x_##c),  7)

#define VEC8_ROUND_SEQ(a1,b1,c1,d1,a2,b2,c2,d2,a3,b3,c3,d3,a4,b4,c4,d4)     \
  VEC8_LINE1(a1,b1,c1,d1);                                              \
  VEC8_LINE1(a2,b2,c2,d2);                                              \
  VEC8_LINE1(a3,b3,c3,d3);                                              \
  VEC8_LINE1(a4,b4,c4,d4);                                              \
  VEC8_LINE2(a1,b1,c1,d1);                                              \
  VEC8_LINE2(a2,b2,c2,d2);                                              \
  VEC8_LINE2(a3,b3,c3,d3);                                              \
  VEC8_LINE2(a4,b4,c4,d4);                                              \
  VEC8_LINE3(a1,b1,c1,d1);                                              \
  VEC8_LINE3(a2,b2,c2,d2);                                              \
  VEC8_LINE3(a3,b3,c3,d3);                                              \
  VEC8_LINE3(a4,b4,c4,d4);                                              \
  VEC8_LINE4(a1,b1,c1,d1);                                              \
  VEC8_LINE4(a2,b2,c2,d2);                                              \
  VEC8_LINE4(a3,b3,c3,d3);                                              \
  VEC8_LINE4(a4,b4,c4,d4)

#define VEC8_ROUND_HALF(a1,b1,c1,d1,a2,b2,c2,d2,a3,b3,c3,d3,a4,b4,c4,d4)     \
  VEC8_LINE1(a1,b1,c1,d1);                                              \
  VEC8_LINE1(a2,b2,c2,d2);                                              \
  VEC8_LINE2(a1,b1,c1,d1);                                              \
  VEC8_LINE2(a2,b2,c2,d2);                                              \
  VEC8_LINE3(a1,b1,c1,d1);                                              \
  VEC8_LINE3(a2,b2,c2,d2);                                              \
  VEC8_LINE4(a1,b1,c1,d1);                                              \
  VEC8_LINE4(a2,b2,c2,d2);                                              \
  VEC8_LINE1(a3,b3,c3,d3);                                              \
  VEC8_LINE1(a4,b4,c4,d4);                                              \
  VEC8_LINE2(a3,b3,c3,d3);                                              \
  VEC8_LINE2(a4,b4,c4,d4);                                              \
  VEC8_LINE3(a3,b3,c3,d3);                                              \
  VEC8_LINE3(a4,b4,c4,d4);                                              \
  VEC8_LINE4(a3,b3,c3,d3);                                              \
  VEC8_LINE4(a4,b4,c4,d4)

#define VEC8_ROUND_HALFANDHALF(a1,b1,c1,d1,a2,b2,c2,d2,a3,b3,c3,d3,a4,b4,c4,d4) \
  VEC8_LINE1(a1,b1,c1,d1);                                              \
  VEC8_LINE1(a2,b2,c2,d2);                                              \
  VEC8_LINE2(a1,b1,c1,d1);                                              \
  VEC8_LINE2(a2,b2,c2,d2);                                              \
  VEC8_LINE1(a3,b3,c3,d3);                                              \
  VEC8_LINE1(a4,b4,c4,d4);                                              \
  VEC8_LINE2(a3,b3,c3,d3);                                              \
  VEC8_LINE2(a4,b4,c4,d4);                                              \
  VEC8_LINE3(a1,b1,c1,d1);                                              \
  VEC8_LINE3(a2,b2,c2,d2);                                              \
  VEC8_LINE4(a1,b1,c1,d1);                                              \
  VEC8_LINE4(a2,b2,c2,d2);                                              \
  VEC8_LINE3(a3,b3,c3,d3);                                              \
  VEC8_LINE3(a4,b4,c4,d4);                                              \
  VEC8_LINE4(a3,b3,c3,d3);                                              \
  VEC8_LINE4(a4,b4,c4,d4)

#define VEC8_ROUND(a1,b1,c1,d1,a2,b2,c2,d2,a3,b3,c3,d3,a4,b4,c4,d4) VEC8_ROUND_SEQ(a1,b1,c1,d1,a2,b2,c2,d2,a3,b3,c3,d3,a4,b4,c4,d4)

  if (!bytes) return;
if (bytes>=512) {
  /* constant for shuffling bytes (replacing multiple-of-8 rotates) */
  __m256i rot16 = _mm256_set_epi8(13,12,15,14,9,8,11,10,5,4,7,6,1,0,3,2,13,12,15,14,9,8,11,10,5,4,7,6,1,0,3,2);
  __m256i rot8  = _mm256_set_epi8(14,13,12,15,10,9,8,11,6,5,4,7,2,1,0,3,14,13,12,15,10,9,8,11,6,5,4,7,2,1,0,3);
  u32 in12, in13;
#if 1
  /* the naive way seems as fast (if not a bit faster) than the vector way */
__m256i x_0 = _mm256_set1_epi32(x[0]);
__m256i x_1 = _mm256_set1_epi32(x[1]);
__m256i x_2 = _mm256_set1_epi32(x[2]);
__m256i x_3 = _mm256_set1_epi32(x[3]);
__m256i x_4 = _mm256_set1_epi32(x[4]);
__m256i x_5 = _mm256_set1_epi32(x[5]);
__m256i x_6 = _mm256_set1_epi32(x[6]);
__m256i x_7 = _mm256_set1_epi32(x[7]);
__m256i x_8 = _mm256_set1_epi32(x[8]);
__m256i x_9 = _mm256_set1_epi32(x[9]);
__m256i x_10 = _mm256_set1_epi32(x[10]);
__m256i x_11 = _mm256_set1_epi32(x[11]);
 __m256i x_12;// = _mm256_set1_epi32(x[12]); /* useless */
 __m256i x_13;// = _mm256_set1_epi32(x[13]); /* useless */
__m256i x_14 = _mm256_set1_epi32(x[14]);
__m256i x_15 = _mm256_set1_epi32(x[15]);
#else
  /* element broadcast immediate for _mm_shuffle_epi32 are in order:
     0x00, 0x55, 0xaa, 0xff */
  __m256i x_0 = _mm256_loadu_si256((__m256i*)(x +  0));
  /* intra-lane shuffle (does both sides at once) */
  __m256i x_1 = _mm256_shuffle_epi32(x_0, 0x55);
  __m256i x_2 = _mm256_shuffle_epi32(x_0, 0xaa);
  __m256i x_3 = _mm256_shuffle_epi32(x_0, 0xff);
  x_0  = _mm256_shuffle_epi32(x_0, 0x00);
  /* inter-lane shuffle */
  __m256i x_4 = _mm256_permute2x128_si256(x_0, x_0, 0x11);
  __m256i x_5 = _mm256_permute2x128_si256(x_1, x_1, 0x11);
  __m256i x_6 = _mm256_permute2x128_si256(x_2, x_2, 0x11);
  __m256i x_7 = _mm256_permute2x128_si256(x_3, x_3, 0x11);
  x_0 = _mm256_permute2x128_si256(x_0, x_0, 0x00);
  x_1 = _mm256_permute2x128_si256(x_1, x_1, 0x00);
  x_2 = _mm256_permute2x128_si256(x_2, x_2, 0x00);
  x_3 = _mm256_permute2x128_si256(x_3, x_3, 0x00);
  __m256i x_8 = _mm256_loadu_si256((__m256i*)(x +  8));
  /* intra-lane shuffle (does both sides at once) */
  __m256i x_9 = _mm256_shuffle_epi32(x_8, 0x55);
  __m256i x_10 = _mm256_shuffle_epi32(x_8, 0xaa);
  __m256i x_11 = _mm256_shuffle_epi32(x_8, 0xff);
  x_8  = _mm256_shuffle_epi32(x_8, 0x00);
  /* inter-lane shuffle */
  __m256i x_12;// = _mm256_permute2x128_si256(x_8, x_8, 0x11); /* useless */
  __m256i x_13;// = _mm256_permute2x128_si256(x_9, x_9, 0x11); /* useless */
  __m256i x_14 = _mm256_permute2x128_si256(x_10, x_10, 0x11);
  __m256i x_15 = _mm256_permute2x128_si256(x_11, x_11, 0x11);
  x_8 = _mm256_permute2x128_si256(x_8, x_8, 0x00);
  x_9 = _mm256_permute2x128_si256(x_9, x_9, 0x00);
  x_10 = _mm256_permute2x128_si256(x_10, x_10, 0x00);
  x_11 = _mm256_permute2x128_si256(x_11, x_11, 0x00);
#endif
  __m256i orig0 = x_0;
  __m256i orig1 = x_1;
  __m256i orig2 = x_2;
  __m256i orig3 = x_3;
  __m256i orig4 = x_4;
  __m256i orig5 = x_5;
  __m256i orig6 = x_6;
  __m256i orig7 = x_7;
  __m256i orig8 = x_8;
  __m256i orig9 = x_9;
  __m256i orig10 = x_10;
  __m256i orig11 = x_11;
  __m256i orig12;// = x_12; /* useless */
  __m256i orig13;// = x_13; /* useless */
  __m256i orig14 = x_14;
  __m256i orig15 = x_15;
  __m256i t_0;
  __m256i t_1;
  __m256i t_2;
  __m256i t_3;
  __m256i t_4;
  __m256i t_5;
  __m256i t_6;
  __m256i t_7;
  __m256i t_8;
  __m256i t_9;
  __m256i t_10;
  __m256i t_11;
  __m256i t_12;
  __m256i t_13;
  __m256i t_14;
  __m256i t_15;

  while (bytes >= 512) {
    x_0 = orig0;
    x_1 = orig1;
    x_2 = orig2;
    x_3 = orig3;
    x_4 = orig4;
    x_5 = orig5;
    x_6 = orig6;
    x_7 = orig7;
    x_8 = orig8;
    x_9 = orig9;
    x_10 = orig10;
    x_11 = orig11;
    //x_12 = orig12; /* useless */
    //x_13 = orig13; /* useless */
    x_14 = orig14;
    x_15 = orig15;



    const __m256i addv12 = _mm256_set_epi64x(3,2,1,0);
    const __m256i addv13 = _mm256_set_epi64x(7,6,5,4);
    const __m256i permute = _mm256_set_epi32(7,6,3,2,5,4,1,0);
    __m256i t12, t13;
    in12 = x[12];
    in13 = x[13];
    u64 in1213 = ((u64)in12) | (((u64)in13) << 32);
    x_12 = _mm256_broadcastq_epi64(_mm_cvtsi64_si128(in1213));
    x_13 = _mm256_broadcastq_epi64(_mm_cvtsi64_si128(in1213));

    t12 = _mm256_add_epi64(addv12, x_12);
    t13 = _mm256_add_epi64(addv13, x_13);

    x_12 = _mm256_unpacklo_epi32(t12, t13);
    x_13 = _mm256_unpackhi_epi32(t12, t13);

    t12 = _mm256_unpacklo_epi32(x_12, x_13);
    t13 = _mm256_unpackhi_epi32(x_12, x_13);

    /* required because unpack* are intra-lane */
    x_12 = _mm256_permutevar8x32_epi32(t12, permute);
    x_13 = _mm256_permutevar8x32_epi32(t13, permute);

    orig12 = x_12;
    orig13 = x_13;

    in1213 += 8;
    
    x[12] = in1213 & 0xFFFFFFFF;
    x[13] = (in1213>>32)&0xFFFFFFFF;

    for (i = 0 ; i < ROUNDS ; i+=2) {
#if 0
      VEC8_QUARTERROUND( 0, 4, 8,12);
      VEC8_QUARTERROUND( 1, 5, 9,13);
      VEC8_QUARTERROUND( 2, 6,10,14);
      VEC8_QUARTERROUND( 3, 7,11,15);
      VEC8_QUARTERROUND( 0, 5,10,15);
      VEC8_QUARTERROUND( 1, 6,11,12);
      VEC8_QUARTERROUND( 2, 7, 8,13);
      VEC8_QUARTERROUND( 3, 4, 9,14);
#else
      VEC8_ROUND( 0, 4, 8,12, 1, 5, 9,13, 2, 6,10,14, 3, 7,11,15);
      VEC8_ROUND( 0, 5,10,15, 1, 6,11,12, 2, 7, 8,13, 3, 4, 9,14);
#endif
    }

#define ONEQUAD_TRANSPOSE(a,b,c,d)                                      \
    {                                                                   \
      __m128i t0, t1, t2, t3;                                           \
      x_##a = _mm256_add_epi32(x_##a, orig##a);                         \
      x_##b = _mm256_add_epi32(x_##b, orig##b);                         \
      x_##c = _mm256_add_epi32(x_##c, orig##c);                         \
      x_##d = _mm256_add_epi32(x_##d, orig##d);                         \
      t_##a = _mm256_unpacklo_epi32(x_##a, x_##b);                      \
      t_##b = _mm256_unpacklo_epi32(x_##c, x_##d);                      \
      t_##c = _mm256_unpackhi_epi32(x_##a, x_##b);                      \
      t_##d = _mm256_unpackhi_epi32(x_##c, x_##d);                      \
      x_##a = _mm256_unpacklo_epi64(t_##a, t_##b);                      \
      x_##b = _mm256_unpackhi_epi64(t_##a, t_##b);                      \
      x_##c = _mm256_unpacklo_epi64(t_##c, t_##d);                      \
      x_##d = _mm256_unpackhi_epi64(t_##c, t_##d);                      \
      t0 = _mm_xor_si128(_mm256_extracti128_si256(x_##a,0), _mm_loadu_si128((__m128i*)(m+0))); \
      _mm_storeu_si128((__m128i*)(out+0),t0);                            \
      t1 = _mm_xor_si128(_mm256_extracti128_si256(x_##b,0), _mm_loadu_si128((__m128i*)(m+64))); \
      _mm_storeu_si128((__m128i*)(out+64),t1);                           \
      t2 = _mm_xor_si128(_mm256_extracti128_si256(x_##c,0), _mm_loadu_si128((__m128i*)(m+128))); \
      _mm_storeu_si128((__m128i*)(out+128),t2);                          \
      t3 = _mm_xor_si128(_mm256_extracti128_si256(x_##d,0), _mm_loadu_si128((__m128i*)(m+192))); \
      _mm_storeu_si128((__m128i*)(out+192),t3);                          \
      t0 = _mm_xor_si128(_mm256_extracti128_si256(x_##a,1), _mm_loadu_si128((__m128i*)(m+256))); \
      _mm_storeu_si128((__m128i*)(out+256),t0);                          \
      t1 = _mm_xor_si128(_mm256_extracti128_si256(x_##b,1), _mm_loadu_si128((__m128i*)(m+320))); \
      _mm_storeu_si128((__m128i*)(out+320),t1);                          \
      t2 = _mm_xor_si128(_mm256_extracti128_si256(x_##c,1), _mm_loadu_si128((__m128i*)(m+384))); \
      _mm_storeu_si128((__m128i*)(out+384),t2);                          \
      t3 = _mm_xor_si128(_mm256_extracti128_si256(x_##d,1), _mm_loadu_si128((__m128i*)(m+448))); \
      _mm_storeu_si128((__m128i*)(out+448),t3);                          \
    }
    
#define ONEQUAD(a,b,c,d) ONEQUAD_TRANSPOSE(a,b,c,d)

#define ONEQUAD_UNPCK(a,b,c,d)                                          \
    {                                                                   \
      x_##a = _mm256_add_epi32(x_##a, orig##a);                         \
      x_##b = _mm256_add_epi32(x_##b, orig##b);                         \
      x_##c = _mm256_add_epi32(x_##c, orig##c);                         \
      x_##d = _mm256_add_epi32(x_##d, orig##d);                         \
      t_##a = _mm256_unpacklo_epi32(x_##a, x_##b);                      \
      t_##b = _mm256_unpacklo_epi32(x_##c, x_##d);                      \
      t_##c = _mm256_unpackhi_epi32(x_##a, x_##b);                      \
      t_##d = _mm256_unpackhi_epi32(x_##c, x_##d);                      \
      x_##a = _mm256_unpacklo_epi64(t_##a, t_##b);                      \
      x_##b = _mm256_unpackhi_epi64(t_##a, t_##b);                      \
      x_##c = _mm256_unpacklo_epi64(t_##c, t_##d);                      \
      x_##d = _mm256_unpackhi_epi64(t_##c, t_##d);                      \
    }
#define ONEOCTO(a,b,c,d,a2,b2,c2,d2)                                    \
    {                                                                   \
      ONEQUAD_UNPCK(a,b,c,d);                                           \
      ONEQUAD_UNPCK(a2,b2,c2,d2);                                       \
      t_##a  = _mm256_permute2x128_si256(x_##a, x_##a2, 0x20);          \
      t_##a2 = _mm256_permute2x128_si256(x_##a, x_##a2, 0x31);          \
      t_##b  = _mm256_permute2x128_si256(x_##b, x_##b2, 0x20);          \
      t_##b2 = _mm256_permute2x128_si256(x_##b, x_##b2, 0x31);          \
      t_##c  = _mm256_permute2x128_si256(x_##c, x_##c2, 0x20);          \
      t_##c2 = _mm256_permute2x128_si256(x_##c, x_##c2, 0x31);          \
      t_##d  = _mm256_permute2x128_si256(x_##d, x_##d2, 0x20);          \
      t_##d2 = _mm256_permute2x128_si256(x_##d, x_##d2, 0x31);          \
      t_##a  = _mm256_xor_si256(t_##a , _mm256_loadu_si256((__m256i*)(m+  0))); \
      t_##b  = _mm256_xor_si256(t_##b , _mm256_loadu_si256((__m256i*)(m+ 64))); \
      t_##c  = _mm256_xor_si256(t_##c , _mm256_loadu_si256((__m256i*)(m+128))); \
      t_##d  = _mm256_xor_si256(t_##d , _mm256_loadu_si256((__m256i*)(m+192))); \
      t_##a2 = _mm256_xor_si256(t_##a2, _mm256_loadu_si256((__m256i*)(m+256))); \
      t_##b2 = _mm256_xor_si256(t_##b2, _mm256_loadu_si256((__m256i*)(m+320))); \
      t_##c2 = _mm256_xor_si256(t_##c2, _mm256_loadu_si256((__m256i*)(m+384))); \
      t_##d2 = _mm256_xor_si256(t_##d2, _mm256_loadu_si256((__m256i*)(m+448))); \
      _mm256_storeu_si256((__m256i*)(out+  0), t_##a );                  \
      _mm256_storeu_si256((__m256i*)(out+ 64), t_##b );                  \
      _mm256_storeu_si256((__m256i*)(out+128), t_##c );                  \
      _mm256_storeu_si256((__m256i*)(out+192), t_##d );                  \
      _mm256_storeu_si256((__m256i*)(out+256), t_##a2);                  \
      _mm256_storeu_si256((__m256i*)(out+320), t_##b2);                  \
      _mm256_storeu_si256((__m256i*)(out+384), t_##c2);                  \
      _mm256_storeu_si256((__m256i*)(out+448), t_##d2);                  \
    }
    
#if 0
    ONEQUAD(0,1,2,3);
    m+=16;
    out+=16;
    ONEQUAD(4,5,6,7);
    m+=16;
    out+=16;
    ONEQUAD(8,9,10,11);
    m+=16;
    out+=16;
    ONEQUAD(12,13,14,15);
    m-=48;
    out-=48;
#else
    ONEOCTO(0,1,2,3,4,5,6,7);
    m+=32;
    out+=32;
    ONEOCTO(8,9,10,11,12,13,14,15);
    m-=32;
    out-=32;
#endif
    
#undef ONEQUAD
#undef ONEQUAD_TRANSPOSE
#undef ONEQUAD_UNPCK
#undef ONEOCTO

    bytes -= 512;
    out += 512;
    m += 512;
  }
 }
#undef VEC8_ROT
#undef VEC8_QUARTERROUND
#undef VEC8_QUARTERROUND_NAIVE
#undef VEC8_QUARTERROUND_SHUFFLE
#undef VEC8_QUARTERROUND_SHUFFLE2
#undef VEC8_LINE1
#undef VEC8_LINE2
#undef VEC8_LINE3
#undef VEC8_LINE4
#undef VEC8_ROUND
#undef VEC8_ROUND_SEQ
#undef VEC8_ROUND_HALF
#undef VEC8_ROUND_HALFANDHALF

