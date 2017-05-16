/*
u16.h version $Date: 2016/04/06 11:58:52 $
D. J. Bernstein
Romain Dolbeau
Public domain.
*/

#define VEC16_ROT(a,imm) _mm512_rol_epi32(a, imm)

#define VEC16_LINE1(a,b,c,d)                                             \
  x_##a = _mm512_add_epi32(x_##a, x_##b); x_##d = VEC16_ROT(_mm512_xor_si512(x_##d, x_##a), 16)
#define VEC16_LINE2(a,b,c,d)                                             \
  x_##c = _mm512_add_epi32(x_##c, x_##d); x_##b = VEC16_ROT(_mm512_xor_si512(x_##b, x_##c), 12)
#define VEC16_LINE3(a,b,c,d)                                             \
  x_##a = _mm512_add_epi32(x_##a, x_##b); x_##d = VEC16_ROT(_mm512_xor_si512(x_##d, x_##a),  8)
#define VEC16_LINE4(a,b,c,d)                                             \
  x_##c = _mm512_add_epi32(x_##c, x_##d); x_##b = VEC16_ROT(_mm512_xor_si512(x_##b, x_##c),  7)

#define VEC16_ROUND_SEQ(a1,b1,c1,d1,a2,b2,c2,d2,a3,b3,c3,d3,a4,b4,c4,d4)     \
  VEC16_LINE1(a1,b1,c1,d1);                                              \
  VEC16_LINE1(a2,b2,c2,d2);                                              \
  VEC16_LINE1(a3,b3,c3,d3);                                              \
  VEC16_LINE1(a4,b4,c4,d4);                                              \
  VEC16_LINE2(a1,b1,c1,d1);                                              \
  VEC16_LINE2(a2,b2,c2,d2);                                              \
  VEC16_LINE2(a3,b3,c3,d3);                                              \
  VEC16_LINE2(a4,b4,c4,d4);                                              \
  VEC16_LINE3(a1,b1,c1,d1);                                              \
  VEC16_LINE3(a2,b2,c2,d2);                                              \
  VEC16_LINE3(a3,b3,c3,d3);                                              \
  VEC16_LINE3(a4,b4,c4,d4);                                              \
  VEC16_LINE4(a1,b1,c1,d1);                                              \
  VEC16_LINE4(a2,b2,c2,d2);                                              \
  VEC16_LINE4(a3,b3,c3,d3);                                              \
  VEC16_LINE4(a4,b4,c4,d4)

#define VEC16_ROUND(a1,b1,c1,d1,a2,b2,c2,d2,a3,b3,c3,d3,a4,b4,c4,d4) VEC16_ROUND_SEQ(a1,b1,c1,d1,a2,b2,c2,d2,a3,b3,c3,d3,a4,b4,c4,d4)

  if (!bytes) return;
if (bytes>=1024) {
  /* constant for shuffling bytes (replacing multiple-of-8 rotates) */
  u32 in12, in13;
  /* the naive way seems as fast (if not a bit faster) than the vector way */
  __m512i x_0 = _mm512_set1_epi32(x[0]);
  __m512i x_1 = _mm512_set1_epi32(x[1]);
  __m512i x_2 = _mm512_set1_epi32(x[2]);
  __m512i x_3 = _mm512_set1_epi32(x[3]);
  __m512i x_4 = _mm512_set1_epi32(x[4]);
  __m512i x_5 = _mm512_set1_epi32(x[5]);
  __m512i x_6 = _mm512_set1_epi32(x[6]);
  __m512i x_7 = _mm512_set1_epi32(x[7]);
  __m512i x_8 = _mm512_set1_epi32(x[8]);
  __m512i x_9 = _mm512_set1_epi32(x[9]);
  __m512i x_10 = _mm512_set1_epi32(x[10]);
  __m512i x_11 = _mm512_set1_epi32(x[11]);
  __m512i x_12;// = _mm512_set1_epi32(x[12]); /* useless */
  __m512i x_13;// = _mm512_set1_epi32(x[13]); /* useless */
  __m512i x_14 = _mm512_set1_epi32(x[14]);
  __m512i x_15 = _mm512_set1_epi32(x[15]);
  __m512i orig0 = x_0;
  __m512i orig1 = x_1;
  __m512i orig2 = x_2;
  __m512i orig3 = x_3;
  __m512i orig4 = x_4;
  __m512i orig5 = x_5;
  __m512i orig6 = x_6;
  __m512i orig7 = x_7;
  __m512i orig8 = x_8;
  __m512i orig9 = x_9;
  __m512i orig10 = x_10;
  __m512i orig11 = x_11;
  __m512i orig12;// = x_12; /* useless */
  __m512i orig13;// = x_13; /* useless */
  __m512i orig14 = x_14;
  __m512i orig15 = x_15;
  __m512i t_0;
  __m512i t_1;
  __m512i t_2;
  __m512i t_3;
  __m512i t_4;
  __m512i t_5;
  __m512i t_6;
  __m512i t_7;
  __m512i t_8;
  __m512i t_9;
  __m512i t_10;
  __m512i t_11;
  __m512i t_12;
  __m512i t_13;
  __m512i t_14;
  __m512i t_15;

  while (bytes >= 1024) {
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

    const __m512i permute = _mm512_set_epi64(7,5,3,1,6,4,2,0);
    const __m512i addv12 = _mm512_set_epi64(7,6,5,4,3,2,1,0);
    const __m512i addv13 = _mm512_set_epi64(15,14,13,12,11,10,9,8);
    __m512i t12, t13;
    in12 = x[12];
    in13 = x[13]; // see arrays above for the address translation
    u64 in1213 = ((u64)in12) | (((u64)in13) << 32);

    x_12 = _mm512_broadcastq_epi64(_mm_cvtsi64_si128(in1213));
    x_13 = _mm512_broadcastq_epi64(_mm_cvtsi64_si128(in1213));
    t12 = _mm512_add_epi64(addv12, x_12);
    t13 = _mm512_add_epi64(addv13, x_13);
    x_12 = _mm512_unpacklo_epi32(t12, t13);
    x_13 = _mm512_unpackhi_epi32(t12, t13);
    t12 = _mm512_unpacklo_epi32(x_12, x_13);
    t13 = _mm512_unpackhi_epi32(x_12, x_13);
    x_12 = _mm512_permutexvar_epi64(permute, t12);
    x_13 = _mm512_permutexvar_epi64(permute, t13);

    orig12 = x_12;
    orig13 = x_13;

    in1213 += 16;
    
    x[12] = in1213 & 0xFFFFFFFF;
    x[13] = (in1213>>32)&0xFFFFFFFF;

    for (i = 0 ; i < ROUNDS ; i+=2) {
      VEC16_ROUND( 0, 4, 8,12, 1, 5, 9,13, 2, 6,10,14, 3, 7,11,15);
      VEC16_ROUND( 0, 5,10,15, 1, 6,11,12, 2, 7, 8,13, 3, 4, 9,14);
    }
    
    __m512i gvv = _mm512_set_epi64(776,768,520,512,264,256,8,0);
    /* same principle, but doesn't break 512-bits block in 128-bits chunks.
       Uses gather & scatter operation instead */
#define ONEQUAD_TRANSPOSE_SCATTERGATHER(a,b,c,d)                        \
    {                                                                   \
      __m512i t0, t1, t2, t3;                                           \
      x_##a = _mm512_add_epi32(x_##a, orig##a);                           \
      x_##b = _mm512_add_epi32(x_##b, orig##b);                           \
      x_##c = _mm512_add_epi32(x_##c, orig##c);                           \
      x_##d = _mm512_add_epi32(x_##d, orig##d);                           \
      t_##a = _mm512_unpacklo_epi32(x_##a, x_##b);                         \
      t_##b = _mm512_unpacklo_epi32(x_##c, x_##d);                         \
      t_##c = _mm512_unpackhi_epi32(x_##a, x_##b);                         \
      t_##d = _mm512_unpackhi_epi32(x_##c, x_##d);                         \
      x_##a = _mm512_unpacklo_epi64(t_##a, t_##b);                         \
      x_##b = _mm512_unpackhi_epi64(t_##a, t_##b);                         \
      x_##c = _mm512_unpacklo_epi64(t_##c, t_##d);                         \
      x_##d = _mm512_unpackhi_epi64(t_##c, t_##d);                         \
      t0 = _mm512_xor_si512(x_##a, _mm512_i64gather_epi64(gvv, (const long long*)(m+  0), 1)); \
      t1 = _mm512_xor_si512(x_##b, _mm512_i64gather_epi64(gvv, (const long long*)(m+ 64), 1)); \
      t2 = _mm512_xor_si512(x_##c, _mm512_i64gather_epi64(gvv, (const long long*)(m+128), 1)); \
      t3 = _mm512_xor_si512(x_##d, _mm512_i64gather_epi64(gvv, (const long long*)(m+192), 1)); \
      _mm512_i64scatter_epi64((long long*)(out+  0), gvv, t0, 1);                     \
      _mm512_i64scatter_epi64((long long*)(out+ 64), gvv, t1, 1);                     \
      _mm512_i64scatter_epi64((long long*)(out+128), gvv, t2, 1);                     \
      _mm512_i64scatter_epi64((long long*)(out+192), gvv, t3, 1);                     \
    }
#define ONEQUAD(a,b,c,d) ONEQUAD_TRANSPOSE_SCATTERGATHER(a,b,c,d)

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

#undef ONEQUAD
#undef ONEQUAD_TRANSPOSE
#undef ONEQUAD_TRANSPOSE_SCATTERGATHER

    bytes -= 1024;
    out += 1024;
    m += 1024;
  }
 }
#undef VEC16_ROT
#undef VEC16_LINE1
#undef VEC16_LINE2
#undef VEC16_LINE3
#undef VEC16_LINE4
#undef VEC16_ROUND
#undef VEC16_ROUND_SEQ
