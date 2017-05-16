/*
u4.h version $Date: 2014/11/30 11:50:07 $
D. J. Bernstein
Romain Dolbeau
Public domain.
*/

/* WARNING: this is all wrong if "m" or "out" are not 16-bytes aligned */

#define printv(s,v)                                     \
  do {                                                  \
    u32 temp[4] __attribute__ ((aligned(16)));     \
    int i;                                              \
    vec_st((vector unsigned int)v,0,temp);              \
    printf("%s: %s: ", s, #v);                          \
    for (i = 3 ; i >= 0 ; i--) {                        \
      printf("0x%08x ", temp[i]);                       \
    }                                                   \
    printf("\n");                                       \
  } while(0)

#define VEC4_ROT(a, imm) vec_vrlw(a,vec_splats((const unsigned int)imm))

#define VEC4_QUARTERROUND(a,b,c,d)                                \
   x_##a = vec_add(x_##a, x_##b); t_##a = vec_xor(x_##d, x_##a); x_##d = VEC4_ROT(t_##a, 16); \
   x_##c = vec_add(x_##c, x_##d); t_##c = vec_xor(x_##b, x_##c); x_##b = VEC4_ROT(t_##c, 12); \
   x_##a = vec_add(x_##a, x_##b); t_##a = vec_xor(x_##d, x_##a); x_##d = VEC4_ROT(t_##a,  8); \
   x_##c = vec_add(x_##c, x_##d); t_##c = vec_xor(x_##b, x_##c); x_##b = VEC4_ROT(t_##c,  7)

  if (!bytes) return;
if (bytes>=256) {
  u32 in12, in13;
  const vector unsigned char br = (const vector unsigned char){3,2,1,0,7,6,5,4,11,10,9,8,15,14,13,12};
  vector unsigned int x_0 = vec_splats((const unsigned int)(x[0]));
  vector unsigned int x_1 = vec_splats((const unsigned int)(x[1]));
  vector unsigned int x_2 = vec_splats((const unsigned int)(x[2]));
  vector unsigned int x_3 = vec_splats((const unsigned int)(x[3]));
  vector unsigned int x_4 = vec_splats((const unsigned int)(x[4]));
  vector unsigned int x_5 = vec_splats((const unsigned int)(x[5]));
  vector unsigned int x_6 = vec_splats((const unsigned int)(x[6]));
  vector unsigned int x_7 = vec_splats((const unsigned int)(x[7]));
  vector unsigned int x_8 = vec_splats((const unsigned int)(x[8]));
  vector unsigned int x_9 = vec_splats((const unsigned int)(x[9]));
  vector unsigned int x_10 = vec_splats((const unsigned int)(x[10]));
  vector unsigned int x_11 = vec_splats((const unsigned int)(x[11]));
  vector unsigned int x_12;// = vec_splats((const unsigned int)(x[12])); /* useless */
  vector unsigned int x_13;// = vec_splats((const unsigned int)(x[13])); /* useless */
  vector unsigned int x_14 = vec_splats((const unsigned int)(x[14]));
  vector unsigned int x_15 = vec_splats((const unsigned int)(x[15]));
  vector unsigned int orig0 = x_0;
  vector unsigned int orig1 = x_1;
  vector unsigned int orig2 = x_2;
  vector unsigned int orig3 = x_3;
  vector unsigned int orig4 = x_4;
  vector unsigned int orig5 = x_5;
  vector unsigned int orig6 = x_6;
  vector unsigned int orig7 = x_7;
  vector unsigned int orig8 = x_8;
  vector unsigned int orig9 = x_9;
  vector unsigned int orig10 = x_10;
  vector unsigned int orig11 = x_11;
  vector unsigned int orig12;// = x_12; /* useless */
  vector unsigned int orig13;// = x_13; /* useless */
  vector unsigned int orig14 = x_14;
  vector unsigned int orig15 = x_15;
  vector unsigned int t_0;
  vector unsigned int t_1;
  vector unsigned int t_2;
  vector unsigned int t_3;
  vector unsigned int t_4;
  vector unsigned int t_5;
  vector unsigned int t_6;
  vector unsigned int t_7;
  vector unsigned int t_8;
  vector unsigned int t_9;
  vector unsigned int t_10;
  vector unsigned int t_11;
  vector unsigned int t_12;
  vector unsigned int t_13;
  vector unsigned int t_14;
  vector unsigned int t_15;

  while (bytes >= 256) {
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

/*     in12 = __builtin_bswap32(x[12]); */
/*     in13 = __builtin_bswap32(x[13]); */
    in12 = (x[12]);
    in13 = (x[13]);
    u64 in1213 = ((u64)in12) | (((u64)in13) << 32);
    x_12 = (vector unsigned int)
      { (unsigned int)(in1213+0)&0xFFFFFFFF,
        (unsigned int)(in1213+1)&0xFFFFFFFF,
        (unsigned int)(in1213+2)&0xFFFFFFFF,
        (unsigned int)(in1213+3)&0xFFFFFFFF };
    x_13 = (vector unsigned int)
      { (unsigned int)((in1213+0)>>32)&0xFFFFFFFF,
        (unsigned int)((in1213+1)>>32)&0xFFFFFFFF,
        (unsigned int)((in1213+2)>>32)&0xFFFFFFFF,
        (unsigned int)((in1213+3)>>32)&0xFFFFFFFF };

    orig12 = x_12;
    orig13 = x_13;
    
    in1213 += 4;
    
/*     x[12] = __builtin_bswap32(in1213 & 0xFFFFFFFF); */
/*     x[13] = __builtin_bswap32((in1213>>32)&0xFFFFFFFF); */
    x[12] = (in1213 & 0xFFFFFFFF);
    x[13] = ((in1213>>32)&0xFFFFFFFF);


    for (i = 0 ; i < ROUNDS ; i+=2) {
      VEC4_QUARTERROUND( 0, 4, 8,12);
      VEC4_QUARTERROUND( 1, 5, 9,13);
      VEC4_QUARTERROUND( 2, 6,10,14);
      VEC4_QUARTERROUND( 3, 7,11,15);
      VEC4_QUARTERROUND( 0, 5,10,15);
      VEC4_QUARTERROUND( 1, 6,11,12);
      VEC4_QUARTERROUND( 2, 7, 8,13);
      VEC4_QUARTERROUND( 3, 4, 9,14);
    }
    
#define ONEQUAD_TRANSPOSE(a,b,c,d)                                      \
    {                                                                   \
      vector unsigned int t0, t1, t2, t3;                               \
      x_##a = vec_add(x_##a, orig##a);                                  \
      x_##b = vec_add(x_##b, orig##b);                                  \
      x_##c = vec_add(x_##c, orig##c);                                  \
      x_##d = vec_add(x_##d, orig##d);                                  \
      t_##a = vec_mergeh(x_##a, x_##c);                                 \
      t_##b = vec_mergel(x_##a, x_##c);                                 \
      t_##c = vec_mergeh(x_##b, x_##d);                                 \
      t_##d = vec_mergel(x_##b, x_##d);                                 \
      x_##a = vec_mergeh(t_##a, t_##c);                                 \
      x_##b = vec_mergel(t_##a, t_##c);                                 \
      x_##c = vec_mergeh(t_##b, t_##d);                                 \
      x_##d = vec_mergel(t_##b, t_##d);                                 \
      t_##a = vec_ld(  0, (const unsigned int*)m);                      \
      t0 = vec_xor(vec_perm(x_##a,x_##a,br),t_##a);                     \
      vec_st(t0,   0, (unsigned int *)out);                             \
      t_##b = vec_ld( 64, (const unsigned int*)m);                      \
      t1 = vec_xor(vec_perm(x_##b,x_##b,br),t_##b);                     \
      vec_st(t1,  64, (unsigned int *)out);                             \
      t_##c = vec_ld(128, (const unsigned int*)m);                      \
      t2 = vec_xor(vec_perm(x_##c,x_##c,br),t_##c);                     \
      vec_st(t2, 128, (unsigned int *)out);                             \
      t_##d = vec_ld(192, (const unsigned int*)m);                      \
      t3 = vec_xor(vec_perm(x_##d,x_##d,br),t_##d);                     \
      vec_st(t3, 192, (unsigned int *)out);                             \
    }
    
#define ONEQUAD(a,b,c,d) ONEQUAD_TRANSPOSE(a,b,c,d)

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

    bytes -= 256;
    out += 256;
    m += 256;
  }
 }
#undef VEC4_ROT
#undef VEC4_QUARTERROUND
