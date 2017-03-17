/*
u4.h version $Date: 2014/11/30 09:03:31 $
D. J. Bernstein
Romain Dolbeau
Public domain.
*/

/* I like the NEON naming convention, so just reuse the name */
typedef u64 uint64x2_t __attribute__ ((vector_size (16)));
typedef u32 uint32x4_t __attribute__ ((vector_size (16)));
typedef u16 uint16x8_t __attribute__ ((vector_size (16)));
typedef u8  uint8x16_t __attribute__ ((vector_size (16)));

#define printv(s,v)                              \
  do {                                           \
    u32 temp[4];                            \
    int i;                                       \
    __builtin_msa_st_w((uint32x4_t)v,temp,0);    \
    printf("%s: %s: ", s, #v);                   \
    for (i = 3 ; i >= 0 ; i--) {                 \
      printf("0x%08x ", temp[i]);                \
    }                                            \
    printf("\n");                                \
  } while(0)

#define VEC4_ROT(a,imm) __builtin_msa_or_v(__builtin_msa_slli_w(a,imm),__builtin_msa_srli_w(a, 32-imm))

#define VEC4_QUARTERROUND(a,b,c,d)                                \
   x_##a = __builtin_msa_addv_w(x_##a, x_##b); t_##a = __builtin_msa_xor_v(x_##d, x_##a); x_##d = VEC4_ROT(t_##a, 16); \
   x_##c = __builtin_msa_addv_w(x_##c, x_##d); t_##c = __builtin_msa_xor_v(x_##b, x_##c); x_##b = VEC4_ROT(t_##c, 12); \
   x_##a = __builtin_msa_addv_w(x_##a, x_##b); t_##a = __builtin_msa_xor_v(x_##d, x_##a); x_##d = VEC4_ROT(t_##a,  8); \
   x_##c = __builtin_msa_addv_w(x_##c, x_##d); t_##c = __builtin_msa_xor_v(x_##b, x_##c); x_##b = VEC4_ROT(t_##c,  7)

  if (!bytes) return;
if (bytes>=256) {
  u32 in12, in13;
  uint32x4_t x_0 = __builtin_msa_fill_w(x[0]);
  uint32x4_t x_1 = __builtin_msa_fill_w(x[1]);
  uint32x4_t x_2 = __builtin_msa_fill_w(x[2]);
  uint32x4_t x_3 = __builtin_msa_fill_w(x[3]);
  uint32x4_t x_4 = __builtin_msa_fill_w(x[4]);
  uint32x4_t x_5 = __builtin_msa_fill_w(x[5]);
  uint32x4_t x_6 = __builtin_msa_fill_w(x[6]);
  uint32x4_t x_7 = __builtin_msa_fill_w(x[7]);
  uint32x4_t x_8 = __builtin_msa_fill_w(x[8]);
  uint32x4_t x_9 = __builtin_msa_fill_w(x[9]);
  uint32x4_t x_10 = __builtin_msa_fill_w(x[10]);
  uint32x4_t x_11 = __builtin_msa_fill_w(x[11]);
  uint32x4_t x_12;// = __builtin_msa_fill_w(x[12]); /* useless */
  uint32x4_t x_13;// = __builtin_msa_fill_w(x[13]); /* useless */
  uint32x4_t x_14 = __builtin_msa_fill_w(x[14]);
  uint32x4_t x_15 = __builtin_msa_fill_w(x[15]);
  uint32x4_t orig0 = x_0;
  uint32x4_t orig1 = x_1;
  uint32x4_t orig2 = x_2;
  uint32x4_t orig3 = x_3;
  uint32x4_t orig4 = x_4;
  uint32x4_t orig5 = x_5;
  uint32x4_t orig6 = x_6;
  uint32x4_t orig7 = x_7;
  uint32x4_t orig8 = x_8;
  uint32x4_t orig9 = x_9;
  uint32x4_t orig10 = x_10;
  uint32x4_t orig11 = x_11;
  uint32x4_t orig12;// = x_12; /* useless */
  uint32x4_t orig13;// = x_13; /* useless */
  uint32x4_t orig14 = x_14;
  uint32x4_t orig15 = x_15;
  uint32x4_t t_0;
  uint32x4_t t_1;
  uint32x4_t t_2;
  uint32x4_t t_3;
  uint32x4_t t_4;
  uint32x4_t t_5;
  uint32x4_t t_6;
  uint32x4_t t_7;
  uint32x4_t t_8;
  uint32x4_t t_9;
  uint32x4_t t_10;
  uint32x4_t t_11;
  uint32x4_t t_12;
  uint32x4_t t_13;
  uint32x4_t t_14;
  uint32x4_t t_15;

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



    uint64x2_t addv12;
    uint64x2_t addv13;
    addv12 = __builtin_msa_insert_d(addv12,0,0);
    addv12 = __builtin_msa_insert_d(addv12,1,1);
    addv13 = __builtin_msa_insert_d(addv13,0,2);
    addv13 = __builtin_msa_insert_d(addv13,1,3);
    uint64x2_t t12, t13;
    in12 = x[12];
    in13 = x[13];
    u64 in1213 = ((u64)in12) | (((u64)in13) << 32);
    t12 = __builtin_msa_fill_d(in1213);
    t13 = __builtin_msa_fill_d(in1213);

    x_12 = (uint32x4_t)(__builtin_msa_addv_d(addv12, t12));
    x_13 = (uint32x4_t)(__builtin_msa_addv_d(addv13, t13));

    uint32x4_t t12b, t13b;

    t12b = __builtin_msa_ilvr_w(x_13, x_12);
    t13b = __builtin_msa_ilvl_w(x_13, x_12);

    x_12 = __builtin_msa_ilvr_w(t13b, t12b);
    x_13 = __builtin_msa_ilvl_w(t13b, t12b);

    orig12 = x_12;
    orig13 = x_13;

    in1213 += 4;
    
    x[12] = in1213 & 0xFFFFFFFF;
    x[13] = (in1213>>32)&0xFFFFFFFF;

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
      uint32x4_t t0, t1, t2, t3;                                        \
      x_##a = __builtin_msa_addv_w(x_##a, orig##a);                    \
      x_##b = __builtin_msa_addv_w(x_##b, orig##b);                    \
      x_##c = __builtin_msa_addv_w(x_##c, orig##c);                    \
      x_##d = __builtin_msa_addv_w(x_##d, orig##d);                    \
      t_##a = __builtin_msa_ilvr_w(x_##b, x_##a);                       \
      t_##b = __builtin_msa_ilvr_w(x_##d, x_##c);                       \
      t_##c = __builtin_msa_ilvl_w(x_##b, x_##a);                       \
      t_##d = __builtin_msa_ilvl_w(x_##d, x_##c);                       \
      x_##a = __builtin_msa_ilvr_d(t_##b, t_##a);                       \
      x_##b = __builtin_msa_ilvl_d(t_##b, t_##a);                       \
      x_##c = __builtin_msa_ilvr_d(t_##d, t_##c);                       \
      x_##d = __builtin_msa_ilvl_d(t_##d, t_##c);                       \
      t0 = __builtin_msa_xor_v(x_##a, __builtin_msa_ld_w(m,0));         \
      __builtin_msa_st_w(t0, out,0);                                    \
      t1 = __builtin_msa_xor_v(x_##b, __builtin_msa_ld_w(m,64));        \
      __builtin_msa_st_w(t1, out,64);                                   \
      t2 = __builtin_msa_xor_v(x_##c, __builtin_msa_ld_w(m,128));       \
      __builtin_msa_st_w(t2, out,128);                                  \
      t3 = __builtin_msa_xor_v(x_##d, __builtin_msa_ld_w(m,192));       \
      __builtin_msa_st_w(t3, out,192);                                  \
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
