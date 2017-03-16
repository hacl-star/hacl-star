#include "Chacha20_vec.h"

inline static void Hacl_Impl_Chacha20_state_state_incr(vec *k)
{
  vec k12 = k[12];
  k[12] = vec_add(k12,eights);
}

inline static void Hacl_Impl_Chacha20_state_state_to_key(vec *k)
{
  vec k01l = vec_interleave32_low(k[0],k[1]);
  vec k23l = vec_interleave32_low(k[2],k[3]);
  vec k45l = vec_interleave32_low(k[4],k[5]);
  vec k67l = vec_interleave32_low(k[6],k[7]);
  vec k89l = vec_interleave32_low(k[8],k[9]);
  vec k1011l = vec_interleave32_low(k[10],k[11]);
  vec k1213l = vec_interleave32_low(k[12],k[13]);
  vec k1415l = vec_interleave32_low(k[14],k[15]);

  vec k03_1 = vec_interleave64_low(k01l,k23l);
  vec k47_1 = vec_interleave64_low(k45l,k67l);
  vec k07_0 = vec_choose_128(k03_1,k47_1,0,2);
  vec k07_4 = vec_choose_128(k03_1,k47_1,1,3);


  vec k03_2 = vec_interleave64_high(k01l,k23l);
  vec k47_2 = vec_interleave64_high(k45l,k67l);
  vec k07_1 = vec_choose_128(k03_2,k47_2,0,2);
  vec k07_5 = vec_choose_128(k03_2,k47_2,1,3);

  vec k811_1 = vec_interleave64_low(k89l,k1011l);
  vec k1215_1 = vec_interleave64_low(k1213l,k1415l);
  vec k815_0 = vec_choose_128(k811_1,k1215_1,0,2);
  vec k815_4 = vec_choose_128(k811_1,k1215_1,1,3);

  vec k811_2 = vec_interleave64_high(k89l,k1011l);
  vec k1215_2 = vec_interleave64_high(k1213l,k1415l);
  vec k815_1 = vec_choose_128(k811_2,k1215_2,0,2);
  vec k815_5 = vec_choose_128(k811_2,k1215_2,1,3);

  vec k01h = vec_interleave32_high(k[0],k[1]);
  vec k23h = vec_interleave32_high(k[2],k[3]);
  vec k45h = vec_interleave32_high(k[4],k[5]);
  vec k67h = vec_interleave32_high(k[6],k[7]);
  vec k89h = vec_interleave32_high(k[8],k[9]);
  vec k1011h = vec_interleave32_high(k[10],k[11]);
  vec k1213h = vec_interleave32_high(k[12],k[13]);
  vec k1415h = vec_interleave32_high(k[14],k[15]);

  vec k03_3 = vec_interleave64_low(k01h,k23h);
  vec k47_3 = vec_interleave64_low(k45h,k67h);
  vec k07_2 = vec_choose_128(k03_3,k47_3,0,2);
  vec k07_6 = vec_choose_128(k03_3,k47_3,1,3);

  vec k03_4 = vec_interleave64_high(k01h,k23h);
  vec k47_4 = vec_interleave64_high(k45h,k67h);
  vec k07_3 = vec_choose_128(k03_4,k47_4,0,2);
  vec k07_7 = vec_choose_128(k03_4,k47_4,1,3);

  vec k811_3 = vec_interleave64_low(k89h,k1011h);
  vec k1215_3 = vec_interleave64_low(k1213h,k1415h);
  vec k815_2 = vec_choose_128(k811_3,k1215_3,0,2);
  vec k815_6 = vec_choose_128(k811_3,k1215_3,1,3);

  vec k811_4 = vec_interleave64_high(k89h,k1011h);
  vec k1215_4 = vec_interleave64_high(k1213h,k1415h);
  vec k815_3 = vec_choose_128(k811_4,k1215_4,0,2);
  vec k815_7 = vec_choose_128(k811_4,k1215_4,1,3);


  k[0] = k07_0;
  k[1] = k815_0;

  k[2] = k07_1;
  k[3] = k815_1;

  k[4] = k07_2;
  k[5] = k815_2;

  k[6] = k07_3;
  k[7] = k815_3;

  k[8] = k07_4;
  k[9] = k815_4;

  k[10] = k07_5;
  k[11] = k815_5;

  k[12] = k07_6;
  k[13] = k815_6;

  k[14] = k07_7;
  k[15] = k815_7;

  
  /*
  uint32_t buf0[8];
  uint32_t buf1[8];
  uint32_t buf2[8];
  uint32_t buf3[8];
  uint32_t buf4[8];
  uint32_t buf5[8];
  uint32_t buf6[8];
  uint32_t buf7[8];
  uint32_t buf8[8];
  uint32_t buf9[8];
  uint32_t buf10[8];
  uint32_t buf11[8];
  uint32_t buf12[8];
  uint32_t buf13[8];
  uint32_t buf14[8];
  uint32_t buf15[8];
  vec_store_le((uint8_t*)buf0,k[0]);
  vec_store_le((uint8_t*)buf1,k[1]);
  vec_store_le((uint8_t*)buf2,k[2]);
  vec_store_le((uint8_t*)buf3,k[3]);
  vec_store_le((uint8_t*)buf4,k[4]);
  vec_store_le((uint8_t*)buf5,k[5]);
  vec_store_le((uint8_t*)buf6,k[6]);
  vec_store_le((uint8_t*)buf7,k[7]);
  vec_store_le((uint8_t*)buf8,k[8]);
  vec_store_le((uint8_t*)buf9,k[9]);
  vec_store_le((uint8_t*)buf10,k[10]);
  vec_store_le((uint8_t*)buf11,k[11]);
  vec_store_le((uint8_t*)buf12,k[12]);
  vec_store_le((uint8_t*)buf13,k[13]);
  vec_store_le((uint8_t*)buf14,k[14]);
  vec_store_le((uint8_t*)buf15,k[15]);
  for (int i = 0; i < 8; i++) {
    k[2*i] = vec_load_32x8(buf0[i],buf1[i],buf2[i],buf3[i],
		         buf4[i],buf5[i],buf6[i],buf7[i]);
    k[2*i+1] = vec_load_32x8(buf8[i],buf9[i],buf10[i],buf11[i],
			   buf12[i],buf13[i],buf14[i],buf15[i]);
  }
  */
}

inline static void Hacl_Impl_Chacha20_state_state_to_key_block(uint8_t *stream_block, vec *k)
{
  Hacl_Impl_Chacha20_state_state_to_key(k);
  for (int i = 0; i < 16; i++) 
    vec_store_le(stream_block + (i*32),k[i]);
}

inline static void
Hacl_Impl_Chacha20_state_state_setup(vec *st, uint8_t *k, uint8_t *n, uint32_t c)
{
  st[0] = vec_load_32((uint32_t )0x61707865);
  st[1] = vec_load_32((uint32_t )0x3320646e);
  st[2] = vec_load_32((uint32_t )0x79622d32);
  st[3] = vec_load_32((uint32_t )0x6b206574);
  uint32_t* ki = (uint32_t*) k;
  uint32_t* ni = (uint32_t*) n;
  for (int i = 0; i < 8; i++)
    st[4+i] = vec_load_32(ki[i]);
  st[12] = vec_load_32x8(c,c+1,c+2,c+3,c+4,c+5,c+6,c+7);
  for (int i = 0; i < 3; i++)
    st[13+i] = vec_load_32(ni[i]);
}

inline static void
Hacl_Impl_Chacha20_vec_line(vec *st, uint32_t a, uint32_t b, uint32_t d, uint32_t s)
{
  vec sa0 = st[a];
  vec sb = st[b];
  vec sd0 = st[d];
  vec sa = vec_add(sa0, sb);
  vec sd = vec_rotate_left(vec_xor(sd0, sa), s);
  st[a] = sa;
  st[d] = sd;
}

inline static void Hacl_Impl_Chacha20_vec_column_round(vec *st)
{
  Hacl_Impl_Chacha20_vec_line(st, 0, 4, 12, 16);
  Hacl_Impl_Chacha20_vec_line(st, 1, 5, 13, 16);
  Hacl_Impl_Chacha20_vec_line(st, 2, 6, 14, 16);
  Hacl_Impl_Chacha20_vec_line(st, 3, 7, 15, 16);

  Hacl_Impl_Chacha20_vec_line(st, 8, 12, 4, 12);
  Hacl_Impl_Chacha20_vec_line(st, 9, 13, 5, 12);
  Hacl_Impl_Chacha20_vec_line(st, 10,14, 6, 12);
  Hacl_Impl_Chacha20_vec_line(st, 11,15, 7, 12);

  Hacl_Impl_Chacha20_vec_line(st, 0, 4, 12, 8);
  Hacl_Impl_Chacha20_vec_line(st, 1, 5, 13, 8);
  Hacl_Impl_Chacha20_vec_line(st, 2, 6, 14, 8);
  Hacl_Impl_Chacha20_vec_line(st, 3, 7, 15, 8);

  Hacl_Impl_Chacha20_vec_line(st, 8, 12, 4, 7);
  Hacl_Impl_Chacha20_vec_line(st, 9, 13, 5, 7);
  Hacl_Impl_Chacha20_vec_line(st, 10,14, 6, 7);
  Hacl_Impl_Chacha20_vec_line(st, 11,15, 7, 7);
  return;
}

inline static void Hacl_Impl_Chacha20_vec_diagonal_round(vec *st)
{
  Hacl_Impl_Chacha20_vec_line(st, 0, 5, 15, 16);
  Hacl_Impl_Chacha20_vec_line(st, 1, 6, 12, 16);
  Hacl_Impl_Chacha20_vec_line(st, 2, 7, 13, 16);
  Hacl_Impl_Chacha20_vec_line(st, 3, 4, 14, 16);

  Hacl_Impl_Chacha20_vec_line(st, 10, 15, 5, 12);
  Hacl_Impl_Chacha20_vec_line(st, 11, 12, 6, 12);
  Hacl_Impl_Chacha20_vec_line(st, 8,  13, 7, 12);
  Hacl_Impl_Chacha20_vec_line(st, 9,  14, 4, 12);

  Hacl_Impl_Chacha20_vec_line(st, 0, 5, 15, 8);
  Hacl_Impl_Chacha20_vec_line(st, 1, 6, 12, 8);
  Hacl_Impl_Chacha20_vec_line(st, 2, 7, 13, 8);
  Hacl_Impl_Chacha20_vec_line(st, 3, 4, 14, 8);

  Hacl_Impl_Chacha20_vec_line(st, 10, 15, 5, 7);
  Hacl_Impl_Chacha20_vec_line(st, 11, 12, 6, 7);
  Hacl_Impl_Chacha20_vec_line(st, 8,  13, 7, 7);
  Hacl_Impl_Chacha20_vec_line(st, 9,  14, 4, 7);
  return;
}

inline static void Hacl_Impl_Chacha20_vec_double_round(vec *st)
{
  Hacl_Impl_Chacha20_vec_column_round(st);
  Hacl_Impl_Chacha20_vec_diagonal_round(st);
}

inline static void Hacl_Impl_Chacha20_vec_sum_states(vec *st_, vec *st)
{
  for (int i = 0; i < 16; i++)
    st_[i] = vec_add(st_[i],st[i]);
}

inline static void Hacl_Impl_Chacha20_vec_copy_state(vec *st_, vec *st)
{
  for (int i = 0; i < 16; i++)
    st_[i] = st[i];
}

inline static void Hacl_Impl_Chacha20_vec_chacha20_core(vec *k, vec *st)
{
  Hacl_Impl_Chacha20_vec_copy_state(k, st);
  rounds(k);
  Hacl_Impl_Chacha20_vec_sum_states(k, st);
  /*
  printf("State after core:\n");
  for (int i = 0 ; i < 4; i ++) {
    printf("row %d: ",i);
    for (int j = 0; j < 4; j++) {
      printf("%02X ",st[i*4 + j].v[0]);
    }
    printf("\n");
  }
  */
  return;
}

inline static void Hacl_Impl_Chacha20_vec_chacha20_block(uint8_t *stream_block, vec *st)
{
  vec k[16];
  for (uintmax_t _i = 0; _i < (uint32_t )16; ++_i)
    k[_i] = zero;
  Hacl_Impl_Chacha20_vec_chacha20_core(k, st);
  Hacl_Impl_Chacha20_state_state_to_key_block(stream_block, k);
}

static void
Hacl_Impl_Chacha20_vec_update_last(uint8_t *output, uint8_t *plain, uint32_t len, vec *st)
{
  uint8_t block[8 * 64];
  memset(block, 0, 8 * 64);
  Hacl_Impl_Chacha20_vec_chacha20_block(block, st);
  uint8_t *mask = block;
  xor_bytes(output, plain, mask, len);
}

static void Hacl_Impl_Chacha20_vec_xor_block(uint8_t *output, uint8_t *plain, vec *st)
{
  Hacl_Impl_Chacha20_state_state_to_key(st);
  /*
  printf("Key before xor:\n");
  for (int i = 0 ; i < 4; i ++) {
    printf("row %d: ",i);
    for (int j = 0; j < 4; j++) {
      if (i > 2) printf("%02X ",st[1].v[4*(i-2) + j]);
      else printf("%02X ",st[0].v[4*i + j]);
    }
    printf("\n");
  }
  */
  for (int i = 0; i < 16; i++) {
    vec p = vec_load_le(plain + (i*32));
    vec o = vec_xor(p,st[i]);
    vec_store_le(output + (i*32), o);
  }
}

static void Hacl_Impl_Chacha20_vec_update(uint8_t *output, uint8_t *plain, vec *st)
{
  vec k[16];
  for (uintmax_t _i = 0; _i < (uint32_t )16; ++_i)
    k[_i] = zero;
  Hacl_Impl_Chacha20_vec_chacha20_core(k, st);
  Hacl_Impl_Chacha20_vec_xor_block(output, plain, k);
  Hacl_Impl_Chacha20_state_state_incr(st);
}

static void
Hacl_Impl_Chacha20_vec_chacha20_counter_mode_(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  vec *st
)
{
  if (len == (uint32_t )0)
    return;
  else
  {
    Hacl_Impl_Chacha20_vec_update_last(output, plain, len, st);
    return;
  }
}

static void
Hacl_Impl_Chacha20_vec_chacha20_counter_mode(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  vec *st,
  uint32_t ctr
)
{
  uint32_t bs = 8 * 64; 
  if (len < bs)
  {
    Hacl_Impl_Chacha20_vec_chacha20_counter_mode_(output, plain, len, st);
    return;
  }
  else
  {
    uint8_t *b = plain;
    uint8_t *b_ = plain + bs;
    uint8_t *o = output;
    uint8_t *o_ = output + bs;
    Hacl_Impl_Chacha20_vec_update(o, b, st);
    Hacl_Impl_Chacha20_vec_chacha20_counter_mode(o_,
						 b_,
						 len - bs,
						 st,
						 ctr + 8);
    return;
  }
}

static void
Hacl_Impl_Chacha20_vec_chacha20(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  uint8_t *k,
  uint8_t *n,
  uint32_t ctr
)
{
  vec buf[16];
  for (uintmax_t _i = 0; _i < (uint32_t )16; ++_i)
    buf[_i] = zero;
  vec *st = buf;
  Hacl_Impl_Chacha20_state_state_setup(st, k, n, ctr);
  Hacl_Impl_Chacha20_vec_chacha20_counter_mode(output, plain, len, st, ctr);
}

void Chacha20_vec_chacha20_key_block(uint8_t *block, uint8_t *k, uint8_t *n, uint32_t ctr)
{
  vec buf[16];
  for (uintmax_t _i = 0; _i < (uint32_t )16; ++_i)
    buf[_i] = zero;
  vec *st = buf;
  Hacl_Impl_Chacha20_state_state_setup(st, k, n, ctr);
  Hacl_Impl_Chacha20_vec_chacha20_block(block, st);
}

void Chacha20_vec_double_round(vec *st)
{
  Hacl_Impl_Chacha20_vec_double_round(st);
  return;
}

void *Chacha20_vec_value_at(uint8_t *m, FStar_HyperStack_mem h)
{
  return (void *)(uint8_t )0;
}

void
Chacha20_vec_chacha20(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  uint8_t *k,
  uint8_t *n,
  uint32_t ctr
)
{
  Hacl_Impl_Chacha20_vec_chacha20(output, plain, len, k, n, ctr);
  return;
}

void
Chacha20_vec_crypto_stream_xor_ic(
  uint8_t *output,
  uint8_t *plain,
  uint32_t len,
  uint8_t *n,
  uint8_t *k,
  uint32_t ctr
)
{
  Chacha20_vec_chacha20(output, plain, len, k, n, ctr);
  return;
}

