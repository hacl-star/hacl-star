#include "SHA2_256.h"

static void
Hacl_Hash_Lib_LoadStore_uint32s_from_be_bytes(uint32_t *output, uint8_t *input, uint32_t len)
{
  for (uint32_t i = (uint32_t )0; i < len; i = i + (uint32_t )1)
  {
    uint8_t *x0 = input + (uint32_t )4 * i;
    uint32_t inputi = load32_be(x0);
    output[i] = inputi;
  }
}

static void
Hacl_Hash_Lib_LoadStore_uint32s_to_be_bytes(uint8_t *output, uint32_t *input, uint32_t len)
{
  for (uint32_t i = (uint32_t )0; i < len; i = i + (uint32_t )1)
  {
    uint32_t hd1 = input[i];
    uint8_t *x0 = output + (uint32_t )4 * i;
    store32_be(x0, hd1);
  }
}

static void Hacl_Hash_SHA2_256_init(uint32_t *state)
{
  (void )(state + (uint32_t )136);
  uint32_t *k1 = state;
  uint32_t *h_01 = state + (uint32_t )128;
  uint32_t *p10 = k1;
  uint32_t *p20 = k1 + (uint32_t )16;
  uint32_t *p3 = k1 + (uint32_t )32;
  uint32_t *p4 = k1 + (uint32_t )48;
  uint32_t *p11 = p10;
  uint32_t *p21 = p10 + (uint32_t )8;
  uint32_t *p12 = p11;
  uint32_t *p22 = p11 + (uint32_t )4;
  p12[0] = (uint32_t )0x428a2f98;
  p12[1] = (uint32_t )0x71374491;
  p12[2] = (uint32_t )0xb5c0fbcf;
  p12[3] = (uint32_t )0xe9b5dba5;
  p22[0] = (uint32_t )0x3956c25b;
  p22[1] = (uint32_t )0x59f111f1;
  p22[2] = (uint32_t )0x923f82a4;
  p22[3] = (uint32_t )0xab1c5ed5;
  uint32_t *p13 = p21;
  uint32_t *p23 = p21 + (uint32_t )4;
  p13[0] = (uint32_t )0xd807aa98;
  p13[1] = (uint32_t )0x12835b01;
  p13[2] = (uint32_t )0x243185be;
  p13[3] = (uint32_t )0x550c7dc3;
  p23[0] = (uint32_t )0x72be5d74;
  p23[1] = (uint32_t )0x80deb1fe;
  p23[2] = (uint32_t )0x9bdc06a7;
  p23[3] = (uint32_t )0xc19bf174;
  uint32_t *p14 = p20;
  uint32_t *p24 = p20 + (uint32_t )8;
  uint32_t *p15 = p14;
  uint32_t *p25 = p14 + (uint32_t )4;
  p15[0] = (uint32_t )0xe49b69c1;
  p15[1] = (uint32_t )0xefbe4786;
  p15[2] = (uint32_t )0x0fc19dc6;
  p15[3] = (uint32_t )0x240ca1cc;
  p25[0] = (uint32_t )0x2de92c6f;
  p25[1] = (uint32_t )0x4a7484aa;
  p25[2] = (uint32_t )0x5cb0a9dc;
  p25[3] = (uint32_t )0x76f988da;
  uint32_t *p16 = p24;
  uint32_t *p26 = p24 + (uint32_t )4;
  p16[0] = (uint32_t )0x983e5152;
  p16[1] = (uint32_t )0xa831c66d;
  p16[2] = (uint32_t )0xb00327c8;
  p16[3] = (uint32_t )0xbf597fc7;
  p26[0] = (uint32_t )0xc6e00bf3;
  p26[1] = (uint32_t )0xd5a79147;
  p26[2] = (uint32_t )0x06ca6351;
  p26[3] = (uint32_t )0x14292967;
  uint32_t *p17 = p3;
  uint32_t *p27 = p3 + (uint32_t )8;
  uint32_t *p18 = p17;
  uint32_t *p28 = p17 + (uint32_t )4;
  p18[0] = (uint32_t )0x27b70a85;
  p18[1] = (uint32_t )0x2e1b2138;
  p18[2] = (uint32_t )0x4d2c6dfc;
  p18[3] = (uint32_t )0x53380d13;
  p28[0] = (uint32_t )0x650a7354;
  p28[1] = (uint32_t )0x766a0abb;
  p28[2] = (uint32_t )0x81c2c92e;
  p28[3] = (uint32_t )0x92722c85;
  uint32_t *p19 = p27;
  uint32_t *p29 = p27 + (uint32_t )4;
  p19[0] = (uint32_t )0xa2bfe8a1;
  p19[1] = (uint32_t )0xa81a664b;
  p19[2] = (uint32_t )0xc24b8b70;
  p19[3] = (uint32_t )0xc76c51a3;
  p29[0] = (uint32_t )0xd192e819;
  p29[1] = (uint32_t )0xd6990624;
  p29[2] = (uint32_t )0xf40e3585;
  p29[3] = (uint32_t )0x106aa070;
  uint32_t *p110 = p4;
  uint32_t *p210 = p4 + (uint32_t )8;
  uint32_t *p1 = p110;
  uint32_t *p211 = p110 + (uint32_t )4;
  p1[0] = (uint32_t )0x19a4c116;
  p1[1] = (uint32_t )0x1e376c08;
  p1[2] = (uint32_t )0x2748774c;
  p1[3] = (uint32_t )0x34b0bcb5;
  p211[0] = (uint32_t )0x391c0cb3;
  p211[1] = (uint32_t )0x4ed8aa4a;
  p211[2] = (uint32_t )0x5b9cca4f;
  p211[3] = (uint32_t )0x682e6ff3;
  uint32_t *p111 = p210;
  uint32_t *p212 = p210 + (uint32_t )4;
  p111[0] = (uint32_t )0x748f82ee;
  p111[1] = (uint32_t )0x78a5636f;
  p111[2] = (uint32_t )0x84c87814;
  p111[3] = (uint32_t )0x8cc70208;
  p212[0] = (uint32_t )0x90befffa;
  p212[1] = (uint32_t )0xa4506ceb;
  p212[2] = (uint32_t )0xbef9a3f7;
  p212[3] = (uint32_t )0xc67178f2;
  uint32_t *p112 = h_01;
  uint32_t *p2 = h_01 + (uint32_t )4;
  p112[0] = (uint32_t )0x6a09e667;
  p112[1] = (uint32_t )0xbb67ae85;
  p112[2] = (uint32_t )0x3c6ef372;
  p112[3] = (uint32_t )0xa54ff53a;
  p2[0] = (uint32_t )0x510e527f;
  p2[1] = (uint32_t )0x9b05688c;
  p2[2] = (uint32_t )0x1f83d9ab;
  p2[3] = (uint32_t )0x5be0cd19;
}

static void Hacl_Hash_SHA2_256_update(uint32_t *state, uint8_t *data)
{
  uint32_t data_w[16] = { 0 };
  Hacl_Hash_Lib_LoadStore_uint32s_from_be_bytes(data_w, data, (uint32_t )16);
  uint32_t *hash_w = state + (uint32_t )128;
  uint32_t *ws_w = state + (uint32_t )64;
  uint32_t *k_w = state;
  uint32_t *counter_w = state + (uint32_t )136;
  for (uint32_t i = (uint32_t )0; i < (uint32_t )16; i = i + (uint32_t )1)
  {
    uint32_t uu____206 = data_w[i];
    ws_w[i] = uu____206;
  }
  for (uint32_t i = (uint32_t )16; i < (uint32_t )64; i = i + (uint32_t )1)
  {
    uint32_t t16 = ws_w[i - (uint32_t )16];
    uint32_t t15 = ws_w[i - (uint32_t )15];
    uint32_t t7 = ws_w[i - (uint32_t )7];
    uint32_t t2 = ws_w[i - (uint32_t )2];
    ws_w[i] =
      ((t2 >> (uint32_t )17 | t2 << (uint32_t )32 - (uint32_t )17)
      ^ (t2 >> (uint32_t )19 | t2 << (uint32_t )32 - (uint32_t )19) ^ t2 >> (uint32_t )10)
      +
        t7
        +
          ((t15 >> (uint32_t )7 | t15 << (uint32_t )32 - (uint32_t )7)
          ^ (t15 >> (uint32_t )18 | t15 << (uint32_t )32 - (uint32_t )18) ^ t15 >> (uint32_t )3)
          + t16;
  }
  uint32_t hash_0[8] = { 0 };
  memcpy(hash_0, hash_w, (uint32_t )8 * sizeof hash_w[0]);
  for (uint32_t i = (uint32_t )0; i < (uint32_t )64; i = i + (uint32_t )1)
  {
    uint32_t a = hash_0[0];
    uint32_t b = hash_0[1];
    uint32_t c = hash_0[2];
    uint32_t d = hash_0[3];
    uint32_t e = hash_0[4];
    uint32_t f1 = hash_0[5];
    uint32_t g = hash_0[6];
    uint32_t h = hash_0[7];
    uint32_t kt = k_w[i];
    uint32_t wst = ws_w[i];
    uint32_t
    t1 =
      h
      +
        ((e >> (uint32_t )6 | e << (uint32_t )32 - (uint32_t )6)
        ^
          (e >> (uint32_t )11 | e << (uint32_t )32 - (uint32_t )11)
          ^ (e >> (uint32_t )25 | e << (uint32_t )32 - (uint32_t )25))
      + (e & f1 ^ ~e & g)
      + kt
      + wst;
    uint32_t
    t2 =
      ((a >> (uint32_t )2 | a << (uint32_t )32 - (uint32_t )2)
      ^
        (a >> (uint32_t )13 | a << (uint32_t )32 - (uint32_t )13)
        ^ (a >> (uint32_t )22 | a << (uint32_t )32 - (uint32_t )22))
      + (a & b ^ a & c ^ b & c);
    uint32_t x1 = t1 + t2;
    uint32_t x5 = d + t1;
    uint32_t *p1 = hash_0;
    uint32_t *p2 = hash_0 + (uint32_t )4;
    p1[0] = x1;
    p1[1] = a;
    p1[2] = b;
    p1[3] = c;
    p2[0] = x5;
    p2[1] = e;
    p2[2] = f1;
    p2[3] = g;
  }
  for (uint32_t i = (uint32_t )0; i < (uint32_t )8; i = i + (uint32_t )1)
  {
    uint32_t uu____871 = hash_w[i];
    uint32_t uu____874 = hash_0[i];
    uint32_t uu____870 = uu____871 + uu____874;
    hash_w[i] = uu____870;
  }
  uint32_t c0 = counter_w[0];
  uint32_t one1 = (uint32_t )1;
  counter_w[0] = c0 + one1;
}

static void Hacl_Hash_SHA2_256_update_multi(uint32_t *state, uint8_t *data, uint32_t n1)
{
  for (uint32_t i = (uint32_t )0; i < n1; i = i + (uint32_t )1)
  {
    uint8_t *b = data + i * (uint32_t )64;
    Hacl_Hash_SHA2_256_update(state, b);
  }
}

static void Hacl_Hash_SHA2_256_update_last(uint32_t *state, uint8_t *data, uint32_t len)
{
  uint8_t blocks[128] = { 0 };
  K___uint32_t_uint8_t_ uu____1925;
  if (len < (uint32_t )56)
    uu____1925 = ((K___uint32_t_uint8_t_ ){ .fst = (uint32_t )1, .snd = blocks + (uint32_t )64 });
  else
    uu____1925 = ((K___uint32_t_uint8_t_ ){ .fst = (uint32_t )2, .snd = blocks });
  K___uint32_t_uint8_t_ scrut = uu____1925;
  uint32_t nb = scrut.fst;
  uint8_t *final_blocks = scrut.snd;
  memcpy(final_blocks, data, len * sizeof data[0]);
  uint32_t n1 = state[136];
  uint8_t *padding = final_blocks + len;
  uint32_t
  pad0len = ((uint32_t )64 - (len + (uint32_t )8 + (uint32_t )1) % (uint32_t )64) % (uint32_t )64;
  uint8_t *buf1 = padding;
  (void )(padding + (uint32_t )1);
  uint8_t *buf2 = padding + (uint32_t )1 + pad0len;
  uint64_t
  encodedlen =
    ((uint64_t )n1 * (uint64_t )(uint32_t )64 + (uint64_t )len)
    * (uint64_t )(uint32_t )8;
  buf1[0] = (uint8_t )0x80;
  store64_be(buf2, encodedlen);
  Hacl_Hash_SHA2_256_update_multi(state, final_blocks, nb);
}

static void Hacl_Hash_SHA2_256_finish(uint32_t *state, uint8_t *hash1)
{
  uint32_t *hash_w = state + (uint32_t )128;
  Hacl_Hash_Lib_LoadStore_uint32s_to_be_bytes(hash1, hash_w, (uint32_t )8);
}

static void Hacl_Hash_SHA2_256_hash(uint8_t *hash1, uint8_t *input, uint32_t len)
{
  uint32_t state[137] = { 0 };
  uint32_t n1 = len / (uint32_t )64;
  uint32_t r = len % (uint32_t )64;
  uint8_t *input_blocks = input;
  uint8_t *input_last = input + n1 * (uint32_t )64;
  Hacl_Hash_SHA2_256_init(state);
  Hacl_Hash_SHA2_256_update_multi(state, input_blocks, n1);
  Hacl_Hash_SHA2_256_update_last(state, input_last, r);
  Hacl_Hash_SHA2_256_finish(state, hash1);
}

uint32_t SHA2_256_size_hash = (uint32_t )32;

uint32_t SHA2_256_size_block = (uint32_t )64;

uint32_t SHA2_256_size_state = (uint32_t )137;

void SHA2_256_init(uint32_t *state)
{
  Hacl_Hash_SHA2_256_init(state);
}

void SHA2_256_update(uint32_t *state, uint8_t *data_8)
{
  Hacl_Hash_SHA2_256_update(state, data_8);
}

void SHA2_256_update_multi(uint32_t *state, uint8_t *data, uint32_t n1)
{
  Hacl_Hash_SHA2_256_update_multi(state, data, n1);
}

void SHA2_256_update_last(uint32_t *state, uint8_t *data, uint32_t len)
{
  Hacl_Hash_SHA2_256_update_last(state, data, len);
}

void SHA2_256_finish(uint32_t *state, uint8_t *hash1)
{
  Hacl_Hash_SHA2_256_finish(state, hash1);
}

void SHA2_256_hash(uint8_t *hash1, uint8_t *input, uint32_t len)
{
  Hacl_Hash_SHA2_256_hash(hash1, input, len);
}

