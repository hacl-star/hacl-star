#include "SHA2_256.h"

static void load32s_be(uint32_t *buf_32, uint8_t *buf_8, uint32_t len_8)
{
  if (len_8 == (uint32_t )0)
    return;
  else
  {
    uint8_t *x_8 = buf_8 + len_8 - (uint32_t )4;
    uint32_t i_32 = len_8 / (uint32_t )4;
    uint32_t x_32 = load32_be(x_8);
    buf_32[i_32 - (uint32_t )1] = x_32;
    load32s_be(buf_32, buf_8, len_8 - (uint32_t )4);
    return;
  }
}

static void store32s_be(uint8_t *buf_8, uint32_t *buf_32, uint32_t len_32)
{
  if (len_32 == (uint32_t )0)
    return;
  else
  {
    uint32_t x_32 = buf_32[len_32 - (uint32_t )1];
    uint8_t *x_8 = buf_8 + (len_32 - (uint32_t )1) * (uint32_t )4;
    store32_be(x_8, x_32);
    store32s_be(buf_8, buf_32, len_32 - (uint32_t )1);
    return;
  }
}

static void init(uint32_t *state)
{
  uint32_t *k1 = state;
  uint32_t *h_01 = state + (uint32_t )128;
  k1[(uint32_t )0 + (uint32_t )0] = (uint32_t )0x428a2f98;
  k1[(uint32_t )0 + (uint32_t )1] = (uint32_t )0x71374491;
  k1[(uint32_t )0 + (uint32_t )2] = (uint32_t )0xb5c0fbcf;
  k1[(uint32_t )0 + (uint32_t )3] = (uint32_t )0xe9b5dba5;
  k1[(uint32_t )4 + (uint32_t )0] = (uint32_t )0x3956c25b;
  k1[(uint32_t )4 + (uint32_t )1] = (uint32_t )0x59f111f1;
  k1[(uint32_t )4 + (uint32_t )2] = (uint32_t )0x923f82a4;
  k1[(uint32_t )4 + (uint32_t )3] = (uint32_t )0xab1c5ed5;
  k1[(uint32_t )8 + (uint32_t )0] = (uint32_t )0xd807aa98;
  k1[(uint32_t )8 + (uint32_t )1] = (uint32_t )0x12835b01;
  k1[(uint32_t )8 + (uint32_t )2] = (uint32_t )0x243185be;
  k1[(uint32_t )8 + (uint32_t )3] = (uint32_t )0x550c7dc3;
  k1[(uint32_t )12 + (uint32_t )0] = (uint32_t )0x72be5d74;
  k1[(uint32_t )12 + (uint32_t )1] = (uint32_t )0x80deb1fe;
  k1[(uint32_t )12 + (uint32_t )2] = (uint32_t )0x9bdc06a7;
  k1[(uint32_t )12 + (uint32_t )3] = (uint32_t )0xc19bf174;
  k1[(uint32_t )16 + (uint32_t )0] = (uint32_t )0xe49b69c1;
  k1[(uint32_t )16 + (uint32_t )1] = (uint32_t )0xefbe4786;
  k1[(uint32_t )16 + (uint32_t )2] = (uint32_t )0x0fc19dc6;
  k1[(uint32_t )16 + (uint32_t )3] = (uint32_t )0x240ca1cc;
  k1[(uint32_t )20 + (uint32_t )0] = (uint32_t )0x2de92c6f;
  k1[(uint32_t )20 + (uint32_t )1] = (uint32_t )0x4a7484aa;
  k1[(uint32_t )20 + (uint32_t )2] = (uint32_t )0x5cb0a9dc;
  k1[(uint32_t )20 + (uint32_t )3] = (uint32_t )0x76f988da;
  k1[(uint32_t )24 + (uint32_t )0] = (uint32_t )0x983e5152;
  k1[(uint32_t )24 + (uint32_t )1] = (uint32_t )0xa831c66d;
  k1[(uint32_t )24 + (uint32_t )2] = (uint32_t )0xb00327c8;
  k1[(uint32_t )24 + (uint32_t )3] = (uint32_t )0xbf597fc7;
  k1[(uint32_t )28 + (uint32_t )0] = (uint32_t )0xc6e00bf3;
  k1[(uint32_t )28 + (uint32_t )1] = (uint32_t )0xd5a79147;
  k1[(uint32_t )28 + (uint32_t )2] = (uint32_t )0x06ca6351;
  k1[(uint32_t )28 + (uint32_t )3] = (uint32_t )0x14292967;
  k1[(uint32_t )32 + (uint32_t )0] = (uint32_t )0x27b70a85;
  k1[(uint32_t )32 + (uint32_t )1] = (uint32_t )0x2e1b2138;
  k1[(uint32_t )32 + (uint32_t )2] = (uint32_t )0x4d2c6dfc;
  k1[(uint32_t )32 + (uint32_t )3] = (uint32_t )0x53380d13;
  k1[(uint32_t )36 + (uint32_t )0] = (uint32_t )0x650a7354;
  k1[(uint32_t )36 + (uint32_t )1] = (uint32_t )0x766a0abb;
  k1[(uint32_t )36 + (uint32_t )2] = (uint32_t )0x81c2c92e;
  k1[(uint32_t )36 + (uint32_t )3] = (uint32_t )0x92722c85;
  k1[(uint32_t )40 + (uint32_t )0] = (uint32_t )0xa2bfe8a1;
  k1[(uint32_t )40 + (uint32_t )1] = (uint32_t )0xa81a664b;
  k1[(uint32_t )40 + (uint32_t )2] = (uint32_t )0xc24b8b70;
  k1[(uint32_t )40 + (uint32_t )3] = (uint32_t )0xc76c51a3;
  k1[(uint32_t )44 + (uint32_t )0] = (uint32_t )0xd192e819;
  k1[(uint32_t )44 + (uint32_t )1] = (uint32_t )0xd6990624;
  k1[(uint32_t )44 + (uint32_t )2] = (uint32_t )0xf40e3585;
  k1[(uint32_t )44 + (uint32_t )3] = (uint32_t )0x106aa070;
  k1[(uint32_t )48 + (uint32_t )0] = (uint32_t )0x19a4c116;
  k1[(uint32_t )48 + (uint32_t )1] = (uint32_t )0x1e376c08;
  k1[(uint32_t )48 + (uint32_t )2] = (uint32_t )0x2748774c;
  k1[(uint32_t )48 + (uint32_t )3] = (uint32_t )0x34b0bcb5;
  k1[(uint32_t )52 + (uint32_t )0] = (uint32_t )0x391c0cb3;
  k1[(uint32_t )52 + (uint32_t )1] = (uint32_t )0x4ed8aa4a;
  k1[(uint32_t )52 + (uint32_t )2] = (uint32_t )0x5b9cca4f;
  k1[(uint32_t )52 + (uint32_t )3] = (uint32_t )0x682e6ff3;
  k1[(uint32_t )56 + (uint32_t )0] = (uint32_t )0x748f82ee;
  k1[(uint32_t )56 + (uint32_t )1] = (uint32_t )0x78a5636f;
  k1[(uint32_t )56 + (uint32_t )2] = (uint32_t )0x84c87814;
  k1[(uint32_t )56 + (uint32_t )3] = (uint32_t )0x8cc70208;
  k1[(uint32_t )60 + (uint32_t )0] = (uint32_t )0x90befffa;
  k1[(uint32_t )60 + (uint32_t )1] = (uint32_t )0xa4506ceb;
  k1[(uint32_t )60 + (uint32_t )2] = (uint32_t )0xbef9a3f7;
  k1[(uint32_t )60 + (uint32_t )3] = (uint32_t )0xc67178f2;
  h_01[(uint32_t )0 + (uint32_t )0] = (uint32_t )0x6a09e667;
  h_01[(uint32_t )0 + (uint32_t )1] = (uint32_t )0xbb67ae85;
  h_01[(uint32_t )0 + (uint32_t )2] = (uint32_t )0x3c6ef372;
  h_01[(uint32_t )0 + (uint32_t )3] = (uint32_t )0xa54ff53a;
  h_01[(uint32_t )4 + (uint32_t )0] = (uint32_t )0x510e527f;
  h_01[(uint32_t )4 + (uint32_t )1] = (uint32_t )0x9b05688c;
  h_01[(uint32_t )4 + (uint32_t )2] = (uint32_t )0x1f83d9ab;
  h_01[(uint32_t )4 + (uint32_t )3] = (uint32_t )0x5be0cd19;
}

static void update(uint32_t *state, uint8_t *data)
{
  KRML_CHECK_SIZE((uint32_t )0, (uint32_t )16);
  uint32_t data_w[16] = { 0 };
  KRML_CHECK_SIZE((uint32_t )0, (uint32_t )8);
  uint32_t hash_0[8] = { 0 };
  uint32_t *hash_w = state + (uint32_t )128;
  uint32_t *ws_w = state + (uint32_t )64;
  uint32_t *k_w = state;
  load32s_be(data_w, data, (uint32_t )64);
  memcpy(hash_0, state + (uint32_t )128, (uint32_t )8 * sizeof state[0]);
  for (uint32_t i = (uint32_t )0; i < (uint32_t )16; i = i + (uint32_t )1)
  {
    uint32_t uu____264 = data_w[i];
    ws_w[i] = uu____264;
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
    uint32_t uu____603 = k_w[i];
    uint32_t
    uu____602 =
      h
      +
        ((e >> (uint32_t )6 | e << (uint32_t )32 - (uint32_t )6)
        ^
          (e >> (uint32_t )11 | e << (uint32_t )32 - (uint32_t )11)
          ^ (e >> (uint32_t )25 | e << (uint32_t )32 - (uint32_t )25))
      + (e & f1 ^ ~e & g)
      + uu____603;
    uint32_t uu____604 = ws_w[i];
    uint32_t t1 = uu____602 + uu____604;
    uint32_t
    t2 =
      ((a >> (uint32_t )2 | a << (uint32_t )32 - (uint32_t )2)
      ^
        (a >> (uint32_t )13 | a << (uint32_t )32 - (uint32_t )13)
        ^ (a >> (uint32_t )22 | a << (uint32_t )32 - (uint32_t )22))
      + (a & b ^ a & c ^ b & c);
    hash_0[7] = g;
    hash_0[6] = f1;
    hash_0[5] = e;
    hash_0[4] = d + t1;
    hash_0[3] = c;
    hash_0[2] = b;
    hash_0[1] = a;
    hash_0[0] = t1 + t2;
  }
  uint32_t *hash_1 = state + (uint32_t )128;
  for (uint32_t i = (uint32_t )0; i < (uint32_t )8; i = i + (uint32_t )1)
  {
    uint32_t uu____763 = hash_1[i];
    uint32_t uu____766 = hash_0[i];
    uint32_t uu____762 = uu____763 + uu____766;
    hash_1[i] = uu____762;
  }
  uint32_t uu____954 = state[136];
  uint32_t uu____953 = uu____954 + (uint32_t )1;
  state[136] = uu____953;
}

static void update_multi(uint32_t *state, uint8_t *data, uint32_t n1)
{
  if (n1 == (uint32_t )0)
    return;
  else
  {
    uint8_t *b = data;
    update(state, b);
    uint8_t *data1 = data + (uint32_t )64;
    update_multi(state, data1, n1 - (uint32_t )1);
    return;
  }
}

static void update_last(uint32_t *state, uint8_t *data, uint32_t len)
{
  KRML_CHECK_SIZE((uint8_t )0, (uint32_t )128);
  uint8_t blocks[128] = { 0 };
  uint32_t count1 = state[136];
  uint64_t l_0 = (uint64_t )count1 * (uint64_t )(uint32_t )64;
  uint64_t l_1 = (uint64_t )len;
  uint64_t t_0 = (l_0 + l_1) * (uint64_t )(uint32_t )8;
  uint8_t *len_64 = blocks + (uint32_t )120;
  store64_be(len_64, t_0);
  bool scrut0 = len < (uint32_t )55;
  K___uint32_t_uint8_t_ scrut;
  if (scrut0 == true)
    scrut = ((K___uint32_t_uint8_t_ ){ .fst = (uint32_t )1, .snd = blocks + (uint32_t )64 });
  else
  {
    bool uu____1096 = scrut0;
    scrut = ((K___uint32_t_uint8_t_ ){ .fst = (uint32_t )2, .snd = blocks });
  }
  uint32_t n1 = scrut.fst;
  uint8_t *final_blocks = scrut.snd;
  memcpy(final_blocks, data, len * sizeof data[0]);
  final_blocks[len] = (uint8_t )0x80;
  update_multi(state, final_blocks, n1);
}

static void finish(uint32_t *state, uint8_t *hash1)
{
  uint32_t *whash = state + (uint32_t )128;
  store32s_be(hash1, whash, (uint32_t )8);
  return;
}

static void hash(uint8_t *hash1, uint8_t *input, uint32_t len)
{
  KRML_CHECK_SIZE((uint32_t )0, (uint32_t )137);
  uint32_t ctx[137] = { 0 };
  uint32_t n1 = len / (uint32_t )64;
  uint32_t r = len % (uint32_t )64;
  init(ctx);
  update_multi(ctx, input, n1);
  uint8_t *input_last = input + n1 * (uint32_t )64;
  update_last(ctx, input_last, r);
  finish(ctx, hash1);
}

uint32_t hash_hashsize_256 = (uint32_t )32;

uint32_t hash_blocksize_256 = (uint32_t )64;

uint32_t hash_size_state_256 = (uint32_t )137;

void sha2_init_256(uint32_t *state)
{
  init(state);
  return;
}

void sha2_update_256(uint32_t *state, uint8_t *data_8)
{
  update(state, data_8);
  return;
}

void sha2_update_multi_256(uint32_t *state, uint8_t *data, uint32_t n1)
{
  update_multi(state, data, n1);
  return;
}

void sha2_update_last_256(uint32_t *state, uint8_t *data, uint32_t len)
{
  update_last(state, data, len);
  return;
}

void sha2_finish_256(uint32_t *state, uint8_t *hash1)
{
  finish(state, hash1);
  return;
}

void sha2_256(uint8_t *hash1, uint8_t *input, uint32_t len)
{
  hash(hash1, input, len);
  return;
}

