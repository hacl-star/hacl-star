#include "SHA2_256.h"

static void
Hacl_Utils_Experimental_load32s_be(uint32_t *buf_32, uint8_t *buf_8, uint32_t len_8)
{
  if (len_8 == (uint32_t )0)
    return;
  else
  {
    uint8_t *x_8 = buf_8 + len_8 - (uint32_t )4;
    uint32_t i_32 = len_8 / (uint32_t )4;
    uint32_t x_32 = load32_be(x_8);
    buf_32[i_32 - (uint32_t )1] = x_32;
    Hacl_Utils_Experimental_load32s_be(buf_32, buf_8, len_8 - (uint32_t )4);
    return;
  }
}

static void
Hacl_Utils_Experimental_store32s_be(uint8_t *buf_8, uint32_t *buf_32, uint32_t len_32)
{
  if (len_32 == (uint32_t )0)
    return;
  else
  {
    uint32_t x_32 = buf_32[len_32 - (uint32_t )1];
    uint8_t *x_8 = buf_8 + (len_32 - (uint32_t )1) * (uint32_t )4;
    store32_be(x_8, x_32);
    Hacl_Utils_Experimental_store32s_be(buf_8, buf_32, len_32 - (uint32_t )1);
    return;
  }
}

static void Hacl_Hash_SHA2_L256_ws_upd(uint32_t *state, uint32_t *wblock, uint32_t t)
{
  uint32_t *ws = state + (uint32_t )64;
  if (t < (uint32_t )16)
  {
    uint32_t _0_33 = wblock[t];
    ws[t] = _0_33;
    Hacl_Hash_SHA2_L256_ws_upd(state, wblock, t + (uint32_t )1);
    return;
  }
  else if (t < (uint32_t )64)
  {
    uint32_t t16 = ws[t - (uint32_t )16];
    uint32_t t15 = ws[t - (uint32_t )15];
    uint32_t t7 = ws[t - (uint32_t )7];
    uint32_t t2 = ws[t - (uint32_t )2];
    ws[t] =
      ((t2 >> (uint32_t )17 | t2 << (uint32_t )32 - (uint32_t )17)
      ^ (t2 >> (uint32_t )19 | t2 << (uint32_t )32 - (uint32_t )19) ^ t2 >> (uint32_t )10)
      +
        t7
        +
          ((t15 >> (uint32_t )7 | t15 << (uint32_t )32 - (uint32_t )7)
          ^ (t15 >> (uint32_t )18 | t15 << (uint32_t )32 - (uint32_t )18) ^ t15 >> (uint32_t )3)
          + t16;
    Hacl_Hash_SHA2_L256_ws_upd(state, wblock, t + (uint32_t )1);
    return;
  }
  else
    return;
}

static void Hacl_Hash_SHA2_L256_init(uint32_t *state)
{
  uint32_t *k = state;
  k[(uint32_t )0 + (uint32_t )0] = (uint32_t )0x428a2f98;
  k[(uint32_t )0 + (uint32_t )1] = (uint32_t )0x71374491;
  k[(uint32_t )0 + (uint32_t )2] = (uint32_t )0xb5c0fbcf;
  k[(uint32_t )0 + (uint32_t )3] = (uint32_t )0xe9b5dba5;
  k[(uint32_t )4 + (uint32_t )0] = (uint32_t )0x3956c25b;
  k[(uint32_t )4 + (uint32_t )1] = (uint32_t )0x59f111f1;
  k[(uint32_t )4 + (uint32_t )2] = (uint32_t )0x923f82a4;
  k[(uint32_t )4 + (uint32_t )3] = (uint32_t )0xab1c5ed5;
  k[(uint32_t )8 + (uint32_t )0] = (uint32_t )0xd807aa98;
  k[(uint32_t )8 + (uint32_t )1] = (uint32_t )0x12835b01;
  k[(uint32_t )8 + (uint32_t )2] = (uint32_t )0x243185be;
  k[(uint32_t )8 + (uint32_t )3] = (uint32_t )0x550c7dc3;
  k[(uint32_t )12 + (uint32_t )0] = (uint32_t )0x72be5d74;
  k[(uint32_t )12 + (uint32_t )1] = (uint32_t )0x80deb1fe;
  k[(uint32_t )12 + (uint32_t )2] = (uint32_t )0x9bdc06a7;
  k[(uint32_t )12 + (uint32_t )3] = (uint32_t )0xc19bf174;
  k[(uint32_t )16 + (uint32_t )0] = (uint32_t )0xe49b69c1;
  k[(uint32_t )16 + (uint32_t )1] = (uint32_t )0xefbe4786;
  k[(uint32_t )16 + (uint32_t )2] = (uint32_t )0x0fc19dc6;
  k[(uint32_t )16 + (uint32_t )3] = (uint32_t )0x240ca1cc;
  k[(uint32_t )20 + (uint32_t )0] = (uint32_t )0x2de92c6f;
  k[(uint32_t )20 + (uint32_t )1] = (uint32_t )0x4a7484aa;
  k[(uint32_t )20 + (uint32_t )2] = (uint32_t )0x5cb0a9dc;
  k[(uint32_t )20 + (uint32_t )3] = (uint32_t )0x76f988da;
  k[(uint32_t )24 + (uint32_t )0] = (uint32_t )0x983e5152;
  k[(uint32_t )24 + (uint32_t )1] = (uint32_t )0xa831c66d;
  k[(uint32_t )24 + (uint32_t )2] = (uint32_t )0xb00327c8;
  k[(uint32_t )24 + (uint32_t )3] = (uint32_t )0xbf597fc7;
  k[(uint32_t )28 + (uint32_t )0] = (uint32_t )0xc6e00bf3;
  k[(uint32_t )28 + (uint32_t )1] = (uint32_t )0xd5a79147;
  k[(uint32_t )28 + (uint32_t )2] = (uint32_t )0x06ca6351;
  k[(uint32_t )28 + (uint32_t )3] = (uint32_t )0x14292967;
  k[(uint32_t )32 + (uint32_t )0] = (uint32_t )0x27b70a85;
  k[(uint32_t )32 + (uint32_t )1] = (uint32_t )0x2e1b2138;
  k[(uint32_t )32 + (uint32_t )2] = (uint32_t )0x4d2c6dfc;
  k[(uint32_t )32 + (uint32_t )3] = (uint32_t )0x53380d13;
  k[(uint32_t )36 + (uint32_t )0] = (uint32_t )0x650a7354;
  k[(uint32_t )36 + (uint32_t )1] = (uint32_t )0x766a0abb;
  k[(uint32_t )36 + (uint32_t )2] = (uint32_t )0x81c2c92e;
  k[(uint32_t )36 + (uint32_t )3] = (uint32_t )0x92722c85;
  k[(uint32_t )40 + (uint32_t )0] = (uint32_t )0xa2bfe8a1;
  k[(uint32_t )40 + (uint32_t )1] = (uint32_t )0xa81a664b;
  k[(uint32_t )40 + (uint32_t )2] = (uint32_t )0xc24b8b70;
  k[(uint32_t )40 + (uint32_t )3] = (uint32_t )0xc76c51a3;
  k[(uint32_t )44 + (uint32_t )0] = (uint32_t )0xd192e819;
  k[(uint32_t )44 + (uint32_t )1] = (uint32_t )0xd6990624;
  k[(uint32_t )44 + (uint32_t )2] = (uint32_t )0xf40e3585;
  k[(uint32_t )44 + (uint32_t )3] = (uint32_t )0x106aa070;
  k[(uint32_t )48 + (uint32_t )0] = (uint32_t )0x19a4c116;
  k[(uint32_t )48 + (uint32_t )1] = (uint32_t )0x1e376c08;
  k[(uint32_t )48 + (uint32_t )2] = (uint32_t )0x2748774c;
  k[(uint32_t )48 + (uint32_t )3] = (uint32_t )0x34b0bcb5;
  k[(uint32_t )52 + (uint32_t )0] = (uint32_t )0x391c0cb3;
  k[(uint32_t )52 + (uint32_t )1] = (uint32_t )0x4ed8aa4a;
  k[(uint32_t )52 + (uint32_t )2] = (uint32_t )0x5b9cca4f;
  k[(uint32_t )52 + (uint32_t )3] = (uint32_t )0x682e6ff3;
  k[(uint32_t )56 + (uint32_t )0] = (uint32_t )0x748f82ee;
  k[(uint32_t )56 + (uint32_t )1] = (uint32_t )0x78a5636f;
  k[(uint32_t )56 + (uint32_t )2] = (uint32_t )0x84c87814;
  k[(uint32_t )56 + (uint32_t )3] = (uint32_t )0x8cc70208;
  k[(uint32_t )60 + (uint32_t )0] = (uint32_t )0x90befffa;
  k[(uint32_t )60 + (uint32_t )1] = (uint32_t )0xa4506ceb;
  k[(uint32_t )60 + (uint32_t )2] = (uint32_t )0xbef9a3f7;
  k[(uint32_t )60 + (uint32_t )3] = (uint32_t )0xc67178f2;
  uint32_t *whash = state + (uint32_t )128;
  whash[(uint32_t )0 + (uint32_t )0] = (uint32_t )0x6a09e667;
  whash[(uint32_t )0 + (uint32_t )1] = (uint32_t )0xbb67ae85;
  whash[(uint32_t )0 + (uint32_t )2] = (uint32_t )0x3c6ef372;
  whash[(uint32_t )0 + (uint32_t )3] = (uint32_t )0xa54ff53a;
  whash[(uint32_t )4 + (uint32_t )0] = (uint32_t )0x510e527f;
  whash[(uint32_t )4 + (uint32_t )1] = (uint32_t )0x9b05688c;
  whash[(uint32_t )4 + (uint32_t )2] = (uint32_t )0x1f83d9ab;
  whash[(uint32_t )4 + (uint32_t )3] = (uint32_t )0x5be0cd19;
}

inline static void
Hacl_Hash_SHA2_L256_shuffle(uint32_t *state, uint32_t t1, uint32_t t2, uint32_t t)
{
  if (t < (uint32_t )64)
  {
    uint32_t *whash = state + (uint32_t )128;
    uint32_t *k = state;
    uint32_t *ws = state + (uint32_t )64;
    uint32_t _h = whash[7];
    uint32_t _kt = k[t];
    uint32_t _wt = ws[t];
    uint32_t x00 = whash[4];
    uint32_t
    v0 =
      (x00 >> (uint32_t )6 | x00 << (uint32_t )32 - (uint32_t )6)
      ^
        (x00 >> (uint32_t )11 | x00 << (uint32_t )32 - (uint32_t )11)
        ^ (x00 >> (uint32_t )25 | x00 << (uint32_t )32 - (uint32_t )25);
    uint32_t _0_36 = whash[4];
    uint32_t _0_35 = whash[5];
    uint32_t _0_34 = whash[6];
    uint32_t v1 = _0_36 & _0_35 ^ ~_0_36 & _0_34;
    uint32_t t1 = _h + v0 + v1 + _kt + _wt;
    uint32_t x0 = whash[0];
    uint32_t
    z0 =
      (x0 >> (uint32_t )2 | x0 << (uint32_t )32 - (uint32_t )2)
      ^
        (x0 >> (uint32_t )13 | x0 << (uint32_t )32 - (uint32_t )13)
        ^ (x0 >> (uint32_t )22 | x0 << (uint32_t )32 - (uint32_t )22);
    uint32_t _0_39 = whash[0];
    uint32_t _0_38 = whash[1];
    uint32_t _0_37 = whash[2];
    uint32_t z1 = _0_39 & _0_38 ^ _0_39 & _0_37 ^ _0_38 & _0_37;
    uint32_t t2 = z0 + z1;
    uint32_t _d = whash[3];
    uint32_t _0_40 = whash[6];
    whash[7] = _0_40;
    uint32_t _0_41 = whash[5];
    whash[6] = _0_41;
    uint32_t _0_42 = whash[4];
    whash[5] = _0_42;
    whash[4] = _d + t1;
    uint32_t _0_43 = whash[2];
    whash[3] = _0_43;
    uint32_t _0_44 = whash[1];
    whash[2] = _0_44;
    uint32_t _0_45 = whash[0];
    whash[1] = _0_45;
    whash[0] = t1 + t2;
    Hacl_Hash_SHA2_L256_shuffle(state, t1, t2, t + (uint32_t )1);
    return;
  }
  else
    return;
}

static void Hacl_Hash_SHA2_L256_update(uint32_t *state, uint8_t *data_8)
{
  KRML_CHECK_SIZE((uint32_t )0, (uint32_t )16);
  uint32_t data_32[16] = { 0 };
  Hacl_Utils_Experimental_load32s_be(data_32, data_8, (uint32_t )64);
  uint32_t *h = state + (uint32_t )128;
  Hacl_Hash_SHA2_L256_ws_upd(state, data_32, (uint32_t )0);
  uint32_t a_0 = h[0];
  uint32_t b_0 = h[1];
  uint32_t c_0 = h[2];
  uint32_t d_0 = h[3];
  uint32_t e_0 = h[4];
  uint32_t f_0 = h[5];
  uint32_t g_0 = h[6];
  uint32_t h_0 = h[7];
  Hacl_Hash_SHA2_L256_shuffle(state, (uint32_t )0, (uint32_t )0, (uint32_t )0);
  uint32_t a_1 = h[0];
  uint32_t b_1 = h[1];
  uint32_t c_1 = h[2];
  uint32_t d_1 = h[3];
  uint32_t e_1 = h[4];
  uint32_t f_1 = h[5];
  uint32_t g_1 = h[6];
  uint32_t h_1 = h[7];
  h[0] = a_0 + a_1;
  h[1] = b_0 + b_1;
  h[2] = c_0 + c_1;
  h[3] = d_0 + d_1;
  h[4] = e_0 + e_1;
  h[5] = f_0 + f_1;
  h[6] = g_0 + g_1;
  h[7] = h_0 + h_1;
  uint32_t _0_46 = state[136];
  uint32_t _0_47 = _0_46 + (uint32_t )1;
  state[136] = _0_47;
}

static void
Hacl_Hash_SHA2_L256_update_multi(uint32_t *state, uint8_t *data, uint32_t n, uint32_t idx)
{
  if (idx == n)
    return;
  else
  {
    uint8_t *b = data + idx * (uint32_t )64;
    Hacl_Hash_SHA2_L256_update(state, b);
    Hacl_Hash_SHA2_L256_update_multi(state, data, n, idx + (uint32_t )1);
    return;
  }
}

static void Hacl_Hash_SHA2_L256_update_last(uint32_t *state, uint8_t *data, uint32_t len)
{
  KRML_CHECK_SIZE((uint8_t )0, (uint32_t )8);
  uint8_t len_64[8] = { 0 };
  KRML_CHECK_SIZE((uint8_t )0, (uint32_t )128);
  uint8_t blocks[128] = { 0 };
  memcpy(blocks, data, len * sizeof data[0]);
  blocks[len] = (uint8_t )0x80;
  uint32_t count = state[136];
  uint64_t l_0 = (uint64_t )count * (uint64_t )(uint32_t )64;
  uint64_t l_1 = (uint64_t )len;
  uint64_t t_0 = (l_0 + l_1) * (uint64_t )(uint32_t )8;
  store64_be(len_64, t_0);
  if (len < (uint32_t )55)
  {
    memcpy(blocks + (uint32_t )56, len_64, (uint32_t )8 * sizeof len_64[0]);
    uint8_t *block_0 = blocks;
    Hacl_Hash_SHA2_L256_update(state, block_0);
  }
  else
  {
    memcpy(blocks + (uint32_t )120, len_64, (uint32_t )8 * sizeof len_64[0]);
    uint8_t *block_0 = blocks;
    uint8_t *block_1 = blocks + (uint32_t )64;
    Hacl_Hash_SHA2_L256_update(state, block_0);
    Hacl_Hash_SHA2_L256_update(state, block_1);
  }
}

static void Hacl_Hash_SHA2_L256_finish(uint32_t *state, uint8_t *hash)
{
  uint32_t *whash = state + (uint32_t )128;
  Hacl_Utils_Experimental_store32s_be(hash, whash, (uint32_t )8);
  return;
}

static void Hacl_Hash_SHA2_L256_hash(uint8_t *hash, uint8_t *input, uint32_t len)
{
  KRML_CHECK_SIZE((uint32_t )0, (uint32_t )137);
  uint32_t ctx[137] = { 0 };
  uint32_t n = len / (uint32_t )64;
  uint32_t r = len % (uint32_t )64;
  Hacl_Hash_SHA2_L256_init(ctx);
  Hacl_Hash_SHA2_L256_update_multi(ctx, input, n, (uint32_t )0);
  uint8_t *input_last = input + n * (uint32_t )64;
  Hacl_Hash_SHA2_L256_update_last(ctx, input_last, r);
  Hacl_Hash_SHA2_L256_finish(ctx, hash);
}

uint32_t hashsize_256 = (uint32_t )32;

uint32_t blocksize_256 = (uint32_t )64;

uint32_t size_state_256 = (uint32_t )137;

void sha2_init_256(uint32_t *state)
{
  Hacl_Hash_SHA2_L256_init(state);
  return;
}

void sha2_update_256(uint32_t *state, uint8_t *data_8)
{
  Hacl_Hash_SHA2_L256_update(state, data_8);
  return;
}

void sha2_update_multi_256(uint32_t *state, uint8_t *data, uint32_t n, uint32_t idx)
{
  Hacl_Hash_SHA2_L256_update_multi(state, data, n, idx);
  return;
}

void sha2_update_last_256(uint32_t *state, uint8_t *data, uint32_t len)
{
  Hacl_Hash_SHA2_L256_update_last(state, data, len);
  return;
}

void sha2_finish_256(uint32_t *state, uint8_t *hash)
{
  Hacl_Hash_SHA2_L256_finish(state, hash);
  return;
}

void sha2_256(uint8_t *hash, uint8_t *input, uint32_t len)
{
  Hacl_Hash_SHA2_L256_hash(hash, input, len);
  return;
}

