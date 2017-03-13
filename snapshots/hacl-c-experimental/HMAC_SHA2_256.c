#include "HMAC_SHA2_256.h"

static void xor_bytes(uint8_t *output, uint8_t *input, uint32_t len)
{
  if (len == (uint32_t )0)
    return;
  else
  {
    uint32_t i = len - (uint32_t )1;
    uint8_t in1i = input[i];
    uint8_t oi = output[i];
    uint8_t oi0 = in1i ^ oi;
    output[i] = oi0;
    xor_bytes(output, input, i);
    return;
  }
}

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

static void Hacl_Hash_SHA2_L256_ws_compute(uint32_t *state, uint32_t *wblock, uint32_t t)
{
  uint32_t *ws = state + (uint32_t )64;
  if (t < (uint32_t )16)
  {
    uint32_t _0_33 = wblock[t];
    ws[t] = _0_33;
    Hacl_Hash_SHA2_L256_ws_compute(state, wblock, t + (uint32_t )1);
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
    Hacl_Hash_SHA2_L256_ws_compute(state, wblock, t + (uint32_t )1);
    return;
  }
  else
    return;
}

inline static void Hacl_Hash_SHA2_L256_shuffle_core(uint32_t *state, uint32_t t)
{
  uint32_t *hash = state + (uint32_t )128;
  uint32_t *k = state;
  uint32_t *ws = state + (uint32_t )64;
  uint32_t a = hash[0];
  uint32_t b = hash[1];
  uint32_t c = hash[2];
  uint32_t d = hash[3];
  uint32_t e = hash[4];
  uint32_t f = hash[5];
  uint32_t g = hash[6];
  uint32_t h = hash[7];
  uint32_t _0_34 = k[t];
  uint32_t
  _0_36 =
    h
    +
      ((e >> (uint32_t )6 | e << (uint32_t )32 - (uint32_t )6)
      ^
        (e >> (uint32_t )11 | e << (uint32_t )32 - (uint32_t )11)
        ^ (e >> (uint32_t )25 | e << (uint32_t )32 - (uint32_t )25))
    + (e & f ^ ~e & g)
    + _0_34;
  uint32_t _0_35 = ws[t];
  uint32_t t1 = _0_36 + _0_35;
  uint32_t
  t2 =
    ((a >> (uint32_t )2 | a << (uint32_t )32 - (uint32_t )2)
    ^
      (a >> (uint32_t )13 | a << (uint32_t )32 - (uint32_t )13)
      ^ (a >> (uint32_t )22 | a << (uint32_t )32 - (uint32_t )22))
    + (a & b ^ a & c ^ b & c);
  hash[7] = g;
  hash[6] = f;
  hash[5] = e;
  hash[4] = d + t1;
  hash[3] = c;
  hash[2] = b;
  hash[1] = a;
  hash[0] = t1 + t2;
}

inline static void Hacl_Hash_SHA2_L256_shuffle(uint32_t *state, uint32_t t)
{
  if (t < (uint32_t )64)
  {
    Hacl_Hash_SHA2_L256_shuffle_core(state, t);
    Hacl_Hash_SHA2_L256_shuffle(state, t + (uint32_t )1);
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

static void Hacl_Hash_SHA2_L256_update(uint32_t *state, uint8_t *data_8)
{
  KRML_CHECK_SIZE((uint32_t )0, (uint32_t )16);
  uint32_t data_32[16] = { 0 };
  load32s_be(data_32, data_8, (uint32_t )64);
  uint32_t *h = state + (uint32_t )128;
  Hacl_Hash_SHA2_L256_ws_compute(state, data_32, (uint32_t )0);
  uint32_t a_0 = h[0];
  uint32_t b_0 = h[1];
  uint32_t c_0 = h[2];
  uint32_t d_0 = h[3];
  uint32_t e_0 = h[4];
  uint32_t f_0 = h[5];
  uint32_t g_0 = h[6];
  uint32_t h_0 = h[7];
  Hacl_Hash_SHA2_L256_shuffle(state, (uint32_t )0);
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
  uint32_t _0_37 = state[136];
  uint32_t _0_38 = _0_37 + (uint32_t )1;
  state[136] = _0_38;
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
  store32s_be(hash, whash, (uint32_t )8);
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

static uint32_t u32_to_s32(uint32_t a)
{
  return a;
}

inline static void hmac_wrap_key(uint8_t *okey, uint8_t *key, uint32_t len)
{
  if (len > (uint32_t )64)
  {
    uint8_t *okey0 = okey;
    Hacl_Hash_SHA2_L256_hash(okey0, key, len);
    return;
  }
  else
  {
    uint8_t *okey0 = okey;
    memcpy(okey0, key, len * sizeof key[0]);
  }
}

static void init(uint32_t *state, uint8_t *key, uint32_t len)
{
  KRML_CHECK_SIZE((uint8_t )0x36, (uint32_t )64);
  uint8_t ipad[64];
  for (uintmax_t _i = 0; _i < (uint32_t )64; ++_i)
    ipad[_i] = (uint8_t )0x36;
  uint32_t *okey_32 = state;
  KRML_CHECK_SIZE((uint8_t )0x00, (uint32_t )64);
  uint8_t okey_8[64];
  for (uintmax_t _i = 0; _i < (uint32_t )64; ++_i)
    okey_8[_i] = (uint8_t )0x00;
  uint32_t *ctx_hash_0 = state + (uint32_t )16;
  Hacl_Hash_SHA2_L256_init(ctx_hash_0);
  hmac_wrap_key(okey_8, key, len);
  load32s_be(okey_32, okey_8, (uint32_t )64);
  xor_bytes(ipad, okey_8, (uint32_t )64);
  uint8_t *s2 = ipad;
  Hacl_Hash_SHA2_L256_update(ctx_hash_0, s2);
}

static void update(uint32_t *state, uint8_t *data)
{
  uint32_t *ctx_hash_0 = state + (uint32_t )16;
  Hacl_Hash_SHA2_L256_update(ctx_hash_0, data);
  return;
}

static void update_multi(uint32_t *state, uint8_t *data, uint32_t n, uint32_t idx)
{
  if (idx == n)
    return;
  else
  {
    uint8_t *b = data + idx * (uint32_t )64;
    update(state, b);
    update_multi(state, data, n, idx + (uint32_t )1);
    return;
  }
}

static void update_last(uint32_t *state, uint8_t *data, uint32_t len)
{
  uint32_t *ctx_hash_0 = state + (uint32_t )16;
  Hacl_Hash_SHA2_L256_update_last(ctx_hash_0, data, len);
  return;
}

static void finish(uint32_t *state, uint8_t *mac)
{
  KRML_CHECK_SIZE((uint8_t )0x5c, (uint32_t )64);
  uint8_t opad[64];
  for (uintmax_t _i = 0; _i < (uint32_t )64; ++_i)
    opad[_i] = (uint8_t )0x5c;
  KRML_CHECK_SIZE((uint8_t )0x00, (uint32_t )32);
  uint8_t s4[32];
  for (uintmax_t _i = 0; _i < (uint32_t )32; ++_i)
    s4[_i] = (uint8_t )0x00;
  KRML_CHECK_SIZE((uint32_t )0, (uint32_t )137);
  uint32_t ctx_hash_1[137] = { 0 };
  uint32_t *ctx_hash_0 = state + (uint32_t )16;
  uint32_t *okey_32 = state;
  KRML_CHECK_SIZE((uint8_t )0x00, (uint32_t )64);
  uint8_t okey_8[64];
  for (uintmax_t _i = 0; _i < (uint32_t )64; ++_i)
    okey_8[_i] = (uint8_t )0x00;
  store32s_be(okey_8, okey_32, (uint32_t )16);
  Hacl_Hash_SHA2_L256_finish(ctx_hash_0, s4);
  xor_bytes(opad, okey_8, (uint32_t )64);
  uint8_t *s5 = opad;
  Hacl_Hash_SHA2_L256_init(ctx_hash_1);
  Hacl_Hash_SHA2_L256_update(ctx_hash_1, s5);
  Hacl_Hash_SHA2_L256_update_last(ctx_hash_1, s4, (uint32_t )32);
  Hacl_Hash_SHA2_L256_finish(ctx_hash_1, mac);
}

static void hmac(uint8_t *mac, uint8_t *key, uint32_t keylen, uint8_t *data, uint32_t datalen)
{
  KRML_CHECK_SIZE(u32_to_s32((uint32_t )0), (uint32_t )153);
  uint32_t ctx[153];
  for (uintmax_t _i = 0; _i < (uint32_t )153; ++_i)
    ctx[_i] = u32_to_s32((uint32_t )0);
  uint32_t n = datalen / (uint32_t )64;
  uint32_t r = datalen % (uint32_t )64;
  init(ctx, key, keylen);
  update_multi(ctx, data, n, (uint32_t )0);
  uint8_t *input_last = data + n * (uint32_t )64;
  update_last(ctx, input_last, r);
  finish(ctx, mac);
}

uint32_t hmac_hashsize_256 = (uint32_t )32;

uint32_t hmac_blocksize_256 = (uint32_t )64;

uint32_t hmac_size_state_256 = (uint32_t )153;

void hmac_sha2_init_256(uint32_t *state, uint8_t *key, uint32_t len)
{
  init(state, key, len);
  return;
}

void hmac_sha2_update_256(uint32_t *state, uint8_t *data)
{
  update(state, data);
  return;
}

void hmac_sha2_update_multi_256(uint32_t *state, uint8_t *data, uint32_t n, uint32_t idx)
{
  update_multi(state, data, n, idx);
  return;
}

void hmac_sha2_update_last_256(uint32_t *state, uint8_t *data, uint32_t len)
{
  update_last(state, data, len);
  return;
}

void hmac_sha2_finish_256(uint32_t *state, uint8_t *mac)
{
  finish(state, mac);
  return;
}

void
hmac_sha2_256(uint8_t *mac, uint8_t *key, uint32_t keylen, uint8_t *data, uint32_t datalen)
{
  hmac(mac, key, keylen, data, datalen);
  return;
}

