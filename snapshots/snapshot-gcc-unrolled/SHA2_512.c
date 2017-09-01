#include "SHA2_512.h"

static void
Hacl_Hash_Lib_LoadStore_uint64s_from_be_bytes(uint64_t *output, uint8_t *input, uint32_t len)
{
  for (uint32_t i = (uint32_t )0; i < len; i = i + (uint32_t )1)
  {
    uint8_t *x0 = input + (uint32_t )8 * i;
    uint64_t inputi = load64_be(x0);
    output[i] = inputi;
  }
}

static void
Hacl_Hash_Lib_LoadStore_uint64s_to_be_bytes(uint8_t *output, uint64_t *input, uint32_t len)
{
  for (uint32_t i = (uint32_t )0; i < len; i = i + (uint32_t )1)
  {
    uint64_t hd1 = input[i];
    uint8_t *x0 = output + (uint32_t )8 * i;
    store64_be(x0, hd1);
  }
}

static void Hacl_Hash_SHA2_512_init(uint64_t *state)
{
  (void )(state + (uint32_t )168);
  uint64_t *k1 = state;
  uint64_t *h_01 = state + (uint32_t )160;
  uint64_t *p10 = k1;
  uint64_t *p20 = k1 + (uint32_t )16;
  uint64_t *p3 = k1 + (uint32_t )32;
  uint64_t *p4 = k1 + (uint32_t )48;
  uint64_t *p5 = k1 + (uint32_t )64;
  uint64_t *p11 = p10;
  uint64_t *p21 = p10 + (uint32_t )8;
  uint64_t *p12 = p11;
  uint64_t *p22 = p11 + (uint32_t )4;
  p12[0] = (uint64_t )0x428a2f98d728ae22;
  p12[1] = (uint64_t )0x7137449123ef65cd;
  p12[2] = (uint64_t )0xb5c0fbcfec4d3b2f;
  p12[3] = (uint64_t )0xe9b5dba58189dbbc;
  p22[0] = (uint64_t )0x3956c25bf348b538;
  p22[1] = (uint64_t )0x59f111f1b605d019;
  p22[2] = (uint64_t )0x923f82a4af194f9b;
  p22[3] = (uint64_t )0xab1c5ed5da6d8118;
  uint64_t *p13 = p21;
  uint64_t *p23 = p21 + (uint32_t )4;
  p13[0] = (uint64_t )0xd807aa98a3030242;
  p13[1] = (uint64_t )0x12835b0145706fbe;
  p13[2] = (uint64_t )0x243185be4ee4b28c;
  p13[3] = (uint64_t )0x550c7dc3d5ffb4e2;
  p23[0] = (uint64_t )0x72be5d74f27b896f;
  p23[1] = (uint64_t )0x80deb1fe3b1696b1;
  p23[2] = (uint64_t )0x9bdc06a725c71235;
  p23[3] = (uint64_t )0xc19bf174cf692694;
  uint64_t *p14 = p20;
  uint64_t *p24 = p20 + (uint32_t )8;
  uint64_t *p15 = p14;
  uint64_t *p25 = p14 + (uint32_t )4;
  p15[0] = (uint64_t )0xe49b69c19ef14ad2;
  p15[1] = (uint64_t )0xefbe4786384f25e3;
  p15[2] = (uint64_t )0x0fc19dc68b8cd5b5;
  p15[3] = (uint64_t )0x240ca1cc77ac9c65;
  p25[0] = (uint64_t )0x2de92c6f592b0275;
  p25[1] = (uint64_t )0x4a7484aa6ea6e483;
  p25[2] = (uint64_t )0x5cb0a9dcbd41fbd4;
  p25[3] = (uint64_t )0x76f988da831153b5;
  uint64_t *p16 = p24;
  uint64_t *p26 = p24 + (uint32_t )4;
  p16[0] = (uint64_t )0x983e5152ee66dfab;
  p16[1] = (uint64_t )0xa831c66d2db43210;
  p16[2] = (uint64_t )0xb00327c898fb213f;
  p16[3] = (uint64_t )0xbf597fc7beef0ee4;
  p26[0] = (uint64_t )0xc6e00bf33da88fc2;
  p26[1] = (uint64_t )0xd5a79147930aa725;
  p26[2] = (uint64_t )0x06ca6351e003826f;
  p26[3] = (uint64_t )0x142929670a0e6e70;
  uint64_t *p17 = p3;
  uint64_t *p27 = p3 + (uint32_t )8;
  uint64_t *p18 = p17;
  uint64_t *p28 = p17 + (uint32_t )4;
  p18[0] = (uint64_t )0x27b70a8546d22ffc;
  p18[1] = (uint64_t )0x2e1b21385c26c926;
  p18[2] = (uint64_t )0x4d2c6dfc5ac42aed;
  p18[3] = (uint64_t )0x53380d139d95b3df;
  p28[0] = (uint64_t )0x650a73548baf63de;
  p28[1] = (uint64_t )0x766a0abb3c77b2a8;
  p28[2] = (uint64_t )0x81c2c92e47edaee6;
  p28[3] = (uint64_t )0x92722c851482353b;
  uint64_t *p19 = p27;
  uint64_t *p29 = p27 + (uint32_t )4;
  p19[0] = (uint64_t )0xa2bfe8a14cf10364;
  p19[1] = (uint64_t )0xa81a664bbc423001;
  p19[2] = (uint64_t )0xc24b8b70d0f89791;
  p19[3] = (uint64_t )0xc76c51a30654be30;
  p29[0] = (uint64_t )0xd192e819d6ef5218;
  p29[1] = (uint64_t )0xd69906245565a910;
  p29[2] = (uint64_t )0xf40e35855771202a;
  p29[3] = (uint64_t )0x106aa07032bbd1b8;
  uint64_t *p110 = p4;
  uint64_t *p210 = p4 + (uint32_t )8;
  uint64_t *p111 = p110;
  uint64_t *p211 = p110 + (uint32_t )4;
  p111[0] = (uint64_t )0x19a4c116b8d2d0c8;
  p111[1] = (uint64_t )0x1e376c085141ab53;
  p111[2] = (uint64_t )0x2748774cdf8eeb99;
  p111[3] = (uint64_t )0x34b0bcb5e19b48a8;
  p211[0] = (uint64_t )0x391c0cb3c5c95a63;
  p211[1] = (uint64_t )0x4ed8aa4ae3418acb;
  p211[2] = (uint64_t )0x5b9cca4f7763e373;
  p211[3] = (uint64_t )0x682e6ff3d6b2b8a3;
  uint64_t *p112 = p210;
  uint64_t *p212 = p210 + (uint32_t )4;
  p112[0] = (uint64_t )0x748f82ee5defb2fc;
  p112[1] = (uint64_t )0x78a5636f43172f60;
  p112[2] = (uint64_t )0x84c87814a1f0ab72;
  p112[3] = (uint64_t )0x8cc702081a6439ec;
  p212[0] = (uint64_t )0x90befffa23631e28;
  p212[1] = (uint64_t )0xa4506cebde82bde9;
  p212[2] = (uint64_t )0xbef9a3f7b2c67915;
  p212[3] = (uint64_t )0xc67178f2e372532b;
  uint64_t *p113 = p5;
  uint64_t *p213 = p5 + (uint32_t )8;
  uint64_t *p1 = p113;
  uint64_t *p214 = p113 + (uint32_t )4;
  p1[0] = (uint64_t )0xca273eceea26619c;
  p1[1] = (uint64_t )0xd186b8c721c0c207;
  p1[2] = (uint64_t )0xeada7dd6cde0eb1e;
  p1[3] = (uint64_t )0xf57d4f7fee6ed178;
  p214[0] = (uint64_t )0x06f067aa72176fba;
  p214[1] = (uint64_t )0x0a637dc5a2c898a6;
  p214[2] = (uint64_t )0x113f9804bef90dae;
  p214[3] = (uint64_t )0x1b710b35131c471b;
  uint64_t *p114 = p213;
  uint64_t *p215 = p213 + (uint32_t )4;
  p114[0] = (uint64_t )0x28db77f523047d84;
  p114[1] = (uint64_t )0x32caab7b40c72493;
  p114[2] = (uint64_t )0x3c9ebe0a15c9bebc;
  p114[3] = (uint64_t )0x431d67c49c100d4c;
  p215[0] = (uint64_t )0x4cc5d4becb3e42b6;
  p215[1] = (uint64_t )0x597f299cfc657e2a;
  p215[2] = (uint64_t )0x5fcb6fab3ad6faec;
  p215[3] = (uint64_t )0x6c44198c4a475817;
  uint64_t *p115 = h_01;
  uint64_t *p2 = h_01 + (uint32_t )4;
  p115[0] = (uint64_t )0x6a09e667f3bcc908;
  p115[1] = (uint64_t )0xbb67ae8584caa73b;
  p115[2] = (uint64_t )0x3c6ef372fe94f82b;
  p115[3] = (uint64_t )0xa54ff53a5f1d36f1;
  p2[0] = (uint64_t )0x510e527fade682d1;
  p2[1] = (uint64_t )0x9b05688c2b3e6c1f;
  p2[2] = (uint64_t )0x1f83d9abfb41bd6b;
  p2[3] = (uint64_t )0x5be0cd19137e2179;
}

static void Hacl_Hash_SHA2_512_update(uint64_t *state, uint8_t *data)
{
  KRML_CHECK_SIZE((uint64_t )(uint32_t )0, (uint32_t )16);
  uint64_t data_w[16];
  for (uintmax_t _i = 0; _i < (uint32_t )16; ++_i)
    data_w[_i] = (uint64_t )(uint32_t )0;
  Hacl_Hash_Lib_LoadStore_uint64s_from_be_bytes(data_w, data, (uint32_t )16);
  uint64_t *hash_w = state + (uint32_t )160;
  uint64_t *ws_w = state + (uint32_t )80;
  uint64_t *k_w = state;
  uint64_t *counter_w = state + (uint32_t )168;
  for (uint32_t i = (uint32_t )0; i < (uint32_t )16; i = i + (uint32_t )1)
  {
    uint64_t uu____242 = data_w[i];
    ws_w[i] = uu____242;
  }
  for (uint32_t i = (uint32_t )16; i < (uint32_t )80; i = i + (uint32_t )1)
  {
    uint64_t t16 = ws_w[i - (uint32_t )16];
    uint64_t t15 = ws_w[i - (uint32_t )15];
    uint64_t t7 = ws_w[i - (uint32_t )7];
    uint64_t t2 = ws_w[i - (uint32_t )2];
    ws_w[i] =
      ((t2 >> (uint32_t )19 | t2 << (uint32_t )64 - (uint32_t )19)
      ^ (t2 >> (uint32_t )61 | t2 << (uint32_t )64 - (uint32_t )61) ^ t2 >> (uint32_t )6)
      +
        t7
        +
          ((t15 >> (uint32_t )1 | t15 << (uint32_t )64 - (uint32_t )1)
          ^ (t15 >> (uint32_t )8 | t15 << (uint32_t )64 - (uint32_t )8) ^ t15 >> (uint32_t )7)
          + t16;
  }
  uint64_t hash_0[8] = { 0 };
  memcpy(hash_0, hash_w, (uint32_t )8 * sizeof hash_w[0]);
  for (uint32_t i = (uint32_t )0; i < (uint32_t )80; i = i + (uint32_t )1)
  {
    uint64_t a = hash_0[0];
    uint64_t b = hash_0[1];
    uint64_t c = hash_0[2];
    uint64_t d = hash_0[3];
    uint64_t e = hash_0[4];
    uint64_t f1 = hash_0[5];
    uint64_t g = hash_0[6];
    uint64_t h = hash_0[7];
    uint64_t k_t = k_w[i];
    uint64_t ws_t = ws_w[i];
    uint64_t
    t1 =
      h
      +
        ((e >> (uint32_t )14 | e << (uint32_t )64 - (uint32_t )14)
        ^
          (e >> (uint32_t )18 | e << (uint32_t )64 - (uint32_t )18)
          ^ (e >> (uint32_t )41 | e << (uint32_t )64 - (uint32_t )41))
      + (e & f1 ^ ~e & g)
      + k_t
      + ws_t;
    uint64_t
    t2 =
      ((a >> (uint32_t )28 | a << (uint32_t )64 - (uint32_t )28)
      ^
        (a >> (uint32_t )34 | a << (uint32_t )64 - (uint32_t )34)
        ^ (a >> (uint32_t )39 | a << (uint32_t )64 - (uint32_t )39))
      + (a & b ^ a & c ^ b & c);
    uint64_t x1 = t1 + t2;
    uint64_t x5 = d + t1;
    uint64_t *p1 = hash_0;
    uint64_t *p2 = hash_0 + (uint32_t )4;
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
    uint64_t uu____871 = hash_w[i];
    uint64_t uu____874 = hash_0[i];
    uint64_t uu____870 = uu____871 + uu____874;
    hash_w[i] = uu____870;
  }
  uint64_t c0 = counter_w[0];
  uint64_t one1 = (uint64_t )(uint32_t )1;
  counter_w[0] = c0 + one1;
}

static void Hacl_Hash_SHA2_512_update_multi(uint64_t *state, uint8_t *data, uint32_t n1)
{
  for (uint32_t i = (uint32_t )0; i < n1; i = i + (uint32_t )1)
  {
    uint8_t *b = data + i * (uint32_t )128;
    Hacl_Hash_SHA2_512_update(state, b);
  }
}

static void Hacl_Hash_SHA2_512_update_last(uint64_t *state, uint8_t *data, uint64_t len)
{
  uint8_t blocks[256] = { 0 };
  uint32_t nb;
  if (len < (uint64_t )112)
    nb = (uint32_t )1;
  else
    nb = (uint32_t )2;
  uint8_t *final_blocks;
  if (len < (uint64_t )112)
    final_blocks = blocks + (uint32_t )128;
  else
    final_blocks = blocks;
  memcpy(final_blocks, data, (uint32_t )len * sizeof data[0]);
  uint64_t n1 = state[168];
  uint8_t *padding = final_blocks + (uint32_t )len;
  FStar_UInt128_t
  encodedlen =
    FStar_UInt128_shift_left(FStar_UInt128_add(FStar_UInt128_mul_wide(n1,
          (uint64_t )(uint32_t )128),
        FStar_Int_Cast_Full_uint64_to_uint128(len)),
      (uint32_t )3);
  uint32_t
  pad0len = ((uint32_t )256 - ((uint32_t )len + (uint32_t )16 + (uint32_t )1)) % (uint32_t )128;
  uint8_t *buf1 = padding;
  (void )(padding + (uint32_t )1);
  uint8_t *buf2 = padding + (uint32_t )1 + pad0len;
  buf1[0] = (uint8_t )0x80;
  store128_be(buf2, encodedlen);
  Hacl_Hash_SHA2_512_update_multi(state, final_blocks, nb);
}

static void Hacl_Hash_SHA2_512_finish(uint64_t *state, uint8_t *hash1)
{
  uint64_t *hash_w = state + (uint32_t )160;
  Hacl_Hash_Lib_LoadStore_uint64s_to_be_bytes(hash1, hash_w, (uint32_t )8);
}

static void Hacl_Hash_SHA2_512_hash(uint8_t *hash1, uint8_t *input, uint32_t len)
{
  KRML_CHECK_SIZE((uint64_t )(uint32_t )0, (uint32_t )169);
  uint64_t state[169];
  for (uintmax_t _i = 0; _i < (uint32_t )169; ++_i)
    state[_i] = (uint64_t )(uint32_t )0;
  uint32_t n1 = len / (uint32_t )128;
  uint32_t r = len % (uint32_t )128;
  uint8_t *input_blocks = input;
  uint8_t *input_last = input + n1 * (uint32_t )128;
  Hacl_Hash_SHA2_512_init(state);
  Hacl_Hash_SHA2_512_update_multi(state, input_blocks, n1);
  Hacl_Hash_SHA2_512_update_last(state, input_last, (uint64_t )r);
  Hacl_Hash_SHA2_512_finish(state, hash1);
}

uint32_t SHA2_512_size_word = (uint32_t )8;

uint32_t SHA2_512_size_hash_w = (uint32_t )8;

uint32_t SHA2_512_size_block_w = (uint32_t )16;

uint32_t SHA2_512_size_hash = (uint32_t )64;

uint32_t SHA2_512_size_block = (uint32_t )128;

uint32_t SHA2_512_size_k_w = (uint32_t )80;

uint32_t SHA2_512_size_ws_w = (uint32_t )80;

uint32_t SHA2_512_size_whash_w = (uint32_t )8;

uint32_t SHA2_512_size_count_w = (uint32_t )1;

uint32_t SHA2_512_size_len_8 = (uint32_t )16;

uint32_t SHA2_512_size_state = (uint32_t )169;

uint32_t SHA2_512_pos_k_w = (uint32_t )0;

uint32_t SHA2_512_pos_ws_w = (uint32_t )80;

uint32_t SHA2_512_pos_whash_w = (uint32_t )160;

uint32_t SHA2_512_pos_count_w = (uint32_t )168;

void SHA2_512_init(uint64_t *state)
{
  Hacl_Hash_SHA2_512_init(state);
}

void SHA2_512_update(uint64_t *state, uint8_t *data)
{
  Hacl_Hash_SHA2_512_update(state, data);
}

void SHA2_512_update_multi(uint64_t *state, uint8_t *data, uint32_t n1)
{
  Hacl_Hash_SHA2_512_update_multi(state, data, n1);
}

void SHA2_512_update_last(uint64_t *state, uint8_t *data, uint64_t len)
{
  Hacl_Hash_SHA2_512_update_last(state, data, len);
}

void SHA2_512_finish(uint64_t *state, uint8_t *hash1)
{
  Hacl_Hash_SHA2_512_finish(state, hash1);
}

void SHA2_512_hash(uint8_t *hash1, uint8_t *input, uint32_t len)
{
  Hacl_Hash_SHA2_512_hash(hash1, input, len);
}

