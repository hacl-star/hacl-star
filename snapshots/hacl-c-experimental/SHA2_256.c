#include "SHA2_256.h"

uint8_t SHA2_256_u8_to_s8(uint8_t a)
{
  return a;
}

uint32_t SHA2_256_u32_to_s32(uint32_t a)
{
  return a;
}

uint64_t SHA2_256_u32_to_s64(uint32_t a)
{
  return (uint64_t )a;
}

uint8_t SHA2_256_s32_to_s8(uint32_t a)
{
  return (uint8_t )a;
}

uint64_t SHA2_256_s32_to_s64(uint32_t a)
{
  return (uint64_t )a;
}

uint64_t SHA2_256_u64_to_s64(uint64_t a)
{
  return a;
}

uint32_t SHA2_256_hashsize = (uint32_t )32;

uint32_t SHA2_256_blocksize = (uint32_t )64;

uint32_t SHA2_256_size_md_len = (uint32_t )8;

uint32_t SHA2_256_size_k = (uint32_t )64;

uint32_t SHA2_256_size_ws = (uint32_t )64;

uint32_t SHA2_256_size_whash = (uint32_t )8;

uint32_t SHA2_256_size_count = (uint32_t )1;

uint32_t SHA2_256_size_state = (uint32_t )137;

uint32_t SHA2_256_pos_k = (uint32_t )0;

uint32_t SHA2_256_pos_ws = (uint32_t )64;

uint32_t SHA2_256_pos_whash = (uint32_t )128;

uint32_t SHA2_256_pos_count = (uint32_t )136;

uint32_t SHA2_256__Ch(uint32_t x, uint32_t y, uint32_t z)
{
  return x & y ^ ~x & z;
}

uint32_t SHA2_256__Maj(uint32_t x, uint32_t y, uint32_t z)
{
  return x & y ^ x & z ^ y & z;
}

uint32_t SHA2_256__Sigma0(uint32_t x)
{
  return
    Hacl_Utils_Experimental_rotate_right(x,
      (uint32_t )2)
    ^
      Hacl_Utils_Experimental_rotate_right(x,
        (uint32_t )13)
      ^ Hacl_Utils_Experimental_rotate_right(x, (uint32_t )22);
}

uint32_t SHA2_256__Sigma1(uint32_t x)
{
  return
    Hacl_Utils_Experimental_rotate_right(x,
      (uint32_t )6)
    ^
      Hacl_Utils_Experimental_rotate_right(x,
        (uint32_t )11)
      ^ Hacl_Utils_Experimental_rotate_right(x, (uint32_t )25);
}

uint32_t SHA2_256__sigma0(uint32_t x)
{
  return
    Hacl_Utils_Experimental_rotate_right(x,
      (uint32_t )7)
    ^ Hacl_Utils_Experimental_rotate_right(x, (uint32_t )18) ^ x >> (uint32_t )3;
}

uint32_t SHA2_256__sigma1(uint32_t x)
{
  return
    Hacl_Utils_Experimental_rotate_right(x,
      (uint32_t )17)
    ^ Hacl_Utils_Experimental_rotate_right(x, (uint32_t )19) ^ x >> (uint32_t )10;
}

inline void SHA2_256_set_k(uint32_t *state)
{
  uint32_t *k = state;
  Hacl_Utils_Experimental_upd4(k,
    (uint32_t )0,
    (uint32_t )0x428a2f98,
    (uint32_t )0x71374491,
    (uint32_t )0xb5c0fbcf,
    (uint32_t )0xe9b5dba5);
  Hacl_Utils_Experimental_upd4(k,
    (uint32_t )4,
    (uint32_t )0x3956c25b,
    (uint32_t )0x59f111f1,
    (uint32_t )0x923f82a4,
    (uint32_t )0xab1c5ed5);
  Hacl_Utils_Experimental_upd4(k,
    (uint32_t )8,
    (uint32_t )0xd807aa98,
    (uint32_t )0x12835b01,
    (uint32_t )0x243185be,
    (uint32_t )0x550c7dc3);
  Hacl_Utils_Experimental_upd4(k,
    (uint32_t )12,
    (uint32_t )0x72be5d74,
    (uint32_t )0x80deb1fe,
    (uint32_t )0x9bdc06a7,
    (uint32_t )0xc19bf174);
  Hacl_Utils_Experimental_upd4(k,
    (uint32_t )16,
    (uint32_t )0xe49b69c1,
    (uint32_t )0xefbe4786,
    (uint32_t )0x0fc19dc6,
    (uint32_t )0x240ca1cc);
  Hacl_Utils_Experimental_upd4(k,
    (uint32_t )20,
    (uint32_t )0x2de92c6f,
    (uint32_t )0x4a7484aa,
    (uint32_t )0x5cb0a9dc,
    (uint32_t )0x76f988da);
  Hacl_Utils_Experimental_upd4(k,
    (uint32_t )24,
    (uint32_t )0x983e5152,
    (uint32_t )0xa831c66d,
    (uint32_t )0xb00327c8,
    (uint32_t )0xbf597fc7);
  Hacl_Utils_Experimental_upd4(k,
    (uint32_t )28,
    (uint32_t )0xc6e00bf3,
    (uint32_t )0xd5a79147,
    (uint32_t )0x06ca6351,
    (uint32_t )0x14292967);
  Hacl_Utils_Experimental_upd4(k,
    (uint32_t )32,
    (uint32_t )0x27b70a85,
    (uint32_t )0x2e1b2138,
    (uint32_t )0x4d2c6dfc,
    (uint32_t )0x53380d13);
  Hacl_Utils_Experimental_upd4(k,
    (uint32_t )36,
    (uint32_t )0x650a7354,
    (uint32_t )0x766a0abb,
    (uint32_t )0x81c2c92e,
    (uint32_t )0x92722c85);
  Hacl_Utils_Experimental_upd4(k,
    (uint32_t )40,
    (uint32_t )0xa2bfe8a1,
    (uint32_t )0xa81a664b,
    (uint32_t )0xc24b8b70,
    (uint32_t )0xc76c51a3);
  Hacl_Utils_Experimental_upd4(k,
    (uint32_t )44,
    (uint32_t )0xd192e819,
    (uint32_t )0xd6990624,
    (uint32_t )0xf40e3585,
    (uint32_t )0x106aa070);
  Hacl_Utils_Experimental_upd4(k,
    (uint32_t )48,
    (uint32_t )0x19a4c116,
    (uint32_t )0x1e376c08,
    (uint32_t )0x2748774c,
    (uint32_t )0x34b0bcb5);
  Hacl_Utils_Experimental_upd4(k,
    (uint32_t )52,
    (uint32_t )0x391c0cb3,
    (uint32_t )0x4ed8aa4a,
    (uint32_t )0x5b9cca4f,
    (uint32_t )0x682e6ff3);
  Hacl_Utils_Experimental_upd4(k,
    (uint32_t )56,
    (uint32_t )0x748f82ee,
    (uint32_t )0x78a5636f,
    (uint32_t )0x84c87814,
    (uint32_t )0x8cc70208);
  Hacl_Utils_Experimental_upd4(k,
    (uint32_t )60,
    (uint32_t )0x90befffa,
    (uint32_t )0xa4506ceb,
    (uint32_t )0xbef9a3f7,
    (uint32_t )0xc67178f2);
  return;
}

inline void SHA2_256_set_whash(uint32_t *state)
{
  uint32_t *whash = state + (uint32_t )128;
  Hacl_Utils_Experimental_upd4(whash,
    (uint32_t )0,
    (uint32_t )0x6a09e667,
    (uint32_t )0xbb67ae85,
    (uint32_t )0x3c6ef372,
    (uint32_t )0xa54ff53a);
  Hacl_Utils_Experimental_upd4(whash,
    (uint32_t )4,
    (uint32_t )0x510e527f,
    (uint32_t )0x9b05688c,
    (uint32_t )0x1f83d9ab,
    (uint32_t )0x5be0cd19);
  return;
}

inline void SHA2_256_ws_upd(uint32_t *state, uint32_t *wblock, uint32_t t)
{
  uint32_t *ws = state + (uint32_t )64;
  if (t < (uint32_t )16)
  {
    uint32_t _0_34 = wblock[t];
    ws[t] = _0_34;
    SHA2_256_ws_upd(state, wblock, t + (uint32_t )1);
    return;
  }
  else if (t < (uint32_t )64)
  {
    uint32_t _t16 = ws[t - (uint32_t )16];
    uint32_t _t15 = ws[t - (uint32_t )15];
    uint32_t _t7 = ws[t - (uint32_t )7];
    uint32_t _t2 = ws[t - (uint32_t )2];
    uint32_t v0 = SHA2_256__sigma1(_t2);
    uint32_t v1 = SHA2_256__sigma0(_t15);
    uint32_t v = v0 + _t7 + v1 + _t16;
    ws[t] = v;
    SHA2_256_ws_upd(state, wblock, t + (uint32_t )1);
    return;
  }
  else
    return;
}

void SHA2_256_init(uint32_t *state)
{
  SHA2_256_set_k(state);
  SHA2_256_set_whash(state);
  return;
}

inline void SHA2_256_update_inner(uint32_t *state, uint32_t t1, uint32_t t2, uint32_t t)
{
  if (t < (uint32_t )64)
  {
    uint32_t *whash = state + (uint32_t )128;
    uint32_t *k = state;
    uint32_t *ws = state + (uint32_t )64;
    uint32_t _h = whash[7];
    uint32_t _kt = k[t];
    uint32_t _wt = ws[t];
    uint32_t v0 = SHA2_256__Sigma1(whash[4]);
    uint32_t _0_37 = whash[4];
    uint32_t _0_36 = whash[5];
    uint32_t _0_35 = whash[6];
    uint32_t v1 = SHA2_256__Ch(_0_37, _0_36, _0_35);
    uint32_t t1 = _h + v0 + v1 + _kt + _wt;
    uint32_t z0 = SHA2_256__Sigma0(whash[0]);
    uint32_t _0_40 = whash[0];
    uint32_t _0_39 = whash[1];
    uint32_t _0_38 = whash[2];
    uint32_t z1 = SHA2_256__Maj(_0_40, _0_39, _0_38);
    uint32_t t2 = z0 + z1;
    uint32_t _d = whash[3];
    uint32_t _0_41 = whash[6];
    whash[7] = _0_41;
    uint32_t _0_42 = whash[5];
    whash[6] = _0_42;
    uint32_t _0_43 = whash[4];
    whash[5] = _0_43;
    whash[4] = _d + t1;
    uint32_t _0_44 = whash[2];
    whash[3] = _0_44;
    uint32_t _0_45 = whash[1];
    whash[2] = _0_45;
    uint32_t _0_46 = whash[0];
    whash[1] = _0_46;
    whash[0] = t1 + t2;
    SHA2_256_update_inner(state, t1, t2, t + (uint32_t )1);
    return;
  }
  else
    return;
}

void SHA2_256_update(uint32_t *state, uint8_t *data_8)
{
  uint32_t data_32[64];
  for (uintmax_t i = 0; i < (uint32_t )64; ++i)
    data_32[i] = SHA2_256_u32_to_s32((uint32_t )0);
  Hacl_Utils_Experimental_be_uint32s_of_bytes(data_32, data_8, (uint32_t )64);
  uint32_t *whash = state + (uint32_t )128;
  SHA2_256_ws_upd(state, data_32, (uint32_t )0);
  uint32_t input_state0 = whash[0];
  uint32_t input_state1 = whash[1];
  uint32_t input_state2 = whash[2];
  uint32_t input_state3 = whash[3];
  uint32_t input_state4 = whash[4];
  uint32_t input_state5 = whash[5];
  uint32_t input_state6 = whash[6];
  uint32_t input_state7 = whash[7];
  SHA2_256_update_inner(state,
    SHA2_256_u32_to_s32((uint32_t )0),
    SHA2_256_u32_to_s32((uint32_t )0),
    (uint32_t )0);
  uint32_t current_state0 = whash[0];
  uint32_t current_state1 = whash[1];
  uint32_t current_state2 = whash[2];
  uint32_t current_state3 = whash[3];
  uint32_t current_state4 = whash[4];
  uint32_t current_state5 = whash[5];
  uint32_t current_state6 = whash[6];
  uint32_t current_state7 = whash[7];
  uint32_t output_state0 = current_state0 + input_state0;
  uint32_t output_state1 = current_state1 + input_state1;
  uint32_t output_state2 = current_state2 + input_state2;
  uint32_t output_state3 = current_state3 + input_state3;
  uint32_t output_state4 = current_state4 + input_state4;
  uint32_t output_state5 = current_state5 + input_state5;
  uint32_t output_state6 = current_state6 + input_state6;
  uint32_t output_state7 = current_state7 + input_state7;
  whash[0] = output_state0;
  whash[1] = output_state1;
  whash[2] = output_state2;
  whash[3] = output_state3;
  whash[4] = output_state4;
  whash[5] = output_state5;
  whash[6] = output_state6;
  whash[7] = output_state7;
  uint32_t pc = state[136];
  uint32_t npc = pc + SHA2_256_u32_to_s32((uint32_t )1);
  state[136] = npc;
}

void SHA2_256_update_multi(uint32_t *state, uint8_t *data, uint32_t n, uint32_t idx)
{
  if (idx == n)
    return;
  else
  {
    uint8_t *b = data + idx * (uint32_t )64;
    SHA2_256_update(state, b);
    SHA2_256_update_multi(state, data, n, idx + (uint32_t )1);
    return;
  }
}

void SHA2_256_update_last(uint32_t *state, uint8_t *data, uint32_t len)
{
  uint8_t len_64[8] = { 0 };
  uint8_t blocks[128] = { 0 };
  memcpy(blocks, data, len * sizeof data[0]);
  blocks[len] = SHA2_256_u8_to_s8((uint8_t )0x80);
  uint32_t count = state[136];
  uint64_t l_0 = SHA2_256_s32_to_s64(count) * SHA2_256_u32_to_s64((uint32_t )64);
  uint64_t l_1 = SHA2_256_u32_to_s64(len);
  uint64_t t_0 = (l_0 + l_1) * SHA2_256_u32_to_s64((uint32_t )8);
  Hacl_Utils_Experimental_be_bytes_of_sint64(len_64, t_0);
  if (len < (uint32_t )55)
  {
    memcpy(blocks + (uint32_t )56, len_64, (uint32_t )8 * sizeof len_64[0]);
    uint8_t *block_0 = blocks;
    SHA2_256_update(state, block_0);
  }
  else
  {
    memcpy(blocks + (uint32_t )120, len_64, (uint32_t )8 * sizeof len_64[0]);
    uint8_t *block_0 = blocks;
    uint8_t *block_1 = blocks + (uint32_t )64;
    SHA2_256_update(state, block_0);
    SHA2_256_update(state, block_1);
  }
}

void SHA2_256_finish(uint32_t *state, uint8_t *hash)
{
  uint32_t *whash = state + (uint32_t )128;
  Hacl_Utils_Experimental_be_bytes_of_uint32s(hash, whash, (uint32_t )32);
  return;
}

void SHA2_256_hash(uint8_t *hash, uint8_t *input, uint32_t len)
{
  uint32_t ctx[137];
  for (uintmax_t i = 0; i < (uint32_t )137; ++i)
    ctx[i] = SHA2_256_u32_to_s32((uint32_t )0);
  uint32_t n = len / (uint32_t )64;
  uint32_t r = len % (uint32_t )64;
  SHA2_256_init(ctx);
  SHA2_256_update_multi(ctx, input, n, (uint32_t )0);
  uint8_t *input_last = input + n * (uint32_t )64;
  SHA2_256_update_last(ctx, input_last, r);
  SHA2_256_finish(ctx, hash);
}

