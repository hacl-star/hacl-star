#include "Hacl_Utils_Experimental.h"

uint8_t Hacl_Utils_Experimental_u8_to_s8(uint8_t a)
{
  return a;
}

uint32_t Hacl_Utils_Experimental_u32_to_s32(uint32_t a)
{
  return a;
}

uint64_t Hacl_Utils_Experimental_u32_to_s64(uint32_t a)
{
  return (uint64_t )a;
}

uint8_t Hacl_Utils_Experimental_s32_to_s8(uint32_t a)
{
  return (uint8_t )a;
}

uint64_t Hacl_Utils_Experimental_s32_to_s64(uint32_t a)
{
  return (uint64_t )a;
}

uint64_t Hacl_Utils_Experimental_u64_to_s64(uint64_t a)
{
  return a;
}

inline void
Hacl_Utils_Experimental_upd4(
  uint32_t *buf,
  uint32_t idx,
  uint32_t a,
  uint32_t b,
  uint32_t c,
  uint32_t d
)
{
  buf[idx + (uint32_t )0] = Hacl_Utils_Experimental_u32_to_s32(a);
  buf[idx + (uint32_t )1] = Hacl_Utils_Experimental_u32_to_s32(b);
  buf[idx + (uint32_t )2] = Hacl_Utils_Experimental_u32_to_s32(c);
  buf[idx + (uint32_t )3] = Hacl_Utils_Experimental_u32_to_s32(d);
}

uint32_t Hacl_Utils_Experimental_rotate_right(uint32_t a, uint32_t b)
{
  return a >> b | a << (uint32_t )32 - b;
}

void Hacl_Utils_Experimental_be_bytes_of_sint32(uint8_t *output, uint32_t x)
{
  uint8_t b0 = (uint8_t )(x >> (uint32_t )24 & (uint32_t )255);
  uint8_t b1 = (uint8_t )(x >> (uint32_t )16 & (uint32_t )255);
  uint8_t b2 = (uint8_t )(x >> (uint32_t )8 & (uint32_t )255);
  uint8_t b3 = (uint8_t )(x & (uint32_t )255);
  output[0] = b0;
  output[1] = b1;
  output[2] = b2;
  output[3] = b3;
}

uint32_t Hacl_Utils_Experimental_be_sint32_of_bytes(uint8_t *b)
{
  uint8_t b0 = b[0];
  uint8_t b1 = b[1];
  uint8_t b2 = b[2];
  uint8_t b3 = b[3];
  return
    (uint32_t )b3
    + ((uint32_t )b2 << (uint32_t )8)
    + ((uint32_t )b1 << (uint32_t )16)
    + ((uint32_t )b0 << (uint32_t )24);
}

void Hacl_Utils_Experimental_be_bytes_of_sint64(uint8_t *output, uint64_t x)
{
  uint8_t b0 = (uint8_t )(x >> (uint32_t )56 & (uint64_t )(uint32_t )255);
  uint8_t b1 = (uint8_t )(x >> (uint32_t )48 & (uint64_t )(uint32_t )255);
  uint8_t b2 = (uint8_t )(x >> (uint32_t )40 & (uint64_t )(uint32_t )255);
  uint8_t b3 = (uint8_t )(x >> (uint32_t )32 & (uint64_t )(uint32_t )255);
  uint8_t b4 = (uint8_t )(x >> (uint32_t )24 & (uint64_t )(uint32_t )255);
  uint8_t b5 = (uint8_t )(x >> (uint32_t )16 & (uint64_t )(uint32_t )255);
  uint8_t b6 = (uint8_t )(x >> (uint32_t )8 & (uint64_t )(uint32_t )255);
  uint8_t b7 = (uint8_t )(x & (uint64_t )(uint32_t )255);
  output[0] = b0;
  output[1] = b1;
  output[2] = b2;
  output[3] = b3;
  output[4] = b4;
  output[5] = b5;
  output[6] = b6;
  output[7] = b7;
}

void Hacl_Utils_Experimental_xor_bytes(uint8_t *output, uint8_t *input, uint32_t len)
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
    Hacl_Utils_Experimental_xor_bytes(output, input, i);
    return;
  }
}

void Hacl_Utils_Experimental_be_bytes_of_uint32s(uint8_t *output, uint32_t *m, uint32_t len)
{
  if (len == (uint32_t )0)
    return;
  else
  {
    uint32_t l40 = len / (uint32_t )4;
    uint32_t l = l40 - (uint32_t )1;
    uint32_t x = m[l];
    uint8_t
    b0 =
      Hacl_Utils_Experimental_s32_to_s8(x
        >> (uint32_t )24
        & Hacl_Utils_Experimental_u32_to_s32((uint32_t )255));
    uint8_t
    b1 =
      Hacl_Utils_Experimental_s32_to_s8(x
        >> (uint32_t )16
        & Hacl_Utils_Experimental_u32_to_s32((uint32_t )255));
    uint8_t
    b2 =
      Hacl_Utils_Experimental_s32_to_s8(x
        >> (uint32_t )8
        & Hacl_Utils_Experimental_u32_to_s32((uint32_t )255));
    uint8_t
    b3 = Hacl_Utils_Experimental_s32_to_s8(x & Hacl_Utils_Experimental_u32_to_s32((uint32_t )255));
    uint32_t l4 = len - (uint32_t )4;
    output[l4] = b0;
    output[l4 + (uint32_t )1] = b1;
    output[l4 + (uint32_t )2] = b2;
    output[l4 + (uint32_t )3] = b3;
    Hacl_Utils_Experimental_be_bytes_of_uint32s(output, m, l4);
    return;
  }
}

void Hacl_Utils_Experimental_be_uint32s_of_bytes(uint32_t *u, uint8_t *b, uint32_t len)
{
  if (len == (uint32_t )0)
    return;
  else
  {
    uint32_t l4 = len / (uint32_t )4;
    uint32_t _0_33 = Hacl_Utils_Experimental_be_sint32_of_bytes(b + len - (uint32_t )4);
    u[l4 - (uint32_t )1] = _0_33;
    Hacl_Utils_Experimental_be_uint32s_of_bytes(u, b, len - (uint32_t )4);
    return;
  }
}

