/* Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
   Licensed under the Apache 2.0 License. */

/******************************************************************************/
/* NOT LOW*: implementing FStar.Bytes.bytes as leaky fat pointers with a      */
/* length                                                                     */
/******************************************************************************/

#include "FStar_Bytes.h"
#include "Prims.h"
#include "FStar_Int_Cast_Full.h"

typedef uint8_t FStar_Bytes_byte;

#define CHECK(x)                                                               \
  do {                                                                         \
    if (!(x)) {                                                                \
      KRML_HOST_EPRINTF("malloc failed at %s:%d", __FILE__, __LINE__);         \
      KRML_HOST_EXIT(253);                                                     \
    }                                                                          \
  } while (0)

FStar_Bytes_bytes FStar_Bytes_copy(FStar_Bytes_bytes b1) {
  return b1;
}

krml_checked_int_t FStar_Bytes_length(FStar_Bytes_bytes b) {
  return b.length;
}

FStar_Bytes_bytes FStar_Bytes_empty_bytes = { .length = 0, .data = NULL };

FStar_Bytes_byte
FStar_Bytes_get(FStar_Bytes_bytes b, uint32_t i) {
  return (FStar_Bytes_byte)b.data[i];
}

FStar_Bytes_bytes
FStar_Bytes_set_byte(FStar_Bytes_bytes b1, uint32_t i, FStar_Bytes_byte v) {
  char *data = KRML_HOST_MALLOC(b1.length);
  CHECK(data);
  memcpy(data, b1.data, b1.length);
  data[i] = v;
  FStar_Bytes_bytes b2 = { .length = b1.length, .data = data };
  return b2;
}

FStar_Bytes_bytes
FStar_Bytes_create(uint32_t length, FStar_Bytes_byte initial) {
  char *data = KRML_HOST_MALLOC(length);
  CHECK(data);
  memset(data, initial, length);
  FStar_Bytes_bytes b = { .length = length, .data = data };
  return b;
}

FStar_Bytes_bytes
FStar_Bytes_init(uint32_t length, FStar_Bytes_byte (*initial)(uint32_t i)) {
  char *data = KRML_HOST_MALLOC(length);
  CHECK(data);
  for (uint32_t i = 0; i < length; ++i)
    data[i] = initial(i);
  FStar_Bytes_bytes b = { .length = length, .data = data };
  return b;
}

FStar_Bytes_bytes FStar_Bytes_abyte(FStar_Bytes_byte v1) {
  char *data = KRML_HOST_MALLOC(1);
  CHECK(data);
  data[0] = v1;
  FStar_Bytes_bytes b = { .length = 1, .data = data };
  return b;
}

FStar_Bytes_bytes FStar_Bytes_twobytes_(K___uint8_t_uint8_t *v) {
  char *data = KRML_HOST_MALLOC(2);
  CHECK(data);
  data[0] = v->fst;
  data[1] = v->snd;
  FStar_Bytes_bytes b = { .length = 2, .data = data };
  return b;
}

#ifdef KRML_NOSTRUCT_PASSING
#define FStar_Bytes_twobytes FStar_Bytes_twobytes_
#else
FStar_Bytes_bytes FStar_Bytes_twobytes(K___uint8_t_uint8_t v) {
  return FStar_Bytes_twobytes_(&v);
}
#endif

FStar_Bytes_bytes
FStar_Bytes_append(FStar_Bytes_bytes b1, FStar_Bytes_bytes b2) {
  // Overflow check
  uint32_t length = Prims_op_Addition(b1.length, b2.length);
  char *data = KRML_HOST_MALLOC(length);
  CHECK(data);
  if (b1.length > 0)
    memcpy(data, b1.data, b1.length);
  if (b2.length > 0)
    memcpy(data + b1.length, b2.data, b2.length);
  FStar_Bytes_bytes b = { .length = length, .data = data };
  return b;
}

FStar_Bytes_bytes
FStar_Bytes_slice(FStar_Bytes_bytes b1, uint32_t s, uint32_t e) {
  if (s == e)
    return FStar_Bytes_empty_bytes;
  if (s > e) {
    KRML_HOST_EPRINTF("!! s > e in FStar_Bytes_slice\n");
    KRML_HOST_EXIT(254);
  }

  uint32_t length = e - s;
  char *data = KRML_HOST_MALLOC(length);
  CHECK(data);
  memcpy(data, b1.data + s, length);
  FStar_Bytes_bytes b = { .length = length, .data = data };
  return b;
}

FStar_Bytes_bytes
FStar_Bytes_sub(FStar_Bytes_bytes b1, uint32_t s, uint32_t l) {
  return FStar_Bytes_slice(b1, s, Prims_op_Addition(s, l));
}

FStar_Bytes_bytes FStar_Bytes_utf8_encode(const char *str) {
  // Note: the original signature wants a Prims.string, which is GC-backed,
  // heap-allocated and immutable. So, it's fine to skip the copy (famous last
  // words?).
  // F* ought to guarantee at some point that i) strings are utf8-encoded and
  // ii) zero-terminated, so we can just see utf8 as bytes by using strlen which
  // is utf8-UNaware.
  FStar_Bytes_bytes b = { .length = strlen(str), .data = str };
  return b;
}

// DEPRECATED
FStar_Bytes_bytes FStar_Bytes_bytes_of_string(const char *str) {
  return FStar_Bytes_utf8_encode(str);
}

void
FStar_Bytes_split__(FStar_Bytes_bytes bs, FStar_UInt32_t i, K___FStar_Bytes_bytes_FStar_Bytes_bytes *dst) {
  dst->fst = FStar_Bytes_slice(bs, 0, i);
  dst->snd = FStar_Bytes_slice(bs, i, bs.length);
}

#ifdef KRML_NOSTRUCT_PASSING
#define FStar_Bytes_split FStar_Bytes_split__
#else
K___FStar_Bytes_bytes_FStar_Bytes_bytes
FStar_Bytes_split(FStar_Bytes_bytes bs, FStar_UInt32_t i) {
  K___FStar_Bytes_bytes_FStar_Bytes_bytes p;
  FStar_Bytes_split__(bs, i, &p);
  return p;
}
#endif

FStar_UInt32_t FStar_Bytes_len(FStar_Bytes_bytes b1) {
  return b1.length;
}

// Right-shifts for negative values at a signed type are undefined behavior in
// C. However, the precondition of the function guarantees that `n` is a `nat`,
// meaning that if it overflew we'd catch it.
FStar_Bytes_bytes
FStar_Bytes_bytes_of_int(krml_checked_int_t k, krml_checked_int_t n) {
  if (n < 0) {
    KRML_HOST_EPRINTF("FStar_Bytes_bytes_of_int: n must be nonnegative\n");
    KRML_HOST_EXIT(252);
  }
  FStar_Bytes_bytes b = FStar_Bytes_create(k, 0);
  char *data = (char *)b.data;
  krml_checked_int_t m = n;
  for (krml_checked_int_t j = 0; j < k; ++j) {
    data[k - 1 - j] = m & 0xFF;
    m = m >> 8;
  }
  return b;
}

#ifdef KRML_NOSTRUCT_PASSING
static inline
void FStar_Bytes_uint128_of_bytes(FStar_Bytes_bytes bs, uint128_t *dst) {
  KRML_HOST_EPRINTF("FStar_Bytes_uint128_of_bytes: not implemented\n");
  KRML_HOST_EXIT(251);
}
#else
uint128_t
FStar_Bytes_uint128_of_bytes(FStar_Bytes_bytes bs) {
  uint128_t res = FStar_Int_Cast_Full_uint64_to_uint128(UINT64_C(0));
  for (uint32_t i = 0; i < bs.length; i++) {
    res = FStar_UInt128_shift_left(res, UINT32_C(8));
    res = FStar_UInt128_logxor(res, FStar_Int_Cast_Full_uint64_to_uint128(bs.data[i] & 0xFF));
  }
  return res;
}
#endif

krml_checked_int_t
FStar_Bytes_int_of_bytes(FStar_Bytes_bytes bs) {
  if (bs.length > 4) {
    KRML_HOST_EPRINTF("int_of_bytes overflow\n");
    KRML_HOST_EXIT(255);
  }
  krml_checked_int_t res = 0;
  for (uint32_t i = 0; i < bs.length; i++) {
    res = res << 8;
    // Note: this is a char, whose signedness is unspecified, so it may get an
    // evil sign-extension -- mask.
    res |= bs.data[i] & 0xFF;
  }
  return res;
}


krml_checked_int_t FStar_Bytes_repr_bytes(Prims_nat bs) {
  if (bs < 0x100)
    return 1;
  else if (bs < 0x10000)
    return 2;
  else if (bs < 0x1000000)
    return 3;
  else
    return 4;
}

FStar_Bytes_bytes
FStar_Bytes_xor(FStar_UInt32_t x, FStar_Bytes_bytes b1, FStar_Bytes_bytes b2) {
  char *data = KRML_HOST_MALLOC(x);
  CHECK(data);
  for (size_t i = 0; i < x; ++i)
    data[i] = b1.data[i] ^ b2.data[i];
  FStar_Bytes_bytes b = { .length = x, .data = data };
  return b;
}

FStar_Bytes_bytes FStar_Bytes_bytes_of_int8(uint8_t x) {
  char *data = KRML_HOST_MALLOC(1);
  data[0] = x;
  return (FStar_Bytes_bytes){ .length = 1, .data = data };
}

FStar_Bytes_bytes FStar_Bytes_bytes_of_int16(uint16_t x) {
  char *data = KRML_HOST_MALLOC(2);
  data[0] = (x >> 8) & 0xFF;
  data[1] = x & 0xFF;
  return (FStar_Bytes_bytes){ .length = 2, .data = data };
}

FStar_Bytes_bytes FStar_Bytes_bytes_of_int32(uint32_t x) {
  char *data = KRML_HOST_MALLOC(4);
  data[0] = x >> 24;
  data[1] = (x >> 16) & 0xFF;
  data[2] = (x >> 8) & 0xFF;
  data[3] = x & 0xFF;
  return (FStar_Bytes_bytes){ .length = 4, .data = data };
}

uint8_t byte_of_hex(char c)
{
    if (c >= '0' && c <= '9') {
        return c-'0';
    } else if (c >= 'a' && c <= 'f') {
        return c-'a'+10;
    } else if (c >= 'A' && c <= 'F') {
        return c-'A'+10;
    } else {
        return 0xff;
    }
}

uint8_t hex_of_nibble(uint8_t n)
{
    n &= 0xf; // clear out any high bits
    if (n <= 9) {
        return (uint8_t)n + '0';
    } else {
        return (uint8_t)n + 'a' - 10;
    }
}

FStar_Bytes_bytes FStar_Bytes_bytes_of_hex(Prims_string str) {
  size_t l = strlen(str);
  if (l % 2 == 1)
    KRML_HOST_EPRINTF(
        "bytes_of_hex: input string has non-even length, truncating!\n");
  char *data = KRML_HOST_MALLOC(l / 2);
  CHECK(data);
  for (size_t i = 0; i < l / 2; i++) {
    uint8_t dst;
    uint8_t dst_hi = byte_of_hex(str[2 * i]);
    uint8_t dst_lo = byte_of_hex(str[2 * i + 1]);
    if (dst_hi == 0xff) {
      // sscanf() fails if the first digit cannot be parsed
      KRML_HOST_EPRINTF(
          "bytes_of_hex: run-time error while scanning at index "
          "%zu\n%s\n",
          2 * i, str);
      return FStar_Bytes_empty_bytes;
    } else if (dst_lo == 0xff) {
      // scanf succeeds if the first digit can be parsed, but not the second
      dst = dst_hi;
    } else {
      // both digits parsed
      dst = (dst_hi << 4) | dst_lo;
    }

    data[i] = dst;
  }
  FStar_Bytes_bytes b = { .length = l / 2, .data = data };
  return b;
}

Prims_string FStar_Bytes_print_bytes(FStar_Bytes_bytes s) {
  char *str = KRML_HOST_MALLOC(s.length * 2 + 1);
  CHECK(str);
  for (size_t i = 0; i < s.length; ++i) {
    str[2 * i] = hex_of_nibble(s.data[i] >> 4);
    str[2 * i + 1] = hex_of_nibble(s.data[i] & 0x0f);
  }
  str[s.length * 2] = 0;
  return str;
}

Prims_string FStar_Bytes_hex_of_bytes(FStar_Bytes_bytes s) {
  return FStar_Bytes_print_bytes(s);
}

// https://www.cl.cam.ac.uk/~mgk25/ucs/utf8_check.c
const unsigned char *utf8_check(const unsigned char *s) {
  while (*s) {
    if (*s < 0x80)
      /* 0xxxxxxx */
      s++;
    else if ((s[0] & 0xe0) == 0xc0) {
      /* 110XXXXx 10xxxxxx */
      if ((s[1] & 0xc0) != 0x80 || (s[0] & 0xfe) == 0xc0) /* overlong? */
        return s;
      else
        s += 2;
    } else if ((s[0] & 0xf0) == 0xe0) {
      /* 1110XXXX 10Xxxxxx 10xxxxxx */
      if ((s[1] & 0xc0) != 0x80 || (s[2] & 0xc0) != 0x80 ||
          (s[0] == 0xe0 && (s[1] & 0xe0) == 0x80) || /* overlong? */
          (s[0] == 0xed && (s[1] & 0xe0) == 0xa0) || /* surrogate? */
          (s[0] == 0xef && s[1] == 0xbf &&
           (s[2] & 0xfe) == 0xbe)) /* U+FFFE or U+FFFF? */
        return s;
      else
        s += 3;
    } else if ((s[0] & 0xf8) == 0xf0) {
      /* 11110XXX 10XXxxxx 10xxxxxx 10xxxxxx */
      if ((s[1] & 0xc0) != 0x80 || (s[2] & 0xc0) != 0x80 ||
          (s[3] & 0xc0) != 0x80 ||
          (s[0] == 0xf0 && (s[1] & 0xf0) == 0x80) ||    /* overlong? */
          (s[0] == 0xf4 && s[1] > 0x8f) || s[0] > 0xf4) /* > U+10FFFF? */
        return s;
      else
        s += 4;
    } else
      return s;
  }

  return NULL;
}

void
FStar_Bytes_iutf8_opt_(FStar_Bytes_bytes b, FStar_Pervasives_Native_option__Prims_string *ret) {
  char *str = KRML_HOST_MALLOC(b.length + 1);
  CHECK(str);
  if (b.length > 0)
    memcpy(str, b.data, b.length);
  str[b.length] = 0;

  unsigned const char *err = utf8_check((unsigned char *)str);
  if (err != NULL) {
    ret->tag = FStar_Pervasives_Native_None;
  } else {
    ret->tag = FStar_Pervasives_Native_Some;
    ret->v = str;
  }
}

#ifdef KRML_NOSTRUCT_PASSING
#define FStar_Bytes_iutf8_opt FStar_Bytes_iutf8_opt_
#else
FStar_Pervasives_Native_option__Prims_string
FStar_Bytes_iutf8_opt(FStar_Bytes_bytes b) {
  FStar_Pervasives_Native_option__Prims_string ret;
  FStar_Bytes_iutf8_opt_(b, &ret);
  return ret;
}
#endif

bool
__eq__FStar_Bytes_bytes(FStar_Bytes_bytes x0, FStar_Bytes_bytes x1) {
  if (x0.length != x1.length)
    return false;
  for (size_t i = 0; i < x0.length; ++i)
    if (x0.data[i] != x1.data[i])
      return false;
  return true;
}

FStar_Bytes_bytes FStar_Bytes_of_buffer(uint32_t length, uint8_t *src) {
  char *data = KRML_HOST_MALLOC(length);
  CHECK(data);
  if (length > 0)
    memcpy(data, src, length);
  FStar_Bytes_bytes b = { .length = length, .data = data };
  return b;
}

void FStar_Bytes_store_bytes(FStar_Bytes_bytes src, uint8_t *dst) {
  memcpy(dst, src.data, src.length);
}
