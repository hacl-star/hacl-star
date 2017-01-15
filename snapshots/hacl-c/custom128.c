/* From OPENSSL's code base */
#define CONSTANT_TIME_CARRY(a, b)                                              \
  ((a ^ ((a ^ b) | ((a - b) ^ b))) >> (sizeof(a) * 8 - 1))

FStar_UInt128_t FStar_UInt128_add(FStar_UInt128_t x, FStar_UInt128_t y) {
  FStar_UInt128_t r;
  r.low = x.low + y.low;
  r.high = x.high + y.high + CONSTANT_TIME_CARRY(r.low, y.low);
  return r;
}

FStar_UInt128_t FStar_UInt128_add_mod(FStar_UInt128_t x, FStar_UInt128_t y) {
  return FStar_UInt128_add(x, y);
}

FStar_UInt128_t FStar_UInt128_sub(FStar_UInt128_t x, FStar_UInt128_t y) {
  FStar_UInt128_t r;
  r.low = x.low - y.low;
  r.high = x.high - y.high - CONSTANT_TIME_CARRY(x.low, r.low);
  return r;
}

FStar_UInt128_t FStar_UInt128_sub_mod(FStar_UInt128_t x, FStar_UInt128_t y) {
  return FStar_UInt128_sub(x, y);
}

FStar_UInt128_t FStar_UInt128_logand(FStar_UInt128_t x, FStar_UInt128_t y) {
  FStar_UInt128_t r;
  r.high = x.high & y.high;
  r.low = x.low & y.low;
  return r;
}

FStar_UInt128_t FStar_UInt128_logor(FStar_UInt128_t x, FStar_UInt128_t y) {
  FStar_UInt128_t r;
  r.high = x.high | y.high;
  r.low = x.low | y.low;
  return r;
}

FStar_UInt128_t FStar_UInt128_logxor(FStar_UInt128_t x, FStar_UInt128_t y) {
  FStar_UInt128_t r;
  r.high = x.high ^ y.high;
  r.low = x.low ^ y.low;
  return r;
}

FStar_UInt128_t FStar_UInt128_lognot(FStar_UInt128_t x) {
  FStar_UInt128_t r;
  r.high = ~x.high;
  r.low = ~x.low;
  return r;
}

/* y >= 128 should never happen */
FStar_UInt128_t FStar_UInt128_shift_left(FStar_UInt128_t x, FStar_UInt32_t y) {
  FStar_UInt128_t r;
  uint64_t mask_64_m = (((int64_t)y - 64) >> 63);
  uint64_t mask_64_p = ((64 - (int64_t)y) >> 63);
  uint64_t mask_64 = ~(mask_64_m | mask_64_p);
  uint64_t mask_0 = ((int64_t)y - 1) >> 63;
  r.low = mask_64_m & (x.low << y);
  r.high = (mask_64_m & ((x.high << y) | ((~mask_0) & (x.low >> (64 - y))))) |
           ((mask_64_p) & (x.low << (y - 64))) | (mask_64 & x.low);
  return r;
}

FStar_UInt128_t FStar_UInt128_shift_right(FStar_UInt128_t x, FStar_UInt32_t y) {
  FStar_UInt128_t r;
  uint64_t mask_64_m = (((int64_t)y - 64) >> 63);
  uint64_t mask_64_p = ((64 - (int64_t)y) >> 63);
  uint64_t mask_64 = ~(mask_64_m | mask_64_p);
  uint64_t mask_0 = ((int64_t)y - 1) >> 63;
  r.high = mask_64_m & (x.high >> y);
  r.low = (mask_64_m & ((x.low >> y) | ((~mask_0) & (x.high << (64 - y))))) |
          ((mask_64_p) & (x.high >> (y - 64))) | (mask_64 & x.high);
  return r;
}

/* Conversions */
FStar_UInt128_t FStar_Int_Cast_uint64_to_uint128(uint64_t x) {
  return (FStar_UInt128_t){.high = UINT64_C(0), .low = x};
}

uint64_t FStar_Int_Cast_uint128_to_uint64(FStar_UInt128_t x) { return x.low; }

FStar_UInt128_t FStar_UInt128_eq_mask(FStar_UInt128_t x, FStar_UInt128_t y) {
  return (FStar_UInt128_t){.low = FStar_UInt64_eq_mask(x.low, y.low),
                           .high = FStar_UInt64_eq_mask(x.high, y.high)};
}

FStar_UInt128_t FStar_UInt128_gte_mask(FStar_UInt128_t x, FStar_UInt128_t y) {
  uint64_t mask = (FStar_UInt64_gte_mask(x.high, y.high) &
                   ~(FStar_UInt64_eq_mask(x.high, y.high))) |
                  (FStar_UInt64_eq_mask(x.high, y.high) &
                   FStar_UInt64_gte_mask(x.low, y.low));
  return (FStar_UInt128_t){.high = mask, .low = mask};
}

FStar_UInt128_t FStar_UInt128_mul_wide(uint64_t x, uint64_t y) {
  uint64_t u1, v1, t, w3, k, w1;
  u1 = (x & 0xffffffff);
  v1 = (y & 0xffffffff);
  t = (u1 * v1);
  w3 = (t & 0xffffffff);
  k = (t >> 32);
  x >>= 32;
  t = (x * v1) + k;
  k = (t & 0xffffffff);
  w1 = (t >> 32);
  y >>= 32;
  t = (u1 * y) + k;
  k = (t >> 32);
  return (FStar_UInt128_t){.high = (x * y) + w1 + k, .low = (t << 32) + w3};
}

bool FStar_UInt128_op_Greater_Greater_Hat(FStar_UInt128_t x, FStar_UInt32_t y) {
  exit(254);
}
