
FStar_UInt128_t FStar_UInt128_eq_mask(FStar_UInt128_t x, FStar_UInt128_t y) {
  uint64_t mask =
      FStar_UInt64_eq_mask((uint64_t)(x >> 64), (uint64_t)(y >> 64)) &
      FStar_UInt64_eq_mask(x, y);
  return ((FStar_UInt128_t)mask) << 64 | mask;
}

FStar_UInt128_t FStar_UInt128_gte_mask(FStar_UInt128_t x, FStar_UInt128_t y) {
  uint64_t mask =
      (FStar_UInt64_gte_mask(x >> 64, y >> 64) &
       ~(FStar_UInt64_eq_mask(x >> 64, y >> 64))) |
      (FStar_UInt64_eq_mask(x >> 64, y >> 64) & FStar_UInt64_gte_mask(x, y));
  return ((FStar_UInt128_t)mask) << 64 | mask;
}
