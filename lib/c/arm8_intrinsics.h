
static inline uint64_t
uint128_t_add_carry_u64(uint64_t cin, uint64_t x, uint64_t y, uint64_t* r) {
  __uint128_t res = (__uint128_t)x + cin + y;
  r[0U] = (uint64_t)res;
  uint64_t c = res >> 64;
  return c;
}

static inline uint64_t
uint128_t_sub_borrow_u64(uint64_t cin, uint64_t x, uint64_t y, uint64_t* r) {
  __uint128_t res = (__uint128_t)x - cin - y;
  r[0U] = (uint64_t)res;
  uint64_t c = (res >> 64) & 1U;
  return c;
}
