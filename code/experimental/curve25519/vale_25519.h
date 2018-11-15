extern void mul(const uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);
extern void sqr(const uint64_t* dst, const uint64_t* in_a);
extern uint64_t mul1(const uint64_t* dst, const uint64_t* in_a, uint64_t b);
extern uint64_t add1(const uint64_t* dst, const uint64_t* in_a, uint64_t b);
extern uint64_t add(const uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);
extern uint64_t sub1(const uint64_t* dst, const uint64_t* in_a, uint64_t b);
extern uint64_t sub(const uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);

static inline
uint64_t mul1_add(const uint64_t* dst, const uint64_t* in_a, uint64_t b) {
  uint64_t tmp[4] = {0};
  uint64_t s5 = mul1(tmp,in_a,b);
  uint64_t res = add(dst,dst,tmp);
  return (s5 + res);
}

static inline
uint64_t mul2(const uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b) {
  mul(dst,in_a,in_b);
  mul(dst+8,in_a+4,in_b+4);
}


static inline
uint64_t sqr2(const uint64_t* dst, const uint64_t* in_a) {
  sqr(dst,in_a);
  sqr(dst+8,in_a+4);
}
