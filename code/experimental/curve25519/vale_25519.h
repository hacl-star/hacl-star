extern void mul(const uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);
extern void sqr(const uint64_t* dst, const uint64_t* in_a);
extern uint64_t mul1(const uint64_t* dst, const uint64_t* in_a, uint64_t b);
extern uint64_t add1(const uint64_t* dst, const uint64_t* in_a, uint64_t b);
extern uint64_t add(const uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);
extern uint64_t sub1(const uint64_t* dst, const uint64_t* in_a, uint64_t b);
extern uint64_t sub(const uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);

static inline
uint64_t mul1_add(const uint64_t* dst, const uint64_t* in_a, uint64_t x, const uint64_t* in_b) {
  uint64_t tmp[4] = {0};
  uint64_t s5 = mul1(tmp,in_a,x);
  uint64_t res = add(dst,tmp,in_b);
  return (s5 + res);
}

static inline
void fadd(uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b) {
  uint64_t carry = add(dst,in_a,in_b);
  carry = add1(dst,dst,carry * 38);
  dst[0] = dst[0] + (carry * 38);
}

static inline
void fsub(uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b) {
  uint64_t carry = sub(dst,in_a,in_b);
  carry = sub1(dst,dst,carry * 38);
  dst[0] = dst[0] - (carry * 38);
}

static inline
void carry_pass(uint64_t* dst, const uint64_t c_in) {
  uint64_t carry = add1(dst,dst,c_in * 38);
  dst[0] = dst[0] + (carry * 38);
}
static inline
void fmul(uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b) {
  uint64_t tmp[8] = {0};
  mul(tmp,in_a,in_b);
  uint64_t carry = mul1_add(dst,tmp+4,38,tmp);
  carry_pass(dst,carry);
}

static inline
void fmul1(uint64_t* dst, const uint64_t* in_a, const uint64_t in_b) {
  uint64_t carry = mul1(dst,in_a,in_b);
  carry_pass(dst,carry);
}

static inline
void fsqr(uint64_t* dst, const uint64_t* in_a) {
  uint64_t tmp[8] = {0};
  sqr(tmp,in_a);
  uint64_t carry = mul1_add(dst,tmp+4,38,tmp);
  carry_pass(dst,carry);
}

static inline
void mul2(const uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b) {
  mul(dst,in_a,in_b);
  mul(dst+8,in_a+4,in_b+4);
}

static inline
void carry_pass2(uint64_t* dst, uint64_t c1, uint64_t c2) {
  uint64_t carry1 = add1(dst,dst,c1 * 38);
  uint64_t carry2 = add1(dst+4,dst+4,c2 * 38);
  dst[0] = dst[0] + (carry1 * 38);
  dst[0] = dst[0] + (carry2 * 38);
}


static inline
void fmul2(uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b) {
  uint64_t tmp[16] = {0};
  mul2(tmp,in_a,in_b);
  uint64_t carry1 = mul1_add(dst,tmp+4,38,tmp);
  uint64_t carry2 = mul1_add(dst+4,tmp+12,38,tmp+8);
  carry_pass2(dst,carry1,carry2);
}

static inline
void sqr2(const uint64_t* dst, const uint64_t* in_a) {
  sqr(dst,in_a);
  sqr(dst+8,in_a+4);
}

static inline
void fsqr2(uint64_t* dst, const uint64_t* in_a) {
  uint64_t tmp[16] = {0};
  sqr2(tmp,in_a);
  uint64_t carry1 = mul1_add(dst,tmp+4,38,tmp);
  uint64_t carry2 = mul1_add(dst+4,tmp+12,38,tmp+8);
  carry_pass2(dst,carry1,carry2);
}




