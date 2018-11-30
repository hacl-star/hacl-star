extern void mul(const uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);
extern void sqr(const uint64_t* dst, const uint64_t* in_a);
extern uint64_t mul1(const uint64_t* dst, const uint64_t* in_a, uint64_t b);
extern uint64_t add1(const uint64_t* dst, const uint64_t* in_a, uint64_t b);
extern uint64_t add(const uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);
extern uint64_t sub1(const uint64_t* dst, const uint64_t* in_a, uint64_t b);
extern uint64_t sub(const uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);
extern void mul2(const uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);
extern void sqr2(const uint64_t* dst, const uint64_t* in_a);

/*
extern uint64_t mul1_add(const uint64_t* dst, const uint64_t* in_a, uint64_t x, const uint64_t* in_b);

static inline
void carry_pass(uint64_t* dst, const uint64_t c_in) {
  uint64_t carry = add1(dst,dst,c_in * 38);
  dst[0] = dst[0] + (carry * 38);
}
*/

extern void carry_wide(uint64_t* dst, uint64_t* tmp);

extern void fadd(uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);
extern void fsub(uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);
extern void fmul1(uint64_t* dst, const uint64_t* in_a, const uint64_t in_b);

// Done in C in rfc7748_25519.h
static inline
void fmul(uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b) {
  uint64_t tmp[8] = {0};
  mul(tmp,in_a,in_b);
  carry_wide(dst,tmp);
}

// Done in C in rfc7748_25519.h
static inline
void fsqr(uint64_t* dst, const uint64_t* in_a) {
  uint64_t tmp[8] = {0};
  sqr(tmp,in_a);
  carry_wide(dst,tmp);
}

// Done in C in rfc7748_25519.h
static inline
void fmul2(uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b) {
  uint64_t tmp[16] = {0};
  mul2(tmp,in_a,in_b);
  carry_wide(dst,tmp);
  carry_wide(dst+4,tmp+8);
}

// Done in C in rfc7748_25519.h
static inline
void fsqr2(uint64_t* dst, const uint64_t* in_a) {
  uint64_t tmp[16] = {0};
  sqr2(tmp,in_a);
  carry_wide(dst,tmp);
  carry_wide(dst+4,tmp+8);
}




