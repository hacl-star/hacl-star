extern void mul(const uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);
extern void sqr(const uint64_t* dst, const uint64_t* in_a);
extern uint64_t mul1(const uint64_t* dst, const uint64_t* in_a, uint64_t b);
extern uint64_t add1(const uint64_t* dst, const uint64_t* in_a, uint64_t b);
extern uint64_t add(const uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);
extern uint64_t sub1(const uint64_t* dst, const uint64_t* in_a, uint64_t b);
extern uint64_t sub(const uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);
extern void mul2(const uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);
extern void sqr2(const uint64_t* dst, const uint64_t* in_a);

extern void fmul_v(const uint64_t* tmp, const uint64_t* in_a, const uint64_t* dst, const uint64_t* in_b);
extern void fmul2_v(const uint64_t* tmp, const uint64_t* in_a, const uint64_t* dst, const uint64_t* in_b);
extern void fsqr_v(const uint64_t* tmp, const uint64_t* in_a, const uint64_t* dst);
extern void fsqr2_v(const uint64_t* tmp, const uint64_t* in_a, const uint64_t* dst);

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
  fmul_v(tmp, in_a, dst, in_b);
}

// Done in C in rfc7748_25519.h
static inline
void fsqr(uint64_t* dst, const uint64_t* in_a) {
  uint64_t tmp[8] = {0};
  fsqr_v(tmp,in_a, dst);
}

// Done in C in rfc7748_25519.h
static inline
void fmul2(uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b) {
  uint64_t tmp[16] = {0};
  fmul2_v(tmp, in_a, dst, in_b);
}

// Done in C in rfc7748_25519.h
static inline
void fsqr2(uint64_t* dst, const uint64_t* in_a) {
  uint64_t tmp[16] = {0};
  fsqr2_v(tmp, in_a, dst);
}




