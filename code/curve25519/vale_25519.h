/////////////////////////////////////////////////////////////////
// These are now all internal to the public functions below
/////////////////////////////////////////////////////////////////

//extern void mul(const uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);
//extern void sqr(const uint64_t* dst, const uint64_t* in_a);
//extern uint64_t mul1(const uint64_t* dst, const uint64_t* in_a, uint64_t b);
//extern uint64_t add(const uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);
//extern uint64_t sub1(const uint64_t* dst, const uint64_t* in_a, uint64_t b);
//extern uint64_t sub(const uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);
//extern void mul2(const uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);
//extern void sqr2(const uint64_t* dst, const uint64_t* in_a);
//extern void carry_wide(uint64_t* dst, uint64_t* tmp);

/////////////////////////////////////////////////////////////////
// Exported from Vale
/////////////////////////////////////////////////////////////////

extern uint64_t add1(const uint64_t* dst, const uint64_t* in_a, uint64_t b);

extern void fadd(uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);
extern void fsub(uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);
extern void fmul1(uint64_t* dst, const uint64_t* in_a, const uint64_t in_b);

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

/////////////////////////////////////////////////////////////////
// Wrappers to align arguments
/////////////////////////////////////////////////////////////////


#define force_inline inline __attribute((always_inline))

// Done in C in rfc7748_25519.h
static force_inline
void fmul(uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b, uint64_t* tmp) {
  fmul_v(tmp, in_a, dst, in_b);
}

// Done in C in rfc7748_25519.h
static force_inline
void fsqr(uint64_t* dst, const uint64_t* in_a, uint64_t* tmp) {
  fsqr_v(tmp,in_a, dst);
}

// Done in C in rfc7748_25519.h
static force_inline
void fmul2(uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b, uint64_t* tmp) {
  fmul2_v(tmp, in_a, dst, in_b);
}

// Done in C in rfc7748_25519.h
static force_inline
void fsqr2(uint64_t* dst, const uint64_t* in_a, uint64_t* tmp) {
  fsqr2_v(tmp, in_a, dst);
}


extern void cswap2_v(uint64_t *const p0, uint64_t *const p1, uint8_t bit);
static inline void cswap2(uint8_t bit, uint64_t *const p0, uint64_t *const p1) {
  cswap2_v(p0, p1, bit);
}

static force_inline void cselect1(uint8_t bit, uint64_t *const px,
                           uint64_t *const py) {
  __asm__ __volatile__(
    "test %4, %4 ;"
    "cmovnzq %5, %0 ;"
    "cmovnzq %6, %1 ;"
    "cmovnzq %7, %2 ;"
    "cmovnzq %8, %3 ;"
    : "+r"(px[0]), "+r"(px[1]), "+r"(px[2]), "+r"(px[3])
    : "r"(bit), "rm"(py[0]), "rm"(py[1]), "rm"(py[2]), "rm"(py[3])
    : "cc"
  );
}



static force_inline void cselect2(uint8_t bit, uint64_t *const p0, uint64_t *const p1) {
  cswap1(bit,p0,p1);
  cswap1(bit,p0+4,p1+4);
}


