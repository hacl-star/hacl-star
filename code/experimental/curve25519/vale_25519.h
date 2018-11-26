extern void mul(const uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);
extern void sqr(const uint64_t* dst, const uint64_t* in_a);
extern uint64_t mul1(const uint64_t* dst, const uint64_t* in_a, uint64_t b);
extern uint64_t add1(const uint64_t* dst, const uint64_t* in_a, uint64_t b);
extern uint64_t add(const uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);
extern uint64_t sub1(const uint64_t* dst, const uint64_t* in_a, uint64_t b);
extern uint64_t sub(const uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b);

static inline
uint64_t mul1_add(const uint64_t* dst, const uint64_t* in_a, uint64_t x, const uint64_t* in_b) {
  uint64_t carry = 0;
  __asm__ __volatile__(
    "movq     %3, %%rdx ;" /* 2*c = 38 = 2^256 */
    "mulx   (%2),  %%r8, %%r10 ;" /* c*C[4] */  "xorl %%ebx, %%ebx ;"  "adox   (%4),  %%r8 ;"
    "mulx  8(%2),  %%r9, %%r11 ;" /* c*C[5] */  "adcx %%r10,  %%r9 ;"  "adox  8(%4),  %%r9 ;"
    "mulx 16(%2), %%r10, %%rax ;" /* c*C[6] */  "adcx %%r11, %%r10 ;"  "adox 16(%4), %%r10 ;"
    "mulx 24(%2), %%r11, %%rcx ;" /* c*C[7] */  "adcx %%rax, %%r11 ;"  "adox 24(%4), %%r11 ;"
    /****************************************/  "adcx %%rbx, %%rcx ;"  "adox  %%rbx, %%rcx ;"
    "movq  %%r8,   (%1) ;"
    "movq  %%r9,  8(%1) ;"
    "movq %%r10, 16(%1) ;"
    "movq %%r11, 24(%1) ;"
    "movq %%rcx, %0 ;"
  : "=r" (carry)
  : "r" (dst), "r" (in_a), "r" (x), "r" (in_b)
  : "memory", "cc", "%rax", "%rbx", "%rcx", "%rdx", "%r8", "%r9", "%r10", "%r11"
  );
  return carry;
}

/*
static inline
uint64_t mul1_add(const uint64_t* dst, const uint64_t* in_a, uint64_t x, const uint64_t* in_b) {
  uint64_t tmp[4] = {0};
  uint64_t s5 = mul1(tmp,in_a,x);
  uint64_t res = add(dst,tmp,in_b);
  return (s5 + res);
}
*/

static inline
void carry_pass(uint64_t* dst, const uint64_t c_in) {
  uint64_t carry = add1(dst,dst,c_in * 38);
  dst[0] = dst[0] + (carry * 38);
}

static inline
void carry_wide(uint64_t* dst, uint64_t* tmp) {
  uint64_t carry = mul1_add(dst,tmp+4,38,tmp);
  carry_pass(dst,carry);
}

static inline
void fadd(uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b) {
  uint64_t carry = add(dst,in_a,in_b);
  carry_pass(dst,carry);
}

static inline
void fsub(uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b) {
  uint64_t carry = sub(dst,in_a,in_b);
  carry = sub1(dst,dst,carry * 38);
  dst[0] = dst[0] - (carry * 38);
}

static inline
void fmul(uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b) {
  uint64_t tmp[8] = {0};
  mul(tmp,in_a,in_b);
  carry_wide(dst,tmp);
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
  carry_wide(dst,tmp);
}

static inline
void mul2(const uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b) {
  mul(dst,in_a,in_b);
  mul(dst+8,in_a+4,in_b+4);
}

static inline
void fmul2(uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b) {
  uint64_t tmp[16] = {0};
  mul2(tmp,in_a,in_b);
  carry_wide(dst,tmp);
  carry_wide(dst+4,tmp+8);
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
  carry_wide(dst,tmp);
  carry_wide(dst+4,tmp+8);
}




