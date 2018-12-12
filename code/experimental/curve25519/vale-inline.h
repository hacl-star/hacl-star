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

#define inline inline __attribute((always_inline))

/////////////////////////////////////////////////////////////////
// Exported from Vale
/////////////////////////////////////////////////////////////////

static inline uint64_t add1(const uint64_t* dst, const uint64_t* in_a, uint64_t b) {
  register uint64_t* dst_r asm("rdi") = dst;
  register uint64_t* in_a_r asm("rsi") = in_a;
  register uint64_t* b_r asm("rcx") = b;
  register uint64_t* carry_r asm("rax");

  __asm__ __volatile__(
    "  xor %%r8, %%r8;"
    "  xor %%r9, %%r9;"
    "  xor %%r10, %%r10;"
    "  xor %%r11, %%r11;"
    "  xor %%rax, %%rax;"
    "  addq 0(%%rsi), %%rcx;"
    "  movq %%rcx, 0(%%rdi);"
    "  adcxq 8(%%rsi), %%r8;"
    "  movq %%r8, 8(%%rdi);"
    "  adcxq 16(%%rsi), %%r9;"
    "  movq %%r9, 16(%%rdi);"
    "  adcxq 24(%%rsi), %%r10;"
    "  movq %%r10, 24(%%rdi);"
    "  adcx %%r11, %%rax;"
  : "=r" (carry_r), "+r" (b_r)
  : "r" (dst_r), "r" (in_a_r)
  : "memory", "cc", "%r8", "%r9", "%r10", "%r11"
  );
}


extern void fadd(uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b) {
  register uint64_t* dst_r asm("rdi") = dst;
  register uint64_t* in_a_r asm("rsi") = in_a;
  register uint64_t* in_b_r asm("rdx") = in_b;

  __asm__ __volatile__(
    "  movq 0(%%rdx), %%r8;"
    "  addq 0(%%rsi), %%r8;"
    "  movq 8(%%rdx), %%r9;"
    "  adcxq 8(%%rsi), %%r9;"
    "  movq 16(%%rdx), %%r10;"
    "  adcxq 16(%%rsi), %%r10;"
    "  movq 24(%%rdx), %%r11;"
    "  adcxq 24(%%rsi), %%r11;"
    "  mov $0, %%rax;"
    "  mov $38, %%rdx;"
    "  cmovc %%rdx, %%rax;"
    "  xor %%rcx, %%rcx;"
    "  add %%rax, %%r8;"
    "  adcx %%rcx, %%r9;"
    "  movq %%r9, 8(%%rdi);"
    "  adcx %%rcx, %%r10;"
    "  movq %%r10, 16(%%rdi);"
    "  adcx %%rcx, %%r11;"
    "  movq %%r11, 24(%%rdi);"
    "  mov $0, %%rax;"
    "  cmovc %%rdx, %%rax;"
    "  add %%rax, %%r8;"
    "  movq %%r8, 0(%%rdi);"
  : "+r" (in_b_r)
  : "r" (dst_r), "r" (in_a_r)
  : "memory", "cc", "%rax", "%rcx", "%r8", "%r9", "%r10", "%r11"
  );
}
extern void fsub(uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b) {
  register uint64_t* dst_r asm("rdi") = dst;
  register uint64_t* in_a_r asm("rsi") = in_a;
  register uint64_t* in_b_r asm("rdx") = in_b;

  __asm__ __volatile__(
    "  movq 0(%%rsi), %%r8;"
    "  subq 0(%%rdx), %%r8;"
    "  movq 8(%%rsi), %%r9;"
    "  sbbq 8(%%rdx), %%r9;"
    "  movq 16(%%rsi), %%r10;"
    "  sbbq 16(%%rdx), %%r10;"
    "  movq 24(%%rsi), %%r11;"
    "  sbbq 24(%%rdx), %%r11;"
    "  mov $0, %%rax;"
    "  mov $38, %%rcx;"
    "  cmovc %%rcx, %%rax;"
    "  sub %%rax, %%r8;"
    "  sbb $0, %%r9;"
    "  sbb $0, %%r10;"
    "  sbb $0, %%r11;"
    "  mov $0, %%rax;"
    "  cmovc %%rcx, %%rax;"
    "  sub %%rax, %%r8;"
    "  movq %%r8, 0(%%rdi);"
    "  movq %%r9, 8(%%rdi);"
    "  movq %%r10, 16(%%rdi);"
    "  movq %%r11, 24(%%rdi);"
  :
  : "r" (dst_r), "r" (in_a_r), "r" (in_b_r)
  : "memory", "cc", "%rax", "%rcx", "%r8", "%r9", "%r10", "%r11"
  );

}
extern void fmul1(uint64_t* dst, const uint64_t* in_a, const uint64_t in_b) {
  register uint64_t* dst_r asm("rdi") = dst;
  register uint64_t* in_a_r asm("rsi") = in_a;
  register uint64_t in_b_r asm("rdx") = in_b;

  __asm__ __volatile__(
    "  mulxq 0(%%rsi), %%r8, %%rcx;"
    "  mulxq 8(%%rsi), %%r9, %%r12;"
    "  add %%rcx, %%r9;"
    "  mov $0, %%rcx;"
    "  mulxq 16(%%rsi), %%r10, %%r13;"
    "  adcx %%r12, %%r10;"
    "  mulxq 24(%%rsi), %%r11, %%rax;"
    "  adcx %%r13, %%r11;"
    "  adcx %%rcx, %%rax;"
    "  mov $38, %%rdx;"
    "  imul %%rdx, %%rax;"
    "  add %%rax, %%r8;"
    "  adcx %%rcx, %%r9;"
    "  movq %%r9, 8(%%rdi);"
    "  adcx %%rcx, %%r10;"
    "  movq %%r10, 16(%%rdi);"
    "  adcx %%rcx, %%r11;"
    "  movq %%r11, 24(%%rdi);"
    "  mov $0, %%rax;"
    "  cmovc %%rdx, %%rax;"
    "  add %%rax, %%r8;"
    "  movq %%r8, 0(%%rdi);"
  : "+r" (in_b_r)
  : "r" (dst_r), "r" (in_a_r)
  : "memory", "cc", "%rax", "%rcx", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13"
  );

}

extern void fmul_v(const uint64_t* tmp, const uint64_t* in_a, const uint64_t* dst, const uint64_t* in_b) {
  register uint64_t* tmp_r asm("rdi") = tmp;
  register uint64_t* in_a_r asm("rsi") = in_a;
  register uint64_t* dst_r asm("rdx") = dst;
  register uint64_t* in_b_r asm("rcx") = in_b;

  __asm__ __volatile__(
    "   push %%rdx;"
    "  movq 0(%%rsi), %%rdx;"
    "  mulxq 0(%%rcx), %%r8, %%r9;"
    "  xor %%r10, %%r10;"
    "  movq %%r8, 0(%%rdi);"
    "  mulxq 8(%%rcx), %%r10, %%r11;"
    "  adox %%r9, %%r10;"
    "  movq %%r10, 8(%%rdi);"
    "  mulxq 16(%%rcx), %%r12, %%r13;"
    "  adox %%r11, %%r12;"
    "  mulxq 24(%%rcx), %%r14, %%rdx;"
    "  adox %%r13, %%r14;"
    "  mov $0, %%rax;"
    "  adox %%rdx, %%rax;"
    "  movq 8(%%rsi), %%rdx;"
    "  mulxq 0(%%rcx), %%r8, %%r9;"
    "  xor %%r10, %%r10;"
    "  adcxq 8(%%rdi), %%r8;"
    "  movq %%r8, 8(%%rdi);"
    "  mulxq 8(%%rcx), %%r10, %%r11;"
    "  adox %%r9, %%r10;"
    "  adcx %%r12, %%r10;"
    "  movq %%r10, 16(%%rdi);"
    "  mulxq 16(%%rcx), %%r12, %%r13;"
    "  adox %%r11, %%r12;"
    "  adcx %%r14, %%r12;"
    "  mov $0, %%r8;"
    "  mulxq 24(%%rcx), %%r14, %%rdx;"
    "  adox %%r13, %%r14;"
    "  adcx %%rax, %%r14;"
    "  mov $0, %%rax;"
    "  adox %%rdx, %%rax;"
    "  adcx %%r8, %%rax;"
    "  movq 16(%%rsi), %%rdx;"
    "  mulxq 0(%%rcx), %%r8, %%r9;"
    "  xor %%r10, %%r10;"
    "  adcxq 16(%%rdi), %%r8;"
    "  movq %%r8, 16(%%rdi);"
    "  mulxq 8(%%rcx), %%r10, %%r11;"
    "  adox %%r9, %%r10;"
    "  adcx %%r12, %%r10;"
    "  movq %%r10, 24(%%rdi);"
    "  mulxq 16(%%rcx), %%r12, %%r13;"
    "  adox %%r11, %%r12;"
    "  adcx %%r14, %%r12;"
    "  mov $0, %%r8;"
    "  mulxq 24(%%rcx), %%r14, %%rdx;"
    "  adox %%r13, %%r14;"
    "  adcx %%rax, %%r14;"
    "  mov $0, %%rax;"
    "  adox %%rdx, %%rax;"
    "  adcx %%r8, %%rax;"
    "  movq 24(%%rsi), %%rdx;"
    "  mulxq 0(%%rcx), %%r8, %%r9;"
    "  xor %%r10, %%r10;"
    "  adcxq 24(%%rdi), %%r8;"
    "  movq %%r8, 24(%%rdi);"
    "  mulxq 8(%%rcx), %%r10, %%r11;"
    "  adox %%r9, %%r10;"
    "  adcx %%r12, %%r10;"
    "  movq %%r10, 32(%%rdi);"
    "  mulxq 16(%%rcx), %%r12, %%r13;"
    "  adox %%r11, %%r12;"
    "  adcx %%r14, %%r12;"
    "  movq %%r12, 40(%%rdi);"
    "  mov $0, %%r8;"
    "  mulxq 24(%%rcx), %%r14, %%rdx;"
    "  adox %%r13, %%r14;"
    "  adcx %%rax, %%r14;"
    "  movq %%r14, 48(%%rdi);"
    "  mov $0, %%rax;"
    "  adox %%rdx, %%rax;"
    "  adcx %%r8, %%rax;"
    "  movq %%rax, 56(%%rdi);"
    "  mov %%rdi, %%rsi;"
    "  pop %%rdi;"
    "  mov $38, %%rdx;"
    "  mulxq 32(%%rsi), %%r8, %%r13;"
    "  xor %%rcx, %%rcx;"
    "  adoxq 0(%%rsi), %%r8;"
    "  mulxq 40(%%rsi), %%r9, %%r12;"
    "  adcx %%r13, %%r9;"
    "  adoxq 8(%%rsi), %%r9;"
    "  mulxq 48(%%rsi), %%r10, %%r13;"
    "  adcx %%r12, %%r10;"
    "  adoxq 16(%%rsi), %%r10;"
    "  mulxq 56(%%rsi), %%r11, %%rax;"
    "  adcx %%r13, %%r11;"
    "  adoxq 24(%%rsi), %%r11;"
    "  adcx %%rcx, %%rax;"
    "  adox %%rcx, %%rax;"
    "  imul %%rdx, %%rax;"
    "  add %%rax, %%r8;"
    "  adcx %%rcx, %%r9;"
    "  movq %%r9, 8(%%rdi);"
    "  adcx %%rcx, %%r10;"
    "  movq %%r10, 16(%%rdi);"
    "  adcx %%rcx, %%r11;"
    "  movq %%r11, 24(%%rdi);"
    "  mov $0, %%rax;"
    "  cmovc %%rdx, %%rax;"
    "  add %%rax, %%r8;"
    "  movq %%r8, 0(%%rdi);"
  : "+r" (tmp_r), "+r" (dst_r), "+r" (in_a_r), "+r" (in_b_r)
  : 
  : "memory", "cc", "%rax", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14"
  );

}
extern void fmul2_v(const uint64_t* tmp, const uint64_t* in_a, const uint64_t* dst, const uint64_t* in_b) {
  register uint64_t* tmp_r asm("rdi") = tmp;
  register uint64_t* in_a_r asm("rsi") = in_a;
  register uint64_t* dst_r asm("rdx") = dst;
  register uint64_t* in_b_r asm("rcx") = in_b;

  __asm__ __volatile__(
    "  push %%rdx;"
    "  movq 0(%%rsi), %%rdx;"
    "  mulxq 0(%%rcx), %%r8, %%r9;"
    "  xor %%r10, %%r10;"
    "  movq %%r8, 0(%%rdi);"
    "  mulxq 8(%%rcx), %%r10, %%r11;"
    "  adox %%r9, %%r10;"
    "  movq %%r10, 8(%%rdi);"
    "  mulxq 16(%%rcx), %%r12, %%r13;"
    "  adox %%r11, %%r12;"
    "  mulxq 24(%%rcx), %%r14, %%rdx;"
    "  adox %%r13, %%r14;"
    "  mov $0, %%rax;"
    "  adox %%rdx, %%rax;"
    "  movq 8(%%rsi), %%rdx;"
    "  mulxq 0(%%rcx), %%r8, %%r9;"
    "  xor %%r10, %%r10;"
    "  adcxq 8(%%rdi), %%r8;"
    "  movq %%r8, 8(%%rdi);"
    "  mulxq 8(%%rcx), %%r10, %%r11;"
    "  adox %%r9, %%r10;"
    "  adcx %%r12, %%r10;"
    "  movq %%r10, 16(%%rdi);"
    "  mulxq 16(%%rcx), %%r12, %%r13;"
    "  adox %%r11, %%r12;"
    "  adcx %%r14, %%r12;"
    "  mov $0, %%r8;"
    "  mulxq 24(%%rcx), %%r14, %%rdx;"
    "  adox %%r13, %%r14;"
    "  adcx %%rax, %%r14;"
    "  mov $0, %%rax;"
    "  adox %%rdx, %%rax;"
    "  adcx %%r8, %%rax;"
    "  movq 16(%%rsi), %%rdx;"
    "  mulxq 0(%%rcx), %%r8, %%r9;"
    "  xor %%r10, %%r10;"
    "  adcxq 16(%%rdi), %%r8;"
    "  movq %%r8, 16(%%rdi);"
    "  mulxq 8(%%rcx), %%r10, %%r11;"
    "  adox %%r9, %%r10;"
    "  adcx %%r12, %%r10;"
    "  movq %%r10, 24(%%rdi);"
    "  mulxq 16(%%rcx), %%r12, %%r13;"
    "  adox %%r11, %%r12;"
    "  adcx %%r14, %%r12;"
    "  mov $0, %%r8;"
    "  mulxq 24(%%rcx), %%r14, %%rdx;"
    "  adox %%r13, %%r14;"
    "  adcx %%rax, %%r14;"
    "  mov $0, %%rax;"
    "  adox %%rdx, %%rax;"
    "  adcx %%r8, %%rax;"
    "  movq 24(%%rsi), %%rdx;"
    "  mulxq 0(%%rcx), %%r8, %%r9;"
    "  xor %%r10, %%r10;"
    "  adcxq 24(%%rdi), %%r8;"
    "  movq %%r8, 24(%%rdi);"
    "  mulxq 8(%%rcx), %%r10, %%r11;"
    "  adox %%r9, %%r10;"
    "  adcx %%r12, %%r10;"
    "  movq %%r10, 32(%%rdi);"
    "  mulxq 16(%%rcx), %%r12, %%r13;"
    "  adox %%r11, %%r12;"
    "  adcx %%r14, %%r12;"
    "  movq %%r12, 40(%%rdi);"
    "  mov $0, %%r8;"
    "  mulxq 24(%%rcx), %%r14, %%rdx;"
    "  adox %%r13, %%r14;"
    "  adcx %%rax, %%r14;"
    "  movq %%r14, 48(%%rdi);"
    "  mov $0, %%rax;"
    "  adox %%rdx, %%rax;"
    "  adcx %%r8, %%rax;"
    "  movq %%rax, 56(%%rdi);"
    "  movq 32(%%rsi), %%rdx;"
    "  mulxq 32(%%rcx), %%r8, %%r9;"
    "  xor %%r10, %%r10;"
    "  movq %%r8, 64(%%rdi);"
    "  mulxq 40(%%rcx), %%r10, %%r11;"
    "  adox %%r9, %%r10;"
    "  movq %%r10, 72(%%rdi);"
    "  mulxq 48(%%rcx), %%r12, %%r13;"
    "  adox %%r11, %%r12;"
    "  mulxq 56(%%rcx), %%r14, %%rdx;"
    "  adox %%r13, %%r14;"
    "  mov $0, %%rax;"
    "  adox %%rdx, %%rax;"
    "  movq 40(%%rsi), %%rdx;"
    "  mulxq 32(%%rcx), %%r8, %%r9;"
    "  xor %%r10, %%r10;"
    "  adcxq 72(%%rdi), %%r8;"
    "  movq %%r8, 72(%%rdi);"
    "  mulxq 40(%%rcx), %%r10, %%r11;"
    "  adox %%r9, %%r10;"
    "  adcx %%r12, %%r10;"
    "  movq %%r10, 80(%%rdi);"
    "  mulxq 48(%%rcx), %%r12, %%r13;"
    "  adox %%r11, %%r12;"
    "  adcx %%r14, %%r12;"
    "  mov $0, %%r8;"
    "  mulxq 56(%%rcx), %%r14, %%rdx;"
    "  adox %%r13, %%r14;"
    "  adcx %%rax, %%r14;"
    "  mov $0, %%rax;"
    "  adox %%rdx, %%rax;"
    "  adcx %%r8, %%rax;"
    "  movq 48(%%rsi), %%rdx;"
    "  mulxq 32(%%rcx), %%r8, %%r9;"
    "  xor %%r10, %%r10;"
    "  adcxq 80(%%rdi), %%r8;"
    "  movq %%r8, 80(%%rdi);"
    "  mulxq 40(%%rcx), %%r10, %%r11;"
    "  adox %%r9, %%r10;"
    "  adcx %%r12, %%r10;"
    "  movq %%r10, 88(%%rdi);"
    "  mulxq 48(%%rcx), %%r12, %%r13;"
    "  adox %%r11, %%r12;"
    "  adcx %%r14, %%r12;"
    "  mov $0, %%r8;"
    "  mulxq 56(%%rcx), %%r14, %%rdx;"
    "  adox %%r13, %%r14;"
    "  adcx %%rax, %%r14;"
    "  mov $0, %%rax;"
    "  adox %%rdx, %%rax;"
    "  adcx %%r8, %%rax;"
    "  movq 56(%%rsi), %%rdx;"
    "  mulxq 32(%%rcx), %%r8, %%r9;"
    "  xor %%r10, %%r10;"
    "  adcxq 88(%%rdi), %%r8;"
    "  movq %%r8, 88(%%rdi);"
    "  mulxq 40(%%rcx), %%r10, %%r11;"
    "  adox %%r9, %%r10;"
    "  adcx %%r12, %%r10;"
    "  movq %%r10, 96(%%rdi);"
    "  mulxq 48(%%rcx), %%r12, %%r13;"
    "  adox %%r11, %%r12;"
    "  adcx %%r14, %%r12;"
    "  movq %%r12, 104(%%rdi);"
    "  mov $0, %%r8;"
    "  mulxq 56(%%rcx), %%r14, %%rdx;"
    "  adox %%r13, %%r14;"
    "  adcx %%rax, %%r14;"
    "  movq %%r14, 112(%%rdi);"
    "  mov $0, %%rax;"
    "  adox %%rdx, %%rax;"
    "  adcx %%r8, %%rax;"
    "  movq %%rax, 120(%%rdi);"
    "  mov %%rdi, %%rsi;"
    "  pop %%rdi;"
    "  mov $38, %%rdx;"
    "  mulxq 32(%%rsi), %%r8, %%r13;"
    "  xor %%rcx, %%rcx;"
    "  adoxq 0(%%rsi), %%r8;"
    "  mulxq 40(%%rsi), %%r9, %%r12;"
    "  adcx %%r13, %%r9;"
    "  adoxq 8(%%rsi), %%r9;"
    "  mulxq 48(%%rsi), %%r10, %%r13;"
    "  adcx %%r12, %%r10;"
    "  adoxq 16(%%rsi), %%r10;"
    "  mulxq 56(%%rsi), %%r11, %%rax;"
    "  adcx %%r13, %%r11;"
    "  adoxq 24(%%rsi), %%r11;"
    "  adcx %%rcx, %%rax;"
    "  adox %%rcx, %%rax;"
    "  imul %%rdx, %%rax;"
    "  add %%rax, %%r8;"
    "  adcx %%rcx, %%r9;"
    "  movq %%r9, 8(%%rdi);"
    "  adcx %%rcx, %%r10;"
    "  movq %%r10, 16(%%rdi);"
    "  adcx %%rcx, %%r11;"
    "  movq %%r11, 24(%%rdi);"
    "  mov $0, %%rax;"
    "  cmovc %%rdx, %%rax;"
    "  add %%rax, %%r8;"
    "  movq %%r8, 0(%%rdi);"
    "  mov $38, %%rdx;"
    "  mulxq 96(%%rsi), %%r8, %%r13;"
    "  xor %%rcx, %%rcx;"
    "  adoxq 64(%%rsi), %%r8;"
    "  mulxq 104(%%rsi), %%r9, %%r12;"
    "  adcx %%r13, %%r9;"
    "  adoxq 72(%%rsi), %%r9;"
    "  mulxq 112(%%rsi), %%r10, %%r13;"
    "  adcx %%r12, %%r10;"
    "  adoxq 80(%%rsi), %%r10;"
    "  mulxq 120(%%rsi), %%r11, %%rax;"
    "  adcx %%r13, %%r11;"
    "  adoxq 88(%%rsi), %%r11;"
    "  adcx %%rcx, %%rax;"
    "  adox %%rcx, %%rax;"
    "  imul %%rdx, %%rax;"
    "  add %%rax, %%r8;"
    "  adcx %%rcx, %%r9;"
    "  movq %%r9, 40(%%rdi);"
    "  adcx %%rcx, %%r10;"
    "  movq %%r10, 48(%%rdi);"
    "  adcx %%rcx, %%r11;"
    "  movq %%r11, 56(%%rdi);"
    "  mov $0, %%rax;"
    "  cmovc %%rdx, %%rax;"
    "  add %%rax, %%r8;"
    "  movq %%r8, 32(%%rdi);"
  : "+r" (tmp_r), "+r" (dst_r), "+r" (in_a_r), "+r" (in_b_r)
  :
  : "memory", "cc", "%rax", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14"
  );

}
extern void fsqr_v(const uint64_t* tmp, const uint64_t* in_a, const uint64_t* dst) {
  register uint64_t* tmp_r asm("rdi") = tmp;
  register uint64_t* in_a_r asm("rsi") = in_a;
  register uint64_t* dst_r asm("rdx") = dst;

  __asm__ __volatile__(
    "  push %%rdx;"
    "  movq 0(%%rsi), %%rdx;"
    "  mulxq 8(%%rsi), %%r8, %%r14;"
    "  xor %%r15, %%r15;"
    "  mulxq 16(%%rsi), %%r9, %%r10;"
    "  adcx %%r14, %%r9;"
    "  mulxq 24(%%rsi), %%rax, %%rcx;"
    "  adcx %%rax, %%r10;"
    "  movq 24(%%rsi), %%rdx;"
    "  mulxq 8(%%rsi), %%r11, %%r12;"
    "  adcx %%rcx, %%r11;"
    "  mulxq 16(%%rsi), %%rax, %%r13;"
    "  adcx %%rax, %%r12;"
    "  movq 8(%%rsi), %%rdx;"
    "  adcx %%r15, %%r13;"
    "  mulxq 16(%%rsi), %%rax, %%rcx;"
    "  mov $0, %%r14;"
    "  xor %%r15, %%r15;"
    "  adox %%rax, %%r10;"
    "  adcx %%r8, %%r8;"
    "  adox %%rcx, %%r11;"
    "  adcx %%r9, %%r9;"
    "  adox %%r15, %%r12;"
    "  adcx %%r10, %%r10;"
    "  adox %%r15, %%r13;"
    "  adcx %%r11, %%r11;"
    "  adox %%r15, %%r14;"
    "  adcx %%r12, %%r12;"
    "  adcx %%r13, %%r13;"
    "  adcx %%r14, %%r14;"
    "  movq 0(%%rsi), %%rdx;"
    "  mulx %%rdx, %%rax, %%rcx;"
    "  movq %%rax, 0(%%rdi);"
    "  add %%rcx, %%r8;"
    "  movq %%r8, 8(%%rdi);"
    "  movq 8(%%rsi), %%rdx;"
    "  mulx %%rdx, %%rax, %%rcx;"
    "  adcx %%rax, %%r9;"
    "  movq %%r9, 16(%%rdi);"
    "  adcx %%rcx, %%r10;"
    "  movq %%r10, 24(%%rdi);"
    "  movq 16(%%rsi), %%rdx;"
    "  mulx %%rdx, %%rax, %%rcx;"
    "  adcx %%rax, %%r11;"
    "  movq %%r11, 32(%%rdi);"
    "  adcx %%rcx, %%r12;"
    "  movq %%r12, 40(%%rdi);"
    "  movq 24(%%rsi), %%rdx;"
    "  mulx %%rdx, %%rax, %%rcx;"
    "  adcx %%rax, %%r13;"
    "  movq %%r13, 48(%%rdi);"
    "  adcx %%rcx, %%r14;"
    "  movq %%r14, 56(%%rdi);"
    "  mov %%rdi, %%rsi;"
    "  pop %%rdi;"
    "  mov $38, %%rdx;"
    "  mulxq 32(%%rsi), %%r8, %%r13;"
    "  xor %%rcx, %%rcx;"
    "  adoxq 0(%%rsi), %%r8;"
    "  mulxq 40(%%rsi), %%r9, %%r12;"
    "  adcx %%r13, %%r9;"
    "  adoxq 8(%%rsi), %%r9;"
    "  mulxq 48(%%rsi), %%r10, %%r13;"
    "  adcx %%r12, %%r10;"
    "  adoxq 16(%%rsi), %%r10;"
    "  mulxq 56(%%rsi), %%r11, %%rax;"
    "  adcx %%r13, %%r11;"
    "  adoxq 24(%%rsi), %%r11;"
    "  adcx %%rcx, %%rax;"
    "  adox %%rcx, %%rax;"
    "  imul %%rdx, %%rax;"
    "  add %%rax, %%r8;"
    "  adcx %%rcx, %%r9;"
    "  movq %%r9, 8(%%rdi);"
    "  adcx %%rcx, %%r10;"
    "  movq %%r10, 16(%%rdi);"
    "  adcx %%rcx, %%r11;"
    "  movq %%r11, 24(%%rdi);"
    "  mov $0, %%rax;"
    "  cmovc %%rdx, %%rax;"
    "  add %%rax, %%r8;"
    "  movq %%r8, 0(%%rdi);"
  : "+r" (tmp_r), "+r" (dst_r), "+r" (in_a_r)
  : 
  : "memory", "cc", "%rax", "%rcx", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15"
  );
}
extern void fsqr2_v(const uint64_t* tmp, const uint64_t* in_a, const uint64_t* dst) {
  register uint64_t* tmp_r asm("rdi") = tmp;
  register uint64_t* in_a_r asm("rsi") = in_a;
  register uint64_t* dst_r asm("rdx") = dst;

  __asm__ __volatile__(
    "  push %%rdx;"
    "  movq 0(%%rsi), %%rdx;"
    "  mulxq 8(%%rsi), %%r8, %%r14;"
    "  xor %%r15, %%r15;"
    "  mulxq 16(%%rsi), %%r9, %%r10;"
    "  adcx %%r14, %%r9;"
    "  mulxq 24(%%rsi), %%rax, %%rcx;"
    "  adcx %%rax, %%r10;"
    "  movq 24(%%rsi), %%rdx;"
    "  mulxq 8(%%rsi), %%r11, %%r12;"
    "  adcx %%rcx, %%r11;"
    "  mulxq 16(%%rsi), %%rax, %%r13;"
    "  adcx %%rax, %%r12;"
    "  movq 8(%%rsi), %%rdx;"
    "  adcx %%r15, %%r13;"
    "  mulxq 16(%%rsi), %%rax, %%rcx;"
    "  mov $0, %%r14;"
    "  xor %%r15, %%r15;"
    "  adox %%rax, %%r10;"
    "  adcx %%r8, %%r8;"
    "  adox %%rcx, %%r11;"
    "  adcx %%r9, %%r9;"
    "  adox %%r15, %%r12;"
    "  adcx %%r10, %%r10;"
    "  adox %%r15, %%r13;"
    "  adcx %%r11, %%r11;"
    "  adox %%r15, %%r14;"
    "  adcx %%r12, %%r12;"
    "  adcx %%r13, %%r13;"
    "  adcx %%r14, %%r14;"
    "  movq 0(%%rsi), %%rdx;"
    "  mulx %%rdx, %%rax, %%rcx;"
    "  movq %%rax, 0(%%rdi);"
    "  add %%rcx, %%r8;"
    "  movq %%r8, 8(%%rdi);"
    "  movq 8(%%rsi), %%rdx;"
    "  mulx %%rdx, %%rax, %%rcx;"
    "  adcx %%rax, %%r9;"
    "  movq %%r9, 16(%%rdi);"
    "  adcx %%rcx, %%r10;"
    "  movq %%r10, 24(%%rdi);"
    "  movq 16(%%rsi), %%rdx;"
    "  mulx %%rdx, %%rax, %%rcx;"
    "  adcx %%rax, %%r11;"
    "  movq %%r11, 32(%%rdi);"
    "  adcx %%rcx, %%r12;"
    "  movq %%r12, 40(%%rdi);"
    "  movq 24(%%rsi), %%rdx;"
    "  mulx %%rdx, %%rax, %%rcx;"
    "  adcx %%rax, %%r13;"
    "  movq %%r13, 48(%%rdi);"
    "  adcx %%rcx, %%r14;"
    "  movq %%r14, 56(%%rdi);"
    "  movq 32(%%rsi), %%rdx;"
    "  mulxq 40(%%rsi), %%r8, %%r14;"
    "  xor %%r15, %%r15;"
    "  mulxq 48(%%rsi), %%r9, %%r10;"
    "  adcx %%r14, %%r9;"
    "  mulxq 56(%%rsi), %%rax, %%rcx;"
    "  adcx %%rax, %%r10;"
    "  movq 56(%%rsi), %%rdx;"
    "  mulxq 40(%%rsi), %%r11, %%r12;"
    "  adcx %%rcx, %%r11;"
    "  mulxq 48(%%rsi), %%rax, %%r13;"
    "  adcx %%rax, %%r12;"
    "  movq 40(%%rsi), %%rdx;"
    "  adcx %%r15, %%r13;"
    "  mulxq 48(%%rsi), %%rax, %%rcx;"
    "  mov $0, %%r14;"
    "  xor %%r15, %%r15;"
    "  adox %%rax, %%r10;"
    "  adcx %%r8, %%r8;"
    "  adox %%rcx, %%r11;"
    "  adcx %%r9, %%r9;"
    "  adox %%r15, %%r12;"
    "  adcx %%r10, %%r10;"
    "  adox %%r15, %%r13;"
    "  adcx %%r11, %%r11;"
    "  adox %%r15, %%r14;"
    "  adcx %%r12, %%r12;"
    "  adcx %%r13, %%r13;"
    "  adcx %%r14, %%r14;"
    "  movq 32(%%rsi), %%rdx;"
    "  mulx %%rdx, %%rax, %%rcx;"
    "  movq %%rax, 64(%%rdi);"
    "  add %%rcx, %%r8;"
    "  movq %%r8, 72(%%rdi);"
    "  movq 40(%%rsi), %%rdx;"
    "  mulx %%rdx, %%rax, %%rcx;"
    "  adcx %%rax, %%r9;"
    "  movq %%r9, 80(%%rdi);"
    "  adcx %%rcx, %%r10;"
    "  movq %%r10, 88(%%rdi);"
    "  movq 48(%%rsi), %%rdx;"
    "  mulx %%rdx, %%rax, %%rcx;"
    "  adcx %%rax, %%r11;"
    "  movq %%r11, 96(%%rdi);"
    "  adcx %%rcx, %%r12;"
    "  movq %%r12, 104(%%rdi);"
    "  movq 56(%%rsi), %%rdx;"
    "  mulx %%rdx, %%rax, %%rcx;"
    "  adcx %%rax, %%r13;"
    "  movq %%r13, 112(%%rdi);"
    "  adcx %%rcx, %%r14;"
    "  movq %%r14, 120(%%rdi);"
    "  mov %%rdi, %%rsi;"
    "  pop %%rdi;"
    "  mov $38, %%rdx;"
    "  mulxq 32(%%rsi), %%r8, %%r13;"
    "  xor %%rcx, %%rcx;"
    "  adoxq 0(%%rsi), %%r8;"
    "  mulxq 40(%%rsi), %%r9, %%r12;"
    "  adcx %%r13, %%r9;"
    "  adoxq 8(%%rsi), %%r9;"
    "  mulxq 48(%%rsi), %%r10, %%r13;"
    "  adcx %%r12, %%r10;"
    "  adoxq 16(%%rsi), %%r10;"
    "  mulxq 56(%%rsi), %%r11, %%rax;"
    "  adcx %%r13, %%r11;"
    "  adoxq 24(%%rsi), %%r11;"
    "  adcx %%rcx, %%rax;"
    "  adox %%rcx, %%rax;"
    "  imul %%rdx, %%rax;"
    "  add %%rax, %%r8;"
    "  adcx %%rcx, %%r9;"
    "  movq %%r9, 8(%%rdi);"
    "  adcx %%rcx, %%r10;"
    "  movq %%r10, 16(%%rdi);"
    "  adcx %%rcx, %%r11;"
    "  movq %%r11, 24(%%rdi);"
    "  mov $0, %%rax;"
    "  cmovc %%rdx, %%rax;"
    "  add %%rax, %%r8;"
    "  movq %%r8, 0(%%rdi);"
    "  mov $38, %%rdx;"
    "  mulxq 96(%%rsi), %%r8, %%r13;"
    "  xor %%rcx, %%rcx;"
    "  adoxq 64(%%rsi), %%r8;"
    "  mulxq 104(%%rsi), %%r9, %%r12;"
    "  adcx %%r13, %%r9;"
    "  adoxq 72(%%rsi), %%r9;"
    "  mulxq 112(%%rsi), %%r10, %%r13;"
    "  adcx %%r12, %%r10;"
    "  adoxq 80(%%rsi), %%r10;"
    "  mulxq 120(%%rsi), %%r11, %%rax;"
    "  adcx %%r13, %%r11;"
    "  adoxq 88(%%rsi), %%r11;"
    "  adcx %%rcx, %%rax;"
    "  adox %%rcx, %%rax;"
    "  imul %%rdx, %%rax;"
    "  add %%rax, %%r8;"
    "  adcx %%rcx, %%r9;"
    "  movq %%r9, 40(%%rdi);"
    "  adcx %%rcx, %%r10;"
    "  movq %%r10, 48(%%rdi);"
    "  adcx %%rcx, %%r11;"
    "  movq %%r11, 56(%%rdi);"
    "  mov $0, %%rax;"
    "  cmovc %%rdx, %%rax;"
    "  add %%rax, %%r8;"
    "  movq %%r8, 32(%%rdi);"
  : "+r" (tmp_r), "+r" (dst_r), "+r" (in_a_r)
  : 
  : "memory", "cc", "%rax", "%rcx", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15"
  );
}

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



// Done in C in rfc7748_25519.h
static inline
void fmul(uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b, uint64_t* tmp) {
  fmul_v(tmp, in_a, dst, in_b);
}

// Done in C in rfc7748_25519.h
static inline
void fsqr(uint64_t* dst, const uint64_t* in_a, uint64_t* tmp) {
  fsqr_v(tmp,in_a, dst);
}

// Done in C in rfc7748_25519.h
static inline
void fmul2(uint64_t* dst, const uint64_t* in_a, const uint64_t* in_b, uint64_t* tmp) {
  fmul2_v(tmp, in_a, dst, in_b);
}

// Done in C in rfc7748_25519.h
static inline
void fsqr2(uint64_t* dst, const uint64_t* in_a, uint64_t* tmp) {
  fsqr2_v(tmp, in_a, dst);
}


//extern void cswap2_v(uint64_t *const p0, uint64_t *const p1, uint8_t bit);
//static inline void cswap2(uint8_t bit, uint64_t *const p0, uint64_t *const p1) {
//  cswap2_v(p0, p1, bit);
//}

// Not quite Vale code, but close enough for the experiment
static inline void cswap1(uint8_t bit, uint64_t *const p0, uint64_t *const p1) {
  uint64_t temp;
  __asm__ __volatile__(
    "test %9, %9 ;"
    "movq %0, %8 ;"
    "cmovnzq %4, %0 ;"
    "cmovnzq %8, %4 ;"
    "movq %1, %8 ;"
    "cmovnzq %5, %1 ;"
    "cmovnzq %8, %5 ;"
    "movq %2, %8 ;"
    "cmovnzq %6, %2 ;"
    "cmovnzq %8, %6 ;"
    "movq %3, %8 ;"
    "cmovnzq %7, %3 ;"
    "cmovnzq %8, %7 ;"
    : "+r"(p0[0]), "+r"(p0[1]), "+r"(p0[2]), "+r"(p0[3]),
      "+r"(p1[0]), "+r"(p1[1]), "+r"(p1[2]), "+r"(p1[3]),
      "=r"(temp)
    : "r"(bit)
    : "cc"
  );
}

static inline void cswap2(uint8_t bit, uint64_t *const p0, uint64_t *const p1) {
  cswap1(bit,p0,p1);
  cswap1(bit,p0+4,p1+4);
}




