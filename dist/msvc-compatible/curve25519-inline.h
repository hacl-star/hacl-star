#ifdef __GNUC__
#pragma once
#include <inttypes.h>

// Computes the addition of four-element f1 with value in f2
// and returns the carry (if any)
static inline uint64_t add1_inline (uint64_t *out1, uint64_t *f1, uint64_t f2) 
{
  uint64_t carry_r;

  asm volatile(
    // Clear registers to propagate the carry bit
    "  xor %%r8, %%r8;"
    "  xor %%r9, %%r9;"
    "  xor %%r10, %%r10;"
    "  xor %%r11, %%r11;"
    "  xor %1, %1;"

    // Begin addition chain
    "  addq 0(%3), %0;"
    "  movq %0, 0(%2);"
    "  adcxq 8(%3), %%r8;"
    "  movq %%r8, 8(%2);"
    "  adcxq 16(%3), %%r9;"
    "  movq %%r9, 16(%2);"
    "  adcxq 24(%3), %%r10;"
    "  movq %%r10, 24(%2);"

    // Return the carry bit in a register
    "  adcx %%r11, %1;"
  : "+&r" (f2), "=&r" (carry_r)
  : "r" (out1), "r" (f1)
  : "%r8", "%r9", "%r10", "%r11", "memory", "cc"
  );

  return carry_r;
}

static inline void fadd_inline (uint64_t *out1, uint64_t *f1, uint64_t *f2) 
{

  asm volatile(
    "  movq 0(%0), %%r8;"
    "  addq 0(%2), %%r8;"
    "  movq 8(%0), %%r9;"
    "  adcxq 8(%2), %%r9;"
    "  movq 16(%0), %%r10;"
    "  adcxq 16(%2), %%r10;"
    "  movq 24(%0), %%r11;"
    "  adcxq 24(%2), %%r11;"
    "  mov $0, %%rax;"
    "  mov $38, %0;"
    "  cmovc %0, %%rax;"
    "  xor %%rcx, %%rcx;"
    "  add %%rax, %%r8;"
    "  adcx %%rcx, %%r9;"
    "  movq %%r9, 8(%1);"
    "  adcx %%rcx, %%r10;"
    "  movq %%r10, 16(%1);"
    "  adcx %%rcx, %%r11;"
    "  movq %%r11, 24(%1);"
    "  mov $0, %%rax;"
    "  cmovc %0, %%rax;"
    "  add %%rax, %%r8;"
    "  movq %%r8, 0(%1);"
  : "+&r" (f2)
  : "r" (out1), "r" (f1)
  : "%rax", "%rcx", "%r8", "%r9", "%r10", "%r11", "memory", "cc"
  );
}

static inline void fsub_inline (uint64_t *out1, uint64_t *f1, uint64_t *f2) 
{

  asm volatile(
    "  movq 0(%1), %%r8;"
    "  subq 0(%2), %%r8;"
    "  movq 8(%1), %%r9;"
    "  sbbq 8(%2), %%r9;"
    "  movq 16(%1), %%r10;"
    "  sbbq 16(%2), %%r10;"
    "  movq 24(%1), %%r11;"
    "  sbbq 24(%2), %%r11;"
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
    "  movq %%r8, 0(%0);"
    "  movq %%r9, 8(%0);"
    "  movq %%r10, 16(%0);"
    "  movq %%r11, 24(%0);"
  : 
  : "r" (out1), "r" (f1), "r" (f2)
  : "%rax", "%rcx", "%r8", "%r9", "%r10", "%r11", "memory", "cc"
  );
}

// Computes a field multiplication: out <- f1 * f2
static inline void fmul_inline (uint64_t *tmp, uint64_t *f1, uint64_t *out, uint64_t *f2) 
{
  register uint64_t *out_r asm("rdx") = out;

  asm volatile(
    // Save dst_ptr which will be clobbered by the raw multiplication
    "  mov %%rdx, %%r15;"

    /////// Compute the raw multiplication: tmp <- src1 * src2 ////// 

    // Compute src1[0] * src2
    "  movq 0(%1), %%rdx;"
    "  mulxq 0(%3), %%r8, %%r9;"       "  xor %%r10, %%r10;"     "  movq %%r8, 0(%0);"
    "  mulxq 8(%3), %%r10, %%r11;"     "  adox %%r9, %%r10;"     "  movq %%r10, 8(%0);"
    "  mulxq 16(%3), %%r12, %%r13;"    "  adox %%r11, %%r12;"
    "  mulxq 24(%3), %%r14, %%rdx;"    "  adox %%r13, %%r14;"    "  mov $0, %%rax;"
                                       "  adox %%rdx, %%rax;"

    // Compute src1[1] * src2
    "  movq 8(%1), %%rdx;"
    "  mulxq 0(%3), %%r8, %%r9;"       "  xor %%r10, %%r10;"     "  adcxq 8(%0), %%r8;"    "  movq %%r8, 8(%0);"
    "  mulxq 8(%3), %%r10, %%r11;"     "  adox %%r9, %%r10;"     "  adcx %%r12, %%r10;"    "  movq %%r10, 16(%0);"
    "  mulxq 16(%3), %%r12, %%r13;"    "  adox %%r11, %%r12;"    "  adcx %%r14, %%r12;"    "  mov $0, %%r8;"
    "  mulxq 24(%3), %%r14, %%rdx;"    "  adox %%r13, %%r14;"    "  adcx %%rax, %%r14;"    "  mov $0, %%rax;"
                                       "  adox %%rdx, %%rax;"    "  adcx %%r8, %%rax;"


    // Compute src1[2] * src2
    "  movq 16(%1), %%rdx;"
    "  mulxq 0(%3), %%r8, %%r9;"       "  xor %%r10, %%r10;"    "  adcxq 16(%0), %%r8;"    "  movq %%r8, 16(%0);"
    "  mulxq 8(%3), %%r10, %%r11;"     "  adox %%r9, %%r10;"     "  adcx %%r12, %%r10;"    "  movq %%r10, 24(%0);"
    "  mulxq 16(%3), %%r12, %%r13;"    "  adox %%r11, %%r12;"    "  adcx %%r14, %%r12;"    "  mov $0, %%r8;"
    "  mulxq 24(%3), %%r14, %%rdx;"    "  adox %%r13, %%r14;"    "  adcx %%rax, %%r14;"    "  mov $0, %%rax;"
                                       "  adox %%rdx, %%rax;"    "  adcx %%r8, %%rax;"


    // Compute src1[3] * src2
    "  movq 24(%1), %%rdx;"
    "  mulxq 0(%3), %%r8, %%r9;"       "  xor %%r10, %%r10;"    "  adcxq 24(%0), %%r8;"    "  movq %%r8, 24(%0);"
    "  mulxq 8(%3), %%r10, %%r11;"     "  adox %%r9, %%r10;"     "  adcx %%r12, %%r10;"    "  movq %%r10, 32(%0);"
    "  mulxq 16(%3), %%r12, %%r13;"    "  adox %%r11, %%r12;"    "  adcx %%r14, %%r12;"    "  movq %%r12, 40(%0);"    "  mov $0, %%r8;"
    "  mulxq 24(%3), %%r14, %%rdx;"    "  adox %%r13, %%r14;"    "  adcx %%rax, %%r14;"    "  movq %%r14, 48(%0);"    "  mov $0, %%rax;"
                                       "  adox %%rdx, %%rax;"    "  adcx %%r8, %%rax;"     "  movq %%rax, 56(%0);"
    "  mov %0, %1;"

    // Restore dst_ptr
    "  mov %%r15, %0;"

    /////// Wrap the result back into the field ////// 

    // Step1: Compute dst + carry == tmp_hi * 38 + tmp_lo
    "  mov $38, %%rdx;"
    "  mulxq 32(%1), %%r8, %%r13;"
    "  xor %3, %3;"
    "  adoxq 0(%1), %%r8;"
    "  mulxq 40(%1), %%r9, %%r12;"
    "  adcx %%r13, %%r9;"
    "  adoxq 8(%1), %%r9;"
    "  mulxq 48(%1), %%r10, %%r13;"
    "  adcx %%r12, %%r10;"
    "  adoxq 16(%1), %%r10;"
    "  mulxq 56(%1), %%r11, %%rax;"
    "  adcx %%r13, %%r11;"
    "  adoxq 24(%1), %%r11;"
    "  adcx %3, %%rax;"
    "  adox %3, %%rax;"

    // Step2: Fold the carry back into dst
    "  imul %%rdx, %%rax;"
    "  add %%rax, %%r8;"
    "  adcx %3, %%r9;"
    "  movq %%r9, 8(%0);"
    "  adcx %3, %%r10;"
    "  movq %%r10, 16(%0);"
    "  adcx %3, %%r11;"
    "  movq %%r11, 24(%0);"
    "  mov $0, %%rax;"
    "  cmovc %%rdx, %%rax;"
    "  add %%rax, %%r8;"
    "  movq %%r8, 0(%0);"
  : "+&r" (tmp), "+&r" (f1), "+&r" (out_r), "+&r" (f2)
  : 
  : "%rax", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory", "cc"
  );
}

static inline void fmul2_inline (uint64_t *tmp, uint64_t *f1, uint64_t *out1, uint64_t *f2) 
{
  register uint64_t *out1_r asm("rdx") = out1;

  asm volatile(
    "  mov %%rdx, %%r15;"
    // Compute src1[0] * src2
    "  movq 0(%1), %%rdx;"
    "  mulxq 0(%3), %%r8, %%r9;"       "  xor %%r10, %%r10;"     "  movq %%r8, 0(%0);"
    "  mulxq 8(%3), %%r10, %%r11;"     "  adox %%r9, %%r10;"     "  movq %%r10, 8(%0);"
    "  mulxq 16(%3), %%r12, %%r13;"    "  adox %%r11, %%r12;"
    "  mulxq 24(%3), %%r14, %%rdx;"    "  adox %%r13, %%r14;"    "  mov $0, %%rax;"
                                       "  adox %%rdx, %%rax;"

    // Compute src1[1] * src2
    "  movq 8(%1), %%rdx;"
    "  mulxq 0(%3), %%r8, %%r9;"       "  xor %%r10, %%r10;"     "  adcxq 8(%0), %%r8;"    "  movq %%r8, 8(%0);"
    "  mulxq 8(%3), %%r10, %%r11;"     "  adox %%r9, %%r10;"     "  adcx %%r12, %%r10;"    "  movq %%r10, 16(%0);"
    "  mulxq 16(%3), %%r12, %%r13;"    "  adox %%r11, %%r12;"    "  adcx %%r14, %%r12;"    "  mov $0, %%r8;"
    "  mulxq 24(%3), %%r14, %%rdx;"    "  adox %%r13, %%r14;"    "  adcx %%rax, %%r14;"    "  mov $0, %%rax;"
                                       "  adox %%rdx, %%rax;"    "  adcx %%r8, %%rax;"


    // Compute src1[2] * src2
    "  movq 16(%1), %%rdx;"
    "  mulxq 0(%3), %%r8, %%r9;"       "  xor %%r10, %%r10;"    "  adcxq 16(%0), %%r8;"    "  movq %%r8, 16(%0);"
    "  mulxq 8(%3), %%r10, %%r11;"     "  adox %%r9, %%r10;"     "  adcx %%r12, %%r10;"    "  movq %%r10, 24(%0);"
    "  mulxq 16(%3), %%r12, %%r13;"    "  adox %%r11, %%r12;"    "  adcx %%r14, %%r12;"    "  mov $0, %%r8;"
    "  mulxq 24(%3), %%r14, %%rdx;"    "  adox %%r13, %%r14;"    "  adcx %%rax, %%r14;"    "  mov $0, %%rax;"
                                       "  adox %%rdx, %%rax;"    "  adcx %%r8, %%rax;"


    // Compute src1[3] * src2
    "  movq 24(%1), %%rdx;"
    "  mulxq 0(%3), %%r8, %%r9;"       "  xor %%r10, %%r10;"    "  adcxq 24(%0), %%r8;"    "  movq %%r8, 24(%0);"
    "  mulxq 8(%3), %%r10, %%r11;"     "  adox %%r9, %%r10;"     "  adcx %%r12, %%r10;"    "  movq %%r10, 32(%0);"
    "  mulxq 16(%3), %%r12, %%r13;"    "  adox %%r11, %%r12;"    "  adcx %%r14, %%r12;"    "  movq %%r12, 40(%0);"    "  mov $0, %%r8;"
    "  mulxq 24(%3), %%r14, %%rdx;"    "  adox %%r13, %%r14;"    "  adcx %%rax, %%r14;"    "  movq %%r14, 48(%0);"    "  mov $0, %%rax;"
                                       "  adox %%rdx, %%rax;"    "  adcx %%r8, %%rax;"     "  movq %%rax, 56(%0);"
    // Compute src1[0] * src2
    "  movq 32(%1), %%rdx;"
    "  mulxq 32(%3), %%r8, %%r9;"       "  xor %%r10, %%r10;"     "  movq %%r8, 64(%0);"
    "  mulxq 40(%3), %%r10, %%r11;"     "  adox %%r9, %%r10;"     "  movq %%r10, 72(%0);"
    "  mulxq 48(%3), %%r12, %%r13;"    "  adox %%r11, %%r12;"
    "  mulxq 56(%3), %%r14, %%rdx;"    "  adox %%r13, %%r14;"    "  mov $0, %%rax;"
                                       "  adox %%rdx, %%rax;"

    // Compute src1[1] * src2
    "  movq 40(%1), %%rdx;"
    "  mulxq 32(%3), %%r8, %%r9;"       "  xor %%r10, %%r10;"     "  adcxq 72(%0), %%r8;"    "  movq %%r8, 72(%0);"
    "  mulxq 40(%3), %%r10, %%r11;"     "  adox %%r9, %%r10;"     "  adcx %%r12, %%r10;"    "  movq %%r10, 80(%0);"
    "  mulxq 48(%3), %%r12, %%r13;"    "  adox %%r11, %%r12;"    "  adcx %%r14, %%r12;"    "  mov $0, %%r8;"
    "  mulxq 56(%3), %%r14, %%rdx;"    "  adox %%r13, %%r14;"    "  adcx %%rax, %%r14;"    "  mov $0, %%rax;"
                                       "  adox %%rdx, %%rax;"    "  adcx %%r8, %%rax;"


    // Compute src1[2] * src2
    "  movq 48(%1), %%rdx;"
    "  mulxq 32(%3), %%r8, %%r9;"       "  xor %%r10, %%r10;"    "  adcxq 80(%0), %%r8;"    "  movq %%r8, 80(%0);"
    "  mulxq 40(%3), %%r10, %%r11;"     "  adox %%r9, %%r10;"     "  adcx %%r12, %%r10;"    "  movq %%r10, 88(%0);"
    "  mulxq 48(%3), %%r12, %%r13;"    "  adox %%r11, %%r12;"    "  adcx %%r14, %%r12;"    "  mov $0, %%r8;"
    "  mulxq 56(%3), %%r14, %%rdx;"    "  adox %%r13, %%r14;"    "  adcx %%rax, %%r14;"    "  mov $0, %%rax;"
                                       "  adox %%rdx, %%rax;"    "  adcx %%r8, %%rax;"


    // Compute src1[3] * src2
    "  movq 56(%1), %%rdx;"
    "  mulxq 32(%3), %%r8, %%r9;"       "  xor %%r10, %%r10;"    "  adcxq 88(%0), %%r8;"    "  movq %%r8, 88(%0);"
    "  mulxq 40(%3), %%r10, %%r11;"     "  adox %%r9, %%r10;"     "  adcx %%r12, %%r10;"    "  movq %%r10, 96(%0);"
    "  mulxq 48(%3), %%r12, %%r13;"    "  adox %%r11, %%r12;"    "  adcx %%r14, %%r12;"    "  movq %%r12, 104(%0);"    "  mov $0, %%r8;"
    "  mulxq 56(%3), %%r14, %%rdx;"    "  adox %%r13, %%r14;"    "  adcx %%rax, %%r14;"    "  movq %%r14, 112(%0);"    "  mov $0, %%rax;"
                                       "  adox %%rdx, %%rax;"    "  adcx %%r8, %%rax;"     "  movq %%rax, 120(%0);"
    "  mov %0, %1;"
    "  mov %%r15, %0;"
    // Step1: Compute dst + carry == tmp_hi * 38 + tmp_lo
    "  mov $38, %%rdx;"
    "  mulxq 32(%1), %%r8, %%r13;"
    "  xor %3, %3;"
    "  adoxq 0(%1), %%r8;"
    "  mulxq 40(%1), %%r9, %%r12;"
    "  adcx %%r13, %%r9;"
    "  adoxq 8(%1), %%r9;"
    "  mulxq 48(%1), %%r10, %%r13;"
    "  adcx %%r12, %%r10;"
    "  adoxq 16(%1), %%r10;"
    "  mulxq 56(%1), %%r11, %%rax;"
    "  adcx %%r13, %%r11;"
    "  adoxq 24(%1), %%r11;"
    "  adcx %3, %%rax;"
    "  adox %3, %%rax;"

    // Step2: Fold the carry back into dst
    "  imul %%rdx, %%rax;"
    "  add %%rax, %%r8;"
    "  adcx %3, %%r9;"
    "  movq %%r9, 8(%0);"
    "  adcx %3, %%r10;"
    "  movq %%r10, 16(%0);"
    "  adcx %3, %%r11;"
    "  movq %%r11, 24(%0);"
    "  mov $0, %%rax;"
    "  cmovc %%rdx, %%rax;"
    "  add %%rax, %%r8;"
    "  movq %%r8, 0(%0);"
    // Step1: Compute dst + carry == tmp_hi * 38 + tmp_lo
    "  mov $38, %%rdx;"
    "  mulxq 96(%1), %%r8, %%r13;"
    "  xor %3, %3;"
    "  adoxq 64(%1), %%r8;"
    "  mulxq 104(%1), %%r9, %%r12;"
    "  adcx %%r13, %%r9;"
    "  adoxq 72(%1), %%r9;"
    "  mulxq 112(%1), %%r10, %%r13;"
    "  adcx %%r12, %%r10;"
    "  adoxq 80(%1), %%r10;"
    "  mulxq 120(%1), %%r11, %%rax;"
    "  adcx %%r13, %%r11;"
    "  adoxq 88(%1), %%r11;"
    "  adcx %3, %%rax;"
    "  adox %3, %%rax;"

    // Step2: Fold the carry back into dst
    "  imul %%rdx, %%rax;"
    "  add %%rax, %%r8;"
    "  adcx %3, %%r9;"
    "  movq %%r9, 40(%0);"
    "  adcx %3, %%r10;"
    "  movq %%r10, 48(%0);"
    "  adcx %3, %%r11;"
    "  movq %%r11, 56(%0);"
    "  mov $0, %%rax;"
    "  cmovc %%rdx, %%rax;"
    "  add %%rax, %%r8;"
    "  movq %%r8, 32(%0);"
  : "+&r" (tmp), "+&r" (f1), "+&r" (out1_r), "+&r" (f2)
  : 
  : "%rax", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory", "cc"
  );
}

static inline void fmul1_inline (uint64_t *out1, uint64_t *f1, uint64_t f2) 
{
  register uint64_t f2_r asm("rdx") = f2;

  asm volatile(
    "  mulxq 0(%2), %%r8, %%rcx;"
    "  mulxq 8(%2), %%r9, %%r12;"
    "  add %%rcx, %%r9;"
    "  mov $0, %%rcx;"
    "  mulxq 16(%2), %%r10, %%r13;"
    "  adcx %%r12, %%r10;"
    "  mulxq 24(%2), %%r11, %%rax;"
    "  adcx %%r13, %%r11;"
    "  adcx %%rcx, %%rax;"
    "  mov $38, %%rdx;"
    "  imul %%rdx, %%rax;"
    "  add %%rax, %%r8;"
    "  adcx %%rcx, %%r9;"
    "  movq %%r9, 8(%1);"
    "  adcx %%rcx, %%r10;"
    "  movq %%r10, 16(%1);"
    "  adcx %%rcx, %%r11;"
    "  movq %%r11, 24(%1);"
    "  mov $0, %%rax;"
    "  cmovc %%rdx, %%rax;"
    "  add %%rax, %%r8;"
    "  movq %%r8, 0(%1);"
  : "+&r" (f2_r)
  : "r" (out1), "r" (f1)
  : "%rax", "%rcx", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "memory", "cc"
  );
}

static inline void cswap2_inline (uint64_t bit, uint64_t *p1, uint64_t *p2) 
{

  asm volatile(
    "  add $18446744073709551615, %0;"
    "  movq 0(%1), %%r8;"
    "  movq 0(%2), %%r9;"
    "  mov %%r8, %%r10;"
    "  cmovc %%r9, %%r8;"
    "  cmovc %%r10, %%r9;"
    "  movq %%r8, 0(%1);"
    "  movq %%r9, 0(%2);"
    "  movq 8(%1), %%r8;"
    "  movq 8(%2), %%r9;"
    "  mov %%r8, %%r10;"
    "  cmovc %%r9, %%r8;"
    "  cmovc %%r10, %%r9;"
    "  movq %%r8, 8(%1);"
    "  movq %%r9, 8(%2);"
    "  movq 16(%1), %%r8;"
    "  movq 16(%2), %%r9;"
    "  mov %%r8, %%r10;"
    "  cmovc %%r9, %%r8;"
    "  cmovc %%r10, %%r9;"
    "  movq %%r8, 16(%1);"
    "  movq %%r9, 16(%2);"
    "  movq 24(%1), %%r8;"
    "  movq 24(%2), %%r9;"
    "  mov %%r8, %%r10;"
    "  cmovc %%r9, %%r8;"
    "  cmovc %%r10, %%r9;"
    "  movq %%r8, 24(%1);"
    "  movq %%r9, 24(%2);"
    "  movq 32(%1), %%r8;"
    "  movq 32(%2), %%r9;"
    "  mov %%r8, %%r10;"
    "  cmovc %%r9, %%r8;"
    "  cmovc %%r10, %%r9;"
    "  movq %%r8, 32(%1);"
    "  movq %%r9, 32(%2);"
    "  movq 40(%1), %%r8;"
    "  movq 40(%2), %%r9;"
    "  mov %%r8, %%r10;"
    "  cmovc %%r9, %%r8;"
    "  cmovc %%r10, %%r9;"
    "  movq %%r8, 40(%1);"
    "  movq %%r9, 40(%2);"
    "  movq 48(%1), %%r8;"
    "  movq 48(%2), %%r9;"
    "  mov %%r8, %%r10;"
    "  cmovc %%r9, %%r8;"
    "  cmovc %%r10, %%r9;"
    "  movq %%r8, 48(%1);"
    "  movq %%r9, 48(%2);"
    "  movq 56(%1), %%r8;"
    "  movq 56(%2), %%r9;"
    "  mov %%r8, %%r10;"
    "  cmovc %%r9, %%r8;"
    "  cmovc %%r10, %%r9;"
    "  movq %%r8, 56(%1);"
    "  movq %%r9, 56(%2);"
  : "+&r" (bit)
  : "r" (p1), "r" (p2)
  : "%r8", "%r9", "%r10", "memory", "cc"
  );
}

static inline void fsqr_inline (uint64_t *tmp, uint64_t *f1, uint64_t *out1) 
{
  register uint64_t *out1_r asm("rdx") = out1;

  asm volatile(
    "  mov %%rdx, %%rbx;"
    "  movq 0(%1), %%rdx;"
    "  mulxq 8(%1), %%r8, %%r14;"
    "  xor %%r15, %%r15;"
    "  mulxq 16(%1), %%r9, %%r10;"
    "  adcx %%r14, %%r9;"
    "  mulxq 24(%1), %%rax, %%rcx;"
    "  adcx %%rax, %%r10;"
    "  movq 24(%1), %%rdx;"
    "  mulxq 8(%1), %%r11, %%r12;"
    "  adcx %%rcx, %%r11;"
    "  mulxq 16(%1), %%rax, %%r13;"
    "  adcx %%rax, %%r12;"
    "  movq 8(%1), %%rdx;"
    "  adcx %%r15, %%r13;"
    "  mulxq 16(%1), %%rax, %%rcx;"
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
    "  movq 0(%1), %%rdx;"
    "  mulx %%rdx, %%rax, %%rcx;"
    "  movq %%rax, 0(%0);"
    "  add %%rcx, %%r8;"
    "  movq %%r8, 8(%0);"
    "  movq 8(%1), %%rdx;"
    "  mulx %%rdx, %%rax, %%rcx;"
    "  adcx %%rax, %%r9;"
    "  movq %%r9, 16(%0);"
    "  adcx %%rcx, %%r10;"
    "  movq %%r10, 24(%0);"
    "  movq 16(%1), %%rdx;"
    "  mulx %%rdx, %%rax, %%rcx;"
    "  adcx %%rax, %%r11;"
    "  movq %%r11, 32(%0);"
    "  adcx %%rcx, %%r12;"
    "  movq %%r12, 40(%0);"
    "  movq 24(%1), %%rdx;"
    "  mulx %%rdx, %%rax, %%rcx;"
    "  adcx %%rax, %%r13;"
    "  movq %%r13, 48(%0);"
    "  adcx %%rcx, %%r14;"
    "  movq %%r14, 56(%0);"
    "  mov %0, %1;"
    "  mov %%rbx, %0;"
    // Step1: Compute dst + carry == tmp_hi * 38 + tmp_lo
    "  mov $38, %%rdx;"
    "  mulxq 32(%1), %%r8, %%r13;"
    "  xor %%rcx, %%rcx;"
    "  adoxq 0(%1), %%r8;"
    "  mulxq 40(%1), %%r9, %%r12;"
    "  adcx %%r13, %%r9;"
    "  adoxq 8(%1), %%r9;"
    "  mulxq 48(%1), %%r10, %%r13;"
    "  adcx %%r12, %%r10;"
    "  adoxq 16(%1), %%r10;"
    "  mulxq 56(%1), %%r11, %%rax;"
    "  adcx %%r13, %%r11;"
    "  adoxq 24(%1), %%r11;"
    "  adcx %%rcx, %%rax;"
    "  adox %%rcx, %%rax;"

    // Step2: Fold the carry back into dst
    "  imul %%rdx, %%rax;"
    "  add %%rax, %%r8;"
    "  adcx %%rcx, %%r9;"
    "  movq %%r9, 8(%0);"
    "  adcx %%rcx, %%r10;"
    "  movq %%r10, 16(%0);"
    "  adcx %%rcx, %%r11;"
    "  movq %%r11, 24(%0);"
    "  mov $0, %%rax;"
    "  cmovc %%rdx, %%rax;"
    "  add %%rax, %%r8;"
    "  movq %%r8, 0(%0);"
  : "+&r" (tmp), "+&r" (f1), "+&r" (out1_r)
  : 
  : "%rax", "%rbx", "%rcx", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory", "cc"
  );
}

static inline void fsqr2_inline (uint64_t *tmp, uint64_t *f, uint64_t *out1) 
{
  register uint64_t *out1_r asm("rdx") = out1;

  asm volatile(
    "  mov %%rdx, %%rbx;"
    "  movq 0(%1), %%rdx;"
    "  mulxq 8(%1), %%r8, %%r14;"
    "  xor %%r15, %%r15;"
    "  mulxq 16(%1), %%r9, %%r10;"
    "  adcx %%r14, %%r9;"
    "  mulxq 24(%1), %%rax, %%rcx;"
    "  adcx %%rax, %%r10;"
    "  movq 24(%1), %%rdx;"
    "  mulxq 8(%1), %%r11, %%r12;"
    "  adcx %%rcx, %%r11;"
    "  mulxq 16(%1), %%rax, %%r13;"
    "  adcx %%rax, %%r12;"
    "  movq 8(%1), %%rdx;"
    "  adcx %%r15, %%r13;"
    "  mulxq 16(%1), %%rax, %%rcx;"
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
    "  movq 0(%1), %%rdx;"
    "  mulx %%rdx, %%rax, %%rcx;"
    "  movq %%rax, 0(%0);"
    "  add %%rcx, %%r8;"
    "  movq %%r8, 8(%0);"
    "  movq 8(%1), %%rdx;"
    "  mulx %%rdx, %%rax, %%rcx;"
    "  adcx %%rax, %%r9;"
    "  movq %%r9, 16(%0);"
    "  adcx %%rcx, %%r10;"
    "  movq %%r10, 24(%0);"
    "  movq 16(%1), %%rdx;"
    "  mulx %%rdx, %%rax, %%rcx;"
    "  adcx %%rax, %%r11;"
    "  movq %%r11, 32(%0);"
    "  adcx %%rcx, %%r12;"
    "  movq %%r12, 40(%0);"
    "  movq 24(%1), %%rdx;"
    "  mulx %%rdx, %%rax, %%rcx;"
    "  adcx %%rax, %%r13;"
    "  movq %%r13, 48(%0);"
    "  adcx %%rcx, %%r14;"
    "  movq %%r14, 56(%0);"
    "  movq 32(%1), %%rdx;"
    "  mulxq 40(%1), %%r8, %%r14;"
    "  xor %%r15, %%r15;"
    "  mulxq 48(%1), %%r9, %%r10;"
    "  adcx %%r14, %%r9;"
    "  mulxq 56(%1), %%rax, %%rcx;"
    "  adcx %%rax, %%r10;"
    "  movq 56(%1), %%rdx;"
    "  mulxq 40(%1), %%r11, %%r12;"
    "  adcx %%rcx, %%r11;"
    "  mulxq 48(%1), %%rax, %%r13;"
    "  adcx %%rax, %%r12;"
    "  movq 40(%1), %%rdx;"
    "  adcx %%r15, %%r13;"
    "  mulxq 48(%1), %%rax, %%rcx;"
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
    "  movq 32(%1), %%rdx;"
    "  mulx %%rdx, %%rax, %%rcx;"
    "  movq %%rax, 64(%0);"
    "  add %%rcx, %%r8;"
    "  movq %%r8, 72(%0);"
    "  movq 40(%1), %%rdx;"
    "  mulx %%rdx, %%rax, %%rcx;"
    "  adcx %%rax, %%r9;"
    "  movq %%r9, 80(%0);"
    "  adcx %%rcx, %%r10;"
    "  movq %%r10, 88(%0);"
    "  movq 48(%1), %%rdx;"
    "  mulx %%rdx, %%rax, %%rcx;"
    "  adcx %%rax, %%r11;"
    "  movq %%r11, 96(%0);"
    "  adcx %%rcx, %%r12;"
    "  movq %%r12, 104(%0);"
    "  movq 56(%1), %%rdx;"
    "  mulx %%rdx, %%rax, %%rcx;"
    "  adcx %%rax, %%r13;"
    "  movq %%r13, 112(%0);"
    "  adcx %%rcx, %%r14;"
    "  movq %%r14, 120(%0);"
    "  mov %0, %1;"
    "  mov %%rbx, %0;"
    // Step1: Compute dst + carry == tmp_hi * 38 + tmp_lo
    "  mov $38, %%rdx;"
    "  mulxq 32(%1), %%r8, %%r13;"
    "  xor %%rcx, %%rcx;"
    "  adoxq 0(%1), %%r8;"
    "  mulxq 40(%1), %%r9, %%r12;"
    "  adcx %%r13, %%r9;"
    "  adoxq 8(%1), %%r9;"
    "  mulxq 48(%1), %%r10, %%r13;"
    "  adcx %%r12, %%r10;"
    "  adoxq 16(%1), %%r10;"
    "  mulxq 56(%1), %%r11, %%rax;"
    "  adcx %%r13, %%r11;"
    "  adoxq 24(%1), %%r11;"
    "  adcx %%rcx, %%rax;"
    "  adox %%rcx, %%rax;"

    // Step2: Fold the carry back into dst
    "  imul %%rdx, %%rax;"
    "  add %%rax, %%r8;"
    "  adcx %%rcx, %%r9;"
    "  movq %%r9, 8(%0);"
    "  adcx %%rcx, %%r10;"
    "  movq %%r10, 16(%0);"
    "  adcx %%rcx, %%r11;"
    "  movq %%r11, 24(%0);"
    "  mov $0, %%rax;"
    "  cmovc %%rdx, %%rax;"
    "  add %%rax, %%r8;"
    "  movq %%r8, 0(%0);"
    // Step1: Compute dst + carry == tmp_hi * 38 + tmp_lo
    "  mov $38, %%rdx;"
    "  mulxq 96(%1), %%r8, %%r13;"
    "  xor %%rcx, %%rcx;"
    "  adoxq 64(%1), %%r8;"
    "  mulxq 104(%1), %%r9, %%r12;"
    "  adcx %%r13, %%r9;"
    "  adoxq 72(%1), %%r9;"
    "  mulxq 112(%1), %%r10, %%r13;"
    "  adcx %%r12, %%r10;"
    "  adoxq 80(%1), %%r10;"
    "  mulxq 120(%1), %%r11, %%rax;"
    "  adcx %%r13, %%r11;"
    "  adoxq 88(%1), %%r11;"
    "  adcx %%rcx, %%rax;"
    "  adox %%rcx, %%rax;"

    // Step2: Fold the carry back into dst
    "  imul %%rdx, %%rax;"
    "  add %%rax, %%r8;"
    "  adcx %%rcx, %%r9;"
    "  movq %%r9, 40(%0);"
    "  adcx %%rcx, %%r10;"
    "  movq %%r10, 48(%0);"
    "  adcx %%rcx, %%r11;"
    "  movq %%r11, 56(%0);"
    "  mov $0, %%rax;"
    "  cmovc %%rdx, %%rax;"
    "  add %%rax, %%r8;"
    "  movq %%r8, 32(%0);"
  : "+&r" (tmp), "+&r" (f), "+&r" (out1_r)
  : 
  : "%rax", "%rbx", "%rcx", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory", "cc"
  );
}

#endif