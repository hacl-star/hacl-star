static inline void fadd(uint64_t *const c, uint64_t *const a, uint64_t *const b) {
  __asm__ __volatile__(
    "mov     $38, %%eax ;"
    "xorl  %%ecx, %%ecx ;"
    "movq   (%2),  %%r8 ;"  "adcx   (%1),  %%r8 ;"
    "movq  8(%2),  %%r9 ;"  "adcx  8(%1),  %%r9 ;"
    "movq 16(%2), %%r10 ;"  "adcx 16(%1), %%r10 ;"
    "movq 24(%2), %%r11 ;"  "adcx 24(%1), %%r11 ;"
    "cmovc %%eax, %%ecx ;"
    "xorl %%eax, %%eax  ;"
    "adcx %%rcx,  %%r8  ;"
    "adcx %%rax,  %%r9  ;"  "movq  %%r9,  8(%0) ;"
    "adcx %%rax, %%r10  ;"  "movq %%r10, 16(%0) ;"
    "adcx %%rax, %%r11  ;"  "movq %%r11, 24(%0) ;"
    "mov     $38, %%ecx ;"
    "cmovc %%ecx, %%eax ;"
    "addq %%rax,  %%r8  ;"  "movq  %%r8,   (%0) ;"
  :
  : "r" (c), "r" (a), "r" (b)
  : "memory", "cc", "%rax", "%rcx", "%r8", "%r9", "%r10", "%r11"
  );
}

static inline void fsub(uint64_t *const c, uint64_t *const a, uint64_t *const b) {
  __asm__ __volatile__(
    "mov     $38, %%eax ;"
    "movq   (%1),  %%r8 ;"  "subq   (%2),  %%r8 ;"
    "movq  8(%1),  %%r9 ;"  "sbbq  8(%2),  %%r9 ;"
    "movq 16(%1), %%r10 ;"  "sbbq 16(%2), %%r10 ;"
    "movq 24(%1), %%r11 ;"  "sbbq 24(%2), %%r11 ;"
    "mov      $0, %%ecx ;"
    "cmovc %%eax, %%ecx ;"
    "subq %%rcx,  %%r8  ;"
    "sbbq    $0,  %%r9  ;"  "movq  %%r9,  8(%0) ;"
    "sbbq    $0, %%r10  ;"  "movq %%r10, 16(%0) ;"
    "sbbq    $0, %%r11  ;"  "movq %%r11, 24(%0) ;"
    "mov     $0, %%ecx  ;"
    "cmovc %%eax, %%ecx ;"
    "subq %%rcx,  %%r8  ;"  "movq  %%r8,   (%0) ;"
  :
  : "r" (c), "r" (a), "r" (b)
  : "memory", "cc", "%rax", "%rcx", "%r8", "%r9", "%r10", "%r11"
  );
}

static inline
void mul(uint64_t *const c, uint64_t *const a, uint64_t *const b) {
  __asm__ __volatile__(
    "movq   (%1), %%rdx; " /* A[0] */
    "mulx   (%2),  %%r8,  %%r9; " /* A[0]*B[0] */    "xorl %%r10d, %%r10d ;"                           "movq  %%r8,  (%0) ;"
    "mulx  8(%2), %%r10, %%r11; " /* A[0]*B[1] */    "adox  %%r9, %%r10 ;"                             "movq %%r10, 8(%0) ;"
    "mulx 16(%2), %%r12, %%r13; " /* A[0]*B[2] */    "adox %%r11, %%r12 ;"
    "mulx 24(%2), %%r14, %%rdx; " /* A[0]*B[3] */    "adox %%r13, %%r14 ;"                                                       "movq $0, %%rax ;"
    /*******************************************/    "adox %%rdx, %%rax ;"

    "movq  8(%1), %%rdx; " /* A[1] */
    "mulx   (%2),  %%r8,  %%r9; " /* A[1]*B[0] */    "xorl %%r10d, %%r10d ;"  "adcx 8(%0),  %%r8 ;"    "movq  %%r8,  8(%0) ;"
    "mulx  8(%2), %%r10, %%r11; " /* A[1]*B[1] */    "adox  %%r9, %%r10 ;"    "adcx %%r12, %%r10 ;"    "movq %%r10, 16(%0) ;"
    "mulx 16(%2), %%r12, %%r13; " /* A[1]*B[2] */    "adox %%r11, %%r12 ;"    "adcx %%r14, %%r12 ;"                              "movq $0, %%r8  ;"
    "mulx 24(%2), %%r14, %%rdx; " /* A[1]*B[3] */    "adox %%r13, %%r14 ;"    "adcx %%rax, %%r14 ;"                              "movq $0, %%rax ;"
    /*******************************************/    "adox %%rdx, %%rax ;"    "adcx  %%r8, %%rax ;"

    "movq 16(%1), %%rdx; " /* A[2] */
    "mulx   (%2),  %%r8,  %%r9; " /* A[2]*B[0] */    "xorl %%r10d, %%r10d ;"  "adcx 16(%0), %%r8 ;"    "movq  %%r8, 16(%0) ;"
    "mulx  8(%2), %%r10, %%r11; " /* A[2]*B[1] */    "adox  %%r9, %%r10 ;"    "adcx %%r12, %%r10 ;"    "movq %%r10, 24(%0) ;"
    "mulx 16(%2), %%r12, %%r13; " /* A[2]*B[2] */    "adox %%r11, %%r12 ;"    "adcx %%r14, %%r12 ;"                              "movq $0, %%r8  ;"
    "mulx 24(%2), %%r14, %%rdx; " /* A[2]*B[3] */    "adox %%r13, %%r14 ;"    "adcx %%rax, %%r14 ;"                              "movq $0, %%rax ;"
    /*******************************************/    "adox %%rdx, %%rax ;"    "adcx  %%r8, %%rax ;"

    "movq 24(%1), %%rdx; " /* A[3] */
    "mulx   (%2),  %%r8,  %%r9; " /* A[3]*B[0] */    "xorl %%r10d, %%r10d ;"  "adcx 24(%0), %%r8 ;"    "movq  %%r8, 24(%0) ;"
    "mulx  8(%2), %%r10, %%r11; " /* A[3]*B[1] */    "adox  %%r9, %%r10 ;"    "adcx %%r12, %%r10 ;"    "movq %%r10, 32(%0) ;"
    "mulx 16(%2), %%r12, %%r13; " /* A[3]*B[2] */    "adox %%r11, %%r12 ;"    "adcx %%r14, %%r12 ;"    "movq %%r12, 40(%0) ;"    "movq $0, %%r8  ;"
    "mulx 24(%2), %%r14, %%rdx; " /* A[3]*B[3] */    "adox %%r13, %%r14 ;"    "adcx %%rax, %%r14 ;"    "movq %%r14, 48(%0) ;"    "movq $0, %%rax ;"
    /*******************************************/    "adox %%rdx, %%rax ;"    "adcx  %%r8, %%rax ;"    "movq %%rax, 56(%0) ;"
  :
  : "r" (c), "r" (a), "r" (b)
  : "memory", "cc", "%rax", "%rdx", "%r8",
    "%r9", "%r10", "%r11", "%r12", "%r13", "%r14"
  );
}

static inline
void mul2(uint64_t *const c, uint64_t *const a, uint64_t *const b) {
  __asm__ __volatile__(
    "xorl %%r14d, %%r14d ;"
    "movq   (%1), %%rdx; " /* A[0] */
    "mulx   (%2),  %%r8, %%r12; " /* A[0]*B[0] */  "xorl %%r10d, %%r10d ;"  "movq %%r8, (%0) ;"
    "mulx  8(%2), %%r10, %%rax; " /* A[0]*B[1] */  "adox %%r10, %%r12 ;"
    "mulx 16(%2),  %%r8, %%rbx; " /* A[0]*B[2] */  "adox  %%r8, %%rax ;"
    "mulx 24(%2), %%r10, %%rcx; " /* A[0]*B[3] */  "adox %%r10, %%rbx ;"
    /*******************************************/  "adox %%r14, %%rcx ;"

    "movq  8(%1), %%rdx; " /* A[1] */
    "mulx   (%2),  %%r8,  %%r9; " /* A[1]*B[0] */  "adox %%r12,  %%r8 ;"  "movq  %%r8, 8(%0) ;"
    "mulx  8(%2), %%r10, %%r11; " /* A[1]*B[1] */  "adox %%r10,  %%r9 ;"  "adcx  %%r9, %%rax ;"
    "mulx 16(%2),  %%r8, %%r13; " /* A[1]*B[2] */  "adox  %%r8, %%r11 ;"  "adcx %%r11, %%rbx ;"
    "mulx 24(%2), %%r10, %%r12; " /* A[1]*B[3] */  "adox %%r10, %%r13 ;"  "adcx %%r13, %%rcx ;"
    /*******************************************/  "adox %%r14, %%r12 ;"  "adcx %%r14, %%r12 ;"

    "movq 16(%1), %%rdx; " /* A[2] */              "xorl %%r10d, %%r10d ;"
    "mulx   (%2),  %%r8,  %%r9; " /* A[2]*B[0] */  "adox %%rax,  %%r8 ;"  "movq %%r8, 16(%0) ;"
    "mulx  8(%2), %%r10, %%r11; " /* A[2]*B[1] */  "adox %%r10,  %%r9 ;"  "adcx  %%r9, %%rbx ;"
    "mulx 16(%2),  %%r8, %%r13; " /* A[2]*B[2] */  "adox  %%r8, %%r11 ;"  "adcx %%r11, %%rcx ;"
    "mulx 24(%2), %%r10, %%rax; " /* A[2]*B[3] */  "adox %%r10, %%r13 ;"  "adcx %%r13, %%r12 ;"
    /*******************************************/  "adox %%r14, %%rax ;"  "adcx %%r14, %%rax ;"

    "movq 24(%1), %%rdx; " /* A[3] */              "xorl %%r10d, %%r10d ;"
    "mulx   (%2),  %%r8,  %%r9; " /* A[3]*B[0] */  "adox %%rbx,  %%r8 ;"  "movq %%r8, 24(%0) ;"
    "mulx  8(%2), %%r10, %%r11; " /* A[3]*B[1] */  "adox %%r10,  %%r9 ;"  "adcx  %%r9, %%rcx ;"  "movq %%rcx, 32(%0) ;"
    "mulx 16(%2),  %%r8, %%r13; " /* A[3]*B[2] */  "adox  %%r8, %%r11 ;"  "adcx %%r11, %%r12 ;"  "movq %%r12, 40(%0) ;"
    "mulx 24(%2), %%r10, %%rbx; " /* A[3]*B[3] */  "adox %%r10, %%r13 ;"  "adcx %%r13, %%rax ;"  "movq %%rax, 48(%0) ;"
    /*******************************************/  "adox %%r14, %%rbx ;"  "adcx %%r14, %%rbx ;"  "movq %%rbx, 56(%0) ;"

    "movq 32(%1), %%rdx; " /* C[0] */
    "mulx 32(%2),  %%r8, %%r12; " /* C[0]*D[0] */  "xorl %%r10d, %%r10d ;" "movq %%r8, 64(%0);"
    "mulx 40(%2), %%r10, %%rax; " /* C[0]*D[1] */  "adox %%r10, %%r12 ;"
    "mulx 48(%2),  %%r8, %%rbx; " /* C[0]*D[2] */  "adox  %%r8, %%rax ;"
    "mulx 56(%2), %%r10, %%rcx; " /* C[0]*D[3] */  "adox %%r10, %%rbx ;"
    /*******************************************/  "adox %%r14, %%rcx ;"

    "movq 40(%1), %%rdx; " /* C[1] */              "xorl %%r10d, %%r10d ;"
    "mulx 32(%2),  %%r8,  %%r9; " /* C[1]*D[0] */  "adox %%r12,  %%r8 ;"  "movq  %%r8, 72(%0);"
    "mulx 40(%2), %%r10, %%r11; " /* C[1]*D[1] */  "adox %%r10,  %%r9 ;"  "adcx  %%r9, %%rax ;"
    "mulx 48(%2),  %%r8, %%r13; " /* C[1]*D[2] */  "adox  %%r8, %%r11 ;"  "adcx %%r11, %%rbx ;"
    "mulx 56(%2), %%r10, %%r12; " /* C[1]*D[3] */  "adox %%r10, %%r13 ;"  "adcx %%r13, %%rcx ;"
    /*******************************************/  "adox %%r14, %%r12 ;"  "adcx %%r14, %%r12 ;"

    "movq 48(%1), %%rdx; " /* C[2] */              "xorl %%r10d, %%r10d ;"
    "mulx 32(%2),  %%r8,  %%r9; " /* C[2]*D[0] */  "adox %%rax,  %%r8 ;"  "movq  %%r8, 80(%0);"
    "mulx 40(%2), %%r10, %%r11; " /* C[2]*D[1] */  "adox %%r10,  %%r9 ;"  "adcx  %%r9, %%rbx ;"
    "mulx 48(%2),  %%r8, %%r13; " /* C[2]*D[2] */  "adox  %%r8, %%r11 ;"  "adcx %%r11, %%rcx ;"
    "mulx 56(%2), %%r10, %%rax; " /* C[2]*D[3] */  "adox %%r10, %%r13 ;"  "adcx %%r13, %%r12 ;"
    /*******************************************/  "adox %%r14, %%rax ;"  "adcx %%r14, %%rax ;"

    "movq 56(%1), %%rdx; " /* C[3] */              "xorl %%r10d, %%r10d ;"
    "mulx 32(%2),  %%r8,  %%r9; " /* C[3]*D[0] */  "adox %%rbx,  %%r8 ;"  "movq  %%r8, 88(%0);"
    "mulx 40(%2), %%r10, %%r11; " /* C[3]*D[1] */  "adox %%r10,  %%r9 ;"  "adcx  %%r9, %%rcx ;"  "movq %%rcx,  96(%0) ;"
    "mulx 48(%2),  %%r8, %%r13; " /* C[3]*D[2] */  "adox  %%r8, %%r11 ;"  "adcx %%r11, %%r12 ;"  "movq %%r12, 104(%0) ;"
    "mulx 56(%2), %%r10, %%rbx; " /* C[3]*D[3] */  "adox %%r10, %%r13 ;"  "adcx %%r13, %%rax ;"  "movq %%rax, 112(%0) ;"
    /*******************************************/  "adox %%r14, %%rbx ;"  "adcx %%r14, %%rbx ;"  "movq %%rbx, 120(%0) ;"
  :
  : "r" (c), "r" (a), "r" (b)
  : "memory", "cc", "%rax", "%rbx", "%rcx", "%rdx",
    "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14"
  );
}

static inline
void sqr(uint64_t *const c, uint64_t *const a) {
  __asm__ __volatile__(
    "movq   (%1), %%rdx        ;" /* A[0]      */
    "mulx  8(%1),  %%r8, %%r14 ;" /* A[1]*A[0] */  "xorl %%r15d, %%r15d;"
    "mulx 16(%1),  %%r9, %%r10 ;" /* A[2]*A[0] */  "adcx %%r14,  %%r9 ;"
    "mulx 24(%1), %%rax, %%rcx ;" /* A[3]*A[0] */  "adcx %%rax, %%r10 ;"
    "movq 24(%1), %%rdx        ;" /* A[3]      */
    "mulx  8(%1), %%r11, %%r12 ;" /* A[1]*A[3] */  "adcx %%rcx, %%r11 ;"
    "mulx 16(%1), %%rax, %%r13 ;" /* A[2]*A[3] */  "adcx %%rax, %%r12 ;"
    "movq  8(%1), %%rdx        ;" /* A[1]      */  "adcx %%r15, %%r13 ;"
    "mulx 16(%1), %%rax, %%rcx ;" /* A[2]*A[1] */  "movq    $0, %%r14 ;"
    /*******************************************/  "adcx %%r15, %%r14 ;"

    "xorl %%r15d, %%r15d;"
    "adox %%rax, %%r10 ;"  "adcx  %%r8,  %%r8 ;"
    "adox %%rcx, %%r11 ;"  "adcx  %%r9,  %%r9 ;"
    "adox %%r15, %%r12 ;"  "adcx %%r10, %%r10 ;"
    "adox %%r15, %%r13 ;"  "adcx %%r11, %%r11 ;"
    "adox %%r15, %%r14 ;"  "adcx %%r12, %%r12 ;"
                           "adcx %%r13, %%r13 ;"
                           "adcx %%r14, %%r14 ;"

    "movq   (%1), %%rdx ;"  "mulx %%rdx, %%rax, %%rcx ;" /* A[0]^2 */
    /********************/  "movq %%rax,  0(%0) ;"
    "addq %%rcx,  %%r8 ;"   "movq  %%r8,  8(%0) ;"
    "movq  8(%1), %%rdx ;"  "mulx %%rdx, %%rax, %%rcx ;" /* A[1]^2 */
    "adcq %%rax,  %%r9 ;"   "movq  %%r9, 16(%0) ;"
    "adcq %%rcx, %%r10 ;"   "movq %%r10, 24(%0) ;"
    "movq 16(%1), %%rdx ;"  "mulx %%rdx, %%rax, %%rcx ;" /* A[2]^2 */
    "adcq %%rax, %%r11 ;"   "movq %%r11, 32(%0) ;"
    "adcq %%rcx, %%r12 ;"   "movq %%r12, 40(%0) ;"
    "movq 24(%1), %%rdx ;"  "mulx %%rdx, %%rax, %%rcx ;" /* A[3]^2 */
    "adcq %%rax, %%r13 ;"   "movq %%r13, 48(%0) ;"
    "adcq %%rcx, %%r14 ;"   "movq %%r14, 56(%0) ;"
  :
  : "r" (c), "r" (a)
  : "memory", "cc", "%rax", "%rcx", "%rdx",
    "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15"
  );
}

static inline
void sqr2(uint64_t *const c, uint64_t *const a) {
  __asm__ __volatile__(
    "movq   (%1), %%rdx        ;" /* A[0]      */
    "mulx  8(%1),  %%r8, %%r14 ;" /* A[1]*A[0] */  "xorl %%r15d, %%r15d;"
    "mulx 16(%1),  %%r9, %%r10 ;" /* A[2]*A[0] */  "adcx %%r14,  %%r9 ;"
    "mulx 24(%1), %%rax, %%rcx ;" /* A[3]*A[0] */  "adcx %%rax, %%r10 ;"
    "movq 24(%1), %%rdx        ;" /* A[3]      */
    "mulx  8(%1), %%r11, %%r12 ;" /* A[1]*A[3] */  "adcx %%rcx, %%r11 ;"
    "mulx 16(%1), %%rax, %%r13 ;" /* A[2]*A[3] */  "adcx %%rax, %%r12 ;"
    "movq  8(%1), %%rdx        ;" /* A[1]      */  "adcx %%r15, %%r13 ;"
    "mulx 16(%1), %%rax, %%rcx ;" /* A[2]*A[1] */  "movq    $0, %%r14 ;"
    /*******************************************/  "adcx %%r15, %%r14 ;"

    "xorl %%r15d, %%r15d;"
    "adox %%rax, %%r10 ;"  "adcx  %%r8,  %%r8 ;"
    "adox %%rcx, %%r11 ;"  "adcx  %%r9,  %%r9 ;"
    "adox %%r15, %%r12 ;"  "adcx %%r10, %%r10 ;"
    "adox %%r15, %%r13 ;"  "adcx %%r11, %%r11 ;"
    "adox %%r15, %%r14 ;"  "adcx %%r12, %%r12 ;"
                           "adcx %%r13, %%r13 ;"
                           "adcx %%r14, %%r14 ;"

    "movq   (%1), %%rdx ;"  "mulx %%rdx, %%rax, %%rcx ;" /* A[0]^2 */
    /********************/  "movq %%rax,  0(%0) ;"
    "addq %%rcx,  %%r8 ;"   "movq  %%r8,  8(%0) ;"
    "movq  8(%1), %%rdx ;"  "mulx %%rdx, %%rax, %%rcx ;" /* A[1]^2 */
    "adcq %%rax,  %%r9 ;"   "movq  %%r9, 16(%0) ;"
    "adcq %%rcx, %%r10 ;"   "movq %%r10, 24(%0) ;"
    "movq 16(%1), %%rdx ;"  "mulx %%rdx, %%rax, %%rcx ;" /* A[2]^2 */
    "adcq %%rax, %%r11 ;"   "movq %%r11, 32(%0) ;"
    "adcq %%rcx, %%r12 ;"   "movq %%r12, 40(%0) ;"
    "movq 24(%1), %%rdx ;"  "mulx %%rdx, %%rax, %%rcx ;" /* A[3]^2 */
    "adcq %%rax, %%r13 ;"   "movq %%r13, 48(%0) ;"
    "adcq %%rcx, %%r14 ;"   "movq %%r14, 56(%0) ;"


    "movq 32(%1), %%rdx        ;" /* B[0]      */
    "mulx 40(%1),  %%r8, %%r14 ;" /* B[1]*B[0] */  "xorl %%r15d, %%r15d;"
    "mulx 48(%1),  %%r9, %%r10 ;" /* B[2]*B[0] */  "adcx %%r14,  %%r9 ;"
    "mulx 56(%1), %%rax, %%rcx ;" /* B[3]*B[0] */  "adcx %%rax, %%r10 ;"
    "movq 56(%1), %%rdx        ;" /* B[3]      */
    "mulx 40(%1), %%r11, %%r12 ;" /* B[1]*B[3] */  "adcx %%rcx, %%r11 ;"
    "mulx 48(%1), %%rax, %%r13 ;" /* B[2]*B[3] */  "adcx %%rax, %%r12 ;"
    "movq 40(%1), %%rdx        ;" /* B[1]      */  "adcx %%r15, %%r13 ;"
    "mulx 48(%1), %%rax, %%rcx ;" /* B[2]*B[1] */  "movq    $0, %%r14 ;"
    /*******************************************/  "adcx %%r15, %%r14 ;"

    "xorl %%r15d, %%r15d;"
    "adox %%rax, %%r10 ;"  "adcx  %%r8,  %%r8 ;"
    "adox %%rcx, %%r11 ;"  "adcx  %%r9,  %%r9 ;"
    "adox %%r15, %%r12 ;"  "adcx %%r10, %%r10 ;"
    "adox %%r15, %%r13 ;"  "adcx %%r11, %%r11 ;"
    "adox %%r15, %%r14 ;"  "adcx %%r12, %%r12 ;"
                           "adcx %%r13, %%r13 ;"
                           "adcx %%r14, %%r14 ;"

    "movq 32(%1), %%rdx ;"  "mulx %%rdx, %%rax, %%rcx ;" /* B[0]^2 */
    /********************/  "movq %%rax,  64(%0) ;"
    "addq %%rcx,  %%r8 ;"   "movq  %%r8,  72(%0) ;"
    "movq 40(%1), %%rdx ;"  "mulx %%rdx, %%rax, %%rcx ;" /* B[1]^2 */
    "adcq %%rax,  %%r9 ;"   "movq  %%r9,  80(%0) ;"
    "adcq %%rcx, %%r10 ;"   "movq %%r10,  88(%0) ;"
    "movq 48(%1), %%rdx ;"  "mulx %%rdx, %%rax, %%rcx ;" /* B[2]^2 */
    "adcq %%rax, %%r11 ;"   "movq %%r11,  96(%0) ;"
    "adcq %%rcx, %%r12 ;"   "movq %%r12, 104(%0) ;"
    "movq 56(%1), %%rdx ;"  "mulx %%rdx, %%rax, %%rcx ;" /* B[3]^2 */
    "adcq %%rax, %%r13 ;"   "movq %%r13, 112(%0) ;"
    "adcq %%rcx, %%r14 ;"   "movq %%r14, 120(%0) ;"
  :
  : "r" (c), "r" (a)
  : "memory", "cc", "%rax", "%rcx", "%rdx",
    "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15"
  );
}

static inline
void carry_wide(uint64_t *const c, uint64_t *const a) {
  __asm__ __volatile__(
    "movl    $38, %%edx ;" /* 2*c = 38 = 2^256 */
    "mulx 32(%1),  %%r8, %%r10 ;" /* c*C[4] */  "xorl %%ebx, %%ebx ;"  "adox   (%1),  %%r8 ;"
    "mulx 40(%1),  %%r9, %%r11 ;" /* c*C[5] */  "adcx %%r10,  %%r9 ;"  "adox  8(%1),  %%r9 ;"
    "mulx 48(%1), %%r10, %%rax ;" /* c*C[6] */  "adcx %%r11, %%r10 ;"  "adox 16(%1), %%r10 ;"
    "mulx 56(%1), %%r11, %%rcx ;" /* c*C[7] */  "adcx %%rax, %%r11 ;"  "adox 24(%1), %%r11 ;"
    /****************************************/  "adcx %%rbx, %%rcx ;"  "adox  %%rbx, %%rcx ;"
    "imul %%rdx, %%rcx ;" /* c*C[4], cf=0, of=0 */
    "adcx %%rcx,  %%r8 ;"
    "adcx %%rbx,  %%r9 ;"  "movq  %%r9,  8(%0) ;"
    "adcx %%rbx, %%r10 ;"  "movq %%r10, 16(%0) ;"
    "adcx %%rbx, %%r11 ;"  "movq %%r11, 24(%0) ;"
    "mov     $0, %%ecx ;"
    "cmovc %%edx, %%ecx ;"
    "addq %%rcx,  %%r8 ;"  "movq  %%r8,   (%0) ;"
  :
  : "r" (c), "r" (a)
  : "memory", "cc", "%rax", "%rbx", "%rcx", "%rdx", "%r8", "%r9", "%r10", "%r11"
  );
}
static inline
void carry_wide2(uint64_t *const c, uint64_t *const a) {
  __asm__ __volatile__(
    "movl    $38, %%edx; " /* 2*c = 38 = 2^256 */
    "mulx 32(%1),  %%r8, %%r10; " /* c*C[4] */   "xorl %%ebx, %%ebx ;"  "adox   (%1),  %%r8 ;"
    "mulx 40(%1),  %%r9, %%r11; " /* c*C[5] */   "adcx %%r10,  %%r9 ;"  "adox  8(%1),  %%r9 ;"
    "mulx 48(%1), %%r10, %%rax; " /* c*C[6] */   "adcx %%r11, %%r10 ;"  "adox 16(%1), %%r10 ;"
    "mulx 56(%1), %%r11, %%rcx; " /* c*C[7] */   "adcx %%rax, %%r11 ;"  "adox 24(%1), %%r11 ;"
    /****************************************/   "adcx %%rbx, %%rcx ;"  "adox  %%rbx, %%rcx ;"
    "imul %%rdx, %%rcx ;" /* c*C[4], cf=0, of=0 */
    "adcx %%rcx,  %%r8 ;"
    "adcx %%rbx,  %%r9 ;"  "movq  %%r9,  8(%0) ;"
    "adcx %%rbx, %%r10 ;"  "movq %%r10, 16(%0) ;"
    "adcx %%rbx, %%r11 ;"  "movq %%r11, 24(%0) ;"
    "mov     $0, %%ecx ;"
    "cmovc %%edx, %%ecx ;"
    "addq %%rcx,  %%r8 ;"  "movq  %%r8,   (%0) ;"

    "mulx  96(%1),  %%r8, %%r10; " /* c*C[4] */  "xorl %%ebx, %%ebx ;"  "adox 64(%1),  %%r8 ;"
    "mulx 104(%1),  %%r9, %%r11; " /* c*C[5] */  "adcx %%r10,  %%r9 ;"  "adox 72(%1),  %%r9 ;"
    "mulx 112(%1), %%r10, %%rax; " /* c*C[6] */  "adcx %%r11, %%r10 ;"  "adox 80(%1), %%r10 ;"
    "mulx 120(%1), %%r11, %%rcx; " /* c*C[7] */  "adcx %%rax, %%r11 ;"  "adox 88(%1), %%r11 ;"
    /*****************************************/  "adcx %%rbx, %%rcx ;"  "adox  %%rbx, %%rcx ;"
    "imul %%rdx, %%rcx ;" /* c*C[4], cf=0, of=0 */
    "adcx %%rcx,  %%r8 ;"
    "adcx %%rbx,  %%r9 ;"  "movq  %%r9, 40(%0) ;"
    "adcx %%rbx, %%r10 ;"  "movq %%r10, 48(%0) ;"
    "adcx %%rbx, %%r11 ;"  "movq %%r11, 56(%0) ;"
    "mov     $0, %%ecx ;"
    "cmovc %%edx, %%ecx ;"
    "addq %%rcx,  %%r8 ;"  "movq  %%r8, 32(%0) ;"
  :
  : "r" (c), "r" (a)
  : "memory", "cc", "%rax", "%rbx", "%rcx", "%rdx", "%r8", "%r9", "%r10", "%r11"
  );
}

static inline void fmul1(uint64_t *const c, uint64_t *const a, uint64_t ignored) {
  const uint64_t a24 = 121665;
  __asm__ __volatile__(
    "movq     %2, %%rdx ;"
    "mulx   (%1),  %%r8, %%r10 ;"
    "mulx  8(%1),  %%r9, %%r11 ;"  "addq %%r10,  %%r9 ;"
    "mulx 16(%1), %%r10, %%rax ;"  "adcq %%r11, %%r10 ;"
    "mulx 24(%1), %%r11, %%rcx ;"  "adcq %%rax, %%r11 ;"
    /***************************/  "adcq    $0, %%rcx ;"
    "movl   $38, %%edx ;" /* 2*c = 38 = 2^256 mod 2^255-19*/
    "imul %%rdx, %%rcx ;"
    "addq %%rcx,  %%r8 ;"
    "adcq    $0,  %%r9 ;"  "movq  %%r9,  8(%0) ;"
    "adcq    $0, %%r10 ;"  "movq %%r10, 16(%0) ;"
    "adcq    $0, %%r11 ;"  "movq %%r11, 24(%0) ;"
    "mov     $0, %%ecx ;"
    "cmovc %%edx, %%ecx ;"
    "addq %%rcx,  %%r8 ;"  "movq  %%r8,   (%0) ;"
  :
  : "r" (c), "r" (a), "r" (a24)
  : "memory", "cc", "%rax", "%rcx", "%rdx", "%r8", "%r9", "%r10", "%r11"
  );
}

static inline uint64_t add1(uint64_t *const c, const uint64_t* a, uint64_t x) {
  uint64_t carry;
  __asm__ __volatile__ (
    /* Add either 19 or 38 to c */
    "addq    %4,   %0 ;"
    "adcq    $0,   %1 ;"
    "adcq    $0,   %2 ;"
    "adcq    $0,   %3 ;"
    "adcq    $0,   %5 ;"

    : "+r"(c[0]), "+r"(c[1]), "+r"(c[2]), "+r"(c[3]), "+r" (x), "=r"(carry)
    :
    : "memory", "cc"
  );
  return carry;
}

static inline
void fmul(uint64_t* dst, uint64_t* in_a, uint64_t* in_b) {
  uint64_t tmp[8] = {0};
  mul(tmp,in_a,in_b);
  carry_wide(dst,tmp);
}


static inline
void fmul2(uint64_t* dst, uint64_t* in_a, uint64_t* in_b) {
  uint64_t tmp[16] = {0};
  mul2(tmp,in_a,in_b);
  carry_wide2(dst,tmp);
}

static inline
void fsqr(uint64_t* dst, uint64_t* in_a) {
  uint64_t tmp[8] = {0};
  sqr(tmp,in_a);
  carry_wide(dst,tmp);
}

static inline
void fsqr2(uint64_t* dst, uint64_t* in_a) {
  uint64_t tmp[16] = {0};
  sqr2(tmp,in_a);
  carry_wide2(dst,tmp);
}

