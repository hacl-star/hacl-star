/**
 * Copyright (c) 2017, Armando Faz <armfazh@ic.unicamp.br>. All rights reserved.
 * Institute of Computing.
 * University of Campinas, Brazil.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 *  * Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *  * Redistributions in binary form must reproduce the above
 *    copyright notice, this list of conditions and the following
 *    disclaimer in the documentation and/or other materials provided
 *    with the distribution.
 *  * Neither the name of University of Campinas nor the names of its
 *    contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include "fp448_x64.h"

void mul_448x448_integer_x64(uint64_t *c, uint64_t *a, uint64_t *b) {
#ifdef __BMI2__
#ifdef __ADX__
  __asm__ __volatile__(
  /*  C[0] = A[0] x B  */
  "movq  0(%1), %%rdx;"
  "mulx  0(%2), %%rax,  %%r8;"  "movq %%rax,  (%0);"  "clc;"
  "mulx  8(%2), %%rax,  %%r9;"  "adcx %%rax,  %%r8;"
  "mulx 16(%2), %%rax, %%r10;"  "adcx %%rax,  %%r9;"
  "mulx 24(%2), %%rax, %%r11;"  "adcx %%rax, %%r10;"
  "mulx 32(%2), %%rax, %%r12;"  "adcx %%rax, %%r11;"
  "mulx 40(%2), %%rax, %%r13;"  "adcx %%rax, %%r12;"
  "mulx 48(%2), %%rax, %%r14;"  "adcx %%rax, %%r13;"  "movq $0, %%rax;"
  /**************************/  "adcx %%rax, %%r14;"

  /*  C[i] += A[i] x B  */
  ".macro MULACC_mulxadx I, R0, R1, R2, R3, R4, R5, R6;"
  "xorl   %%eax, %%eax;"
  "movq \\I(%1), %%rdx;"
  "mulx  0(%2), %%rax, %%rcx;"  "adox %%rax, \\R0;"  "adox %%rcx, \\R1;"  "movq \\R0, \\I(%0);"
  "mulx  8(%2), %%rax, %%rcx;"  "adcx %%rax, \\R1;"  "adox %%rcx, \\R2;"
  "mulx 16(%2), %%rax, %%rcx;"  "adcx %%rax, \\R2;"  "adox %%rcx, \\R3;"
  "mulx 24(%2), %%rax, %%rcx;"  "adcx %%rax, \\R3;"  "adox %%rcx, \\R4;"
  "mulx 32(%2), %%rax, %%rcx;"  "adcx %%rax, \\R4;"  "adox %%rcx, \\R5;"
  "mulx 40(%2), %%rax, %%rcx;"  "adcx %%rax, \\R5;"  "adox %%rcx, \\R6;"  "movq $0,  \\R0;"
  "mulx 48(%2), %%rax, %%rcx;"  "adcx %%rax, \\R6;"  "adox %%rcx, \\R0;"  "movq $0, %%rax;"
  /**************************/  "adcx %%rax, \\R0;"
  ".endm;"

  "MULACC_mulxadx  8,  %%r8,  %%r9, %%r10, %%r11, %%r12, %%r13, %%r14;"
  "MULACC_mulxadx 16,  %%r9, %%r10, %%r11, %%r12, %%r13, %%r14,  %%r8;"
  "MULACC_mulxadx 24, %%r10, %%r11, %%r12, %%r13, %%r14,  %%r8,  %%r9;"
  "MULACC_mulxadx 32, %%r11, %%r12, %%r13, %%r14,  %%r8,  %%r9, %%r10;"
  "MULACC_mulxadx 40, %%r12, %%r13, %%r14,  %%r8,  %%r9, %%r10, %%r11;"
  "MULACC_mulxadx 48, %%r13, %%r14,  %%r8,  %%r9, %%r10, %%r11, %%r12;"
  ".purgem MULACC_mulxadx;"

  "movq %%r14,  56(%0);"
  "movq  %%r8,  64(%0);"
  "movq  %%r9,  72(%0);"
  "movq %%r10,  80(%0);"
  "movq %%r11,  88(%0);"
  "movq %%r12,  96(%0);"
  "movq %%r13, 104(%0);"
  :
  : "r" (c), "r" (a), "r" (b)
  : "memory", "cc", "%rax", "%rcx", "%rdx", "%r8",
  "%r9", "%r10", "%r11", "%r12", "%r13", "%r14"
  );
#else
  __asm__ __volatile__(
  "movq  0(%1), %%rdx;"
  "mulx  0(%2),  %%r8,  %%r9;"  /******************/  "movq  %%r8,  0(%0);"
  "mulx  8(%2), %%rax, %%r10;"  "addq %%rax,  %%r9;"  "movq  %%r9,  8(%0);"
  "mulx 16(%2), %%rax, %%r11;"  "adcq %%rax, %%r10;"  "movq %%r10, 16(%0);"
  "mulx 24(%2), %%rax,  %%r8;"  "adcq %%rax, %%r11;"  "movq %%r11, 24(%0);"
  "mulx 32(%2), %%rax,  %%r9;"  "adcq %%rax,  %%r8;"  "movq  %%r8, 32(%0);"
  "mulx 40(%2), %%rax, %%rcx;"  "adcq %%rax,  %%r9;"  "movq  %%r9, 40(%0);"
  "mulx 48(%2), %%rax, %%rdx;"  "adcq %%rax, %%rcx;"  "movq %%rcx, 48(%0);"
  /**************************/  "adcq    $0, %%rdx;"  "movq %%rdx, 56(%0);"

  ".macro MULACC_mulx I;"
  "movq \\I(%1), %%rdx;"
  "mulx  0(%2),  %%r8,  %%r9;"
  "mulx  8(%2), %%rax, %%r10;"  "addq %%rax,  %%r9;"
  "mulx 16(%2), %%rax, %%r11;"  "adcq %%rax, %%r10;"
  "mulx 24(%2), %%rax, %%r12;"  "adcq %%rax, %%r11;"
  "mulx 32(%2), %%rax, %%r13;"  "adcq %%rax, %%r12;"
  "mulx 40(%2), %%rax, %%rcx;"  "adcq %%rax, %%r13;"
  "mulx 48(%2), %%rax, %%rdx;"  "adcq %%rax, %%rcx;"
  /**************************/  "adcq    $0, %%rdx;"
  "addq (\\I+ 0)(%0),  %%r8;"  "movq  %%r8, (\\I+ 0)(%0);"
  "adcq (\\I+ 8)(%0),  %%r9;"  "movq  %%r9, (\\I+ 8)(%0);"
  "adcq (\\I+16)(%0), %%r10;"  "movq %%r10, (\\I+16)(%0);"
  "adcq (\\I+24)(%0), %%r11;"  "movq %%r11, (\\I+24)(%0);"
  "adcq (\\I+32)(%0), %%r12;"  "movq %%r12, (\\I+32)(%0);"
  "adcq (\\I+40)(%0), %%r13;"  "movq %%r13, (\\I+40)(%0);"
  "adcq (\\I+48)(%0), %%rcx;"  "movq %%rcx, (\\I+48)(%0);"
  "adcq           $0, %%rdx;"  "movq %%rdx, (\\I+56)(%0);"
  ".endm;"

  "MULACC_mulx  8;"
  "MULACC_mulx 16;"
  "MULACC_mulx 24;"
  "MULACC_mulx 32;"
  "MULACC_mulx 40;"
  "MULACC_mulx 48;"
  ".purgem MULACC_mulx;"
  :
  : "r" (c), "r" (a), "r" (b)
  : "memory", "cc", "%rax", "%rcx", "%rdx", "%r8",
  "%r9", "%r10", "%r11", "%r12", "%r13"
  );
#endif
#else    /* Without BMI2 */
  __asm__ __volatile__(
  "movq   (%1), %%rcx;"
  "movq   (%2), %%rax;"  "mulq %%rcx;"  "movq %%rax,  (%0);"  /***************/  "movq %%rdx,  %%r8;"
  "movq  8(%2), %%rax;"  "mulq %%rcx;"  "addq %%rax,  %%r8;"  "adcq $0, %%rdx;"  "movq %%rdx,  %%r9;"  "movq  %%r8,  8(%0);"
  "movq 16(%2), %%rax;"  "mulq %%rcx;"  "addq %%rax,  %%r9;"  "adcq $0, %%rdx;"  "movq %%rdx, %%r10;"  "movq  %%r9, 16(%0);"
  "movq 24(%2), %%rax;"  "mulq %%rcx;"  "addq %%rax, %%r10;"  "adcq $0, %%rdx;"  "movq %%rdx, %%r11;"  "movq %%r10, 24(%0);"
  "movq 32(%2), %%rax;"  "mulq %%rcx;"  "addq %%rax, %%r11;"  "adcq $0, %%rdx;"  "movq %%rdx, %%r12;"  "movq %%r11, 32(%0);"
  "movq 40(%2), %%rax;"  "mulq %%rcx;"  "addq %%rax, %%r12;"  "adcq $0, %%rdx;"  "movq %%rdx, %%r13;"  "movq %%r12, 40(%0);"
  "movq 48(%2), %%rax;"  "mulq %%rcx;"  "addq %%rax, %%r13;"  "adcq $0, %%rdx;"  "movq %%rdx, 56(%0);" "movq %%r13, 48(%0);"

  ".macro MULACC I;"
  "movq \\I(%1), %%rcx;"
  "movq   (%2), %%rax;"  "mulq %%rcx;"  "movq %%rax,  %%r8;"  /***************/  "movq %%rdx,  %%r9;"
  "movq  8(%2), %%rax;"  "mulq %%rcx;"  "addq %%rax,  %%r9;"  "adcq $0, %%rdx;"  "movq %%rdx, %%r10;"
  "movq 16(%2), %%rax;"  "mulq %%rcx;"  "addq %%rax, %%r10;"  "adcq $0, %%rdx;"  "movq %%rdx, %%r11;"
  "movq 24(%2), %%rax;"  "mulq %%rcx;"  "addq %%rax, %%r11;"  "adcq $0, %%rdx;"  "movq %%rdx, %%r12;"
  "movq 32(%2), %%rax;"  "mulq %%rcx;"  "addq %%rax, %%r12;"  "adcq $0, %%rdx;"  "movq %%rdx, %%r13;"
  "movq 40(%2), %%rax;"  "mulq %%rcx;"  "addq %%rax, %%r13;"  "adcq $0, %%rdx;"  "movq %%rdx, %%r14;"
  "movq 48(%2), %%rax;"  "mulq %%rcx;"  "addq %%rax, %%r14;"  "adcq $0, %%rdx;"

  "addq (\\I+ 0)(%0),  %%r8;"  "movq  %%r8, (\\I+ 0)(%0);"
  "adcq (\\I+ 8)(%0),  %%r9;"  "movq  %%r9, (\\I+ 8)(%0);"
  "adcq (\\I+16)(%0), %%r10;"  "movq %%r10, (\\I+16)(%0);"
  "adcq (\\I+24)(%0), %%r11;"  "movq %%r11, (\\I+24)(%0);"
  "adcq (\\I+32)(%0), %%r12;"  "movq %%r12, (\\I+32)(%0);"
  "adcq (\\I+40)(%0), %%r13;"  "movq %%r13, (\\I+40)(%0);"
  "adcq (\\I+48)(%0), %%r14;"  "movq %%r14, (\\I+48)(%0);"
  "adcq           $0, %%rdx;"  "movq %%rdx, (\\I+56)(%0);"
  ".endm;"

  "MULACC  8;"
  "MULACC 16;"
  "MULACC 24;"
  "MULACC 32;"
  "MULACC 40;"
  "MULACC 48;"
  ".purgem MULACC;"
  :
  : "r" (c), "r" (a), "r" (b)
  : "memory", "cc", "%rax", "%rcx", "%rdx", "%r8", "%r9",
  "%r10", "%r11", "%r12", "%r13", "%r14"
  );
#endif
}

void sqr_448x448_integer_x64(uint64_t *c, uint64_t *a) {
#ifdef __BMI2__
#ifdef __ADX__
  __asm__ __volatile__(
    "movq   (%1), %%rdx        ; " /* A[0]    */
    "mulx  %%rdx, %%rax, %%rbx ; " /* A[0]^2  */
    "movq  8(%1), %%rdx        ; " /* A[1]    */
    "mulx  %%rdx,  %%r8, %%r9  ; " /* A[1]^2  */
    "movq  %%rax,   (%0) ;"
    "movq  %%rbx,  8(%0) ;"
    "movq   %%r8, 16(%0) ;"
    "movq   %%r9, 24(%0) ;"
    "movq 16(%1), %%rdx        ; " /* A[2]    */
    "mulx  %%rdx, %%r10, %%r11 ; " /* A[2]^2  */
    "movq 24(%1), %%rdx        ; " /* A[3]    */
    "mulx  %%rdx, %%r12, %%r13 ; " /* A[3]^2  */
    "movq  %%r10, 32(%0) ;"
    "movq  %%r11, 40(%0) ;"
    "movq  %%r12, 48(%0) ;"
    "movq  %%r13, 56(%0) ;"
    "movq 32(%1), %%rdx        ; " /* A[4]    */
    "mulx  %%rdx, %%rax, %%rbx ; " /* A[4]^2  */
    "movq 40(%1), %%rdx        ; " /* A[5]    */
    "mulx  %%rdx,  %%r8, %%r9  ; " /* A[5]^2  */
    "movq  %%rax, 64(%0) ;"
    "movq  %%rbx, 72(%0) ;"
    "movq   %%r8, 80(%0) ;"
    "movq   %%r9, 88(%0) ;"
    "movq 48(%1), %%rdx        ; " /* A[6]    */
    "mulx  %%rdx, %%r10, %%r11 ; " /* A[6]^2  */
    "movq  %%r10, 96(%0) ;"
    "movq  %%r11,104(%0) ;"

    "movq   (%1), %%rdx      ; " /* A[0]      */
    "mulx  8(%1), %%r8, %%r9 ; " /* A[0]A[1]  */  "xorl %%r10d,%%r10d;"  "adox  %%r8,  %%r8 ;"
    "mulx 16(%1),%%r10,%%r11 ; " /* A[0]A[2]  */  "adcx %%r10,  %%r9 ;"  "adox  %%r9,  %%r9 ;"
    "mulx 24(%1),%%r12,%%r13 ; " /* A[0]A[3]  */  "adcx %%r12, %%r11 ;"  "adox %%r11, %%r11 ;"
    "mulx 32(%1),%%r14,%%rax ; " /* A[0]A[4]  */  "adcx %%r14, %%r13 ;"  "adox %%r13, %%r13 ;"
    "mulx 40(%1),%%r10,%%rbx ; " /* A[0]A[5]  */  "adcx %%r10, %%rax ;"  "adox %%rax, %%rax ;"
    "mulx 48(%1),%%r12,%%rcx ; " /* A[0]A[6]  */  "adcx %%r12, %%rbx ;"  "adox %%rbx, %%rbx ;"
    "movq 24(%1),%%rdx       ; " /* A[3]      */  "movq    $0, %%r12 ;"  "movq    $0, %%r10 ;"
    "mulx 32(%1),%%r14,%%rdx ; " /* A[3]A[4]  */  "adcx %%r14, %%rcx ;"  "adox %%rcx, %%rcx ;"
    /******************************************/  "adcx %%r12, %%rdx ;"  "adox %%rdx, %%rdx ;"
    /*****************************************************************/  "adox %%r12, %%r10 ;"

    "addq  8(%0), %%r8;" "movq  %%r8, 8(%0);"
    "adcq 16(%0), %%r9;" "movq  %%r9,16(%0);"
    "adcq 24(%0),%%r11;" "movq %%r11,24(%0);"
    "adcq 32(%0),%%r13;" "movq %%r13,32(%0);"
    "adcq 40(%0),%%rax;" "movq %%rax,40(%0);"
    "adcq 48(%0),%%rbx;" "movq %%rbx,48(%0);"
    "adcq 56(%0),%%rcx;" "movq %%rcx,56(%0);"
    "adcq 64(%0),%%rdx;" "movq %%rdx,64(%0);"
    "adcq 72(%0),%%r10;" "movq %%r10,72(%0);"

    "movq  8(%1),%%rdx        ; " /* A[1]     */
    "mulx 16(%1), %%r8,  %%r9 ; " /* A[1]A[2] */  "xorl %%r10d,%%r10d;"  "adox  %%r8,  %%r8 ;"
    "mulx 24(%1),%%r10, %%r11 ; " /* A[1]A[3] */  "adcx %%r10,  %%r9 ;"  "adox  %%r9,  %%r9 ;"
    "mulx 32(%1),%%r12, %%r13 ; " /* A[1]A[4] */  "adcx %%r12, %%r11 ;"  "adox %%r11, %%r11 ;"
    "mulx 40(%1),%%r14, %%rax ; " /* A[1]A[5] */  "adcx %%r14, %%r13 ;"  "adox %%r13, %%r13 ;"
    "mulx 48(%1),%%r10, %%rbx ; " /* A[1]A[6] */  "adcx %%r10, %%rax ;"  "adox %%rax, %%rax ;"
    "movq 40(%1),%%rdx        ; " /* A[5]     */
    "mulx 24(%1),%%r12, %%rcx ; " /* A[5]A[3] */  "adcx %%r12, %%rbx ;"  "adox %%rbx, %%rbx ;"
    "mulx 32(%1),%%r14, %%rdx ; " /* A[5]A[4] */  "adcx %%r14, %%rcx ;"  "adox %%rcx, %%rcx ;"
    /******************************************/  "movq    $0, %%r12 ;"  "movq    $0, %%r10 ;"
    /******************************************/  "adcx %%r12, %%rdx ;"  "adox %%rdx, %%rdx ;"
    /*****************************************************************/  "adox %%r12, %%r10 ;"

    "addq 24(%0), %%r8;" "movq  %%r8,24(%0);"
    "adcq 32(%0), %%r9;" "movq  %%r9,32(%0);"
    "adcq 40(%0),%%r11;" "movq %%r11,40(%0);"
    "adcq 48(%0),%%r13;" "movq %%r13,48(%0);"
    "adcq 56(%0),%%rax;" "movq %%rax,56(%0);"
    "adcq 64(%0),%%rbx;" "movq %%rbx,64(%0);"
    "adcq 72(%0),%%rcx;" "movq %%rcx,72(%0);"
    "adcq 80(%0),%%rdx;" "movq %%rdx,80(%0);"
    "adcq 88(%0),%%r10;" "movq %%r10,88(%0);"

    "movq 16(%1), %%rdx        ; " /* A[2]     */
    "mulx 24(%1),  %%r8,  %%r9 ; " /* A[2]A[3] */  "xorl %%r10d,%%r10d;"  "adox  %%r8,  %%r8 ;"
    "mulx 32(%1), %%r10, %%r11 ; " /* A[2]A[4] */  "adcx %%r10,  %%r9 ;"  "adox  %%r9,  %%r9 ;"
    "mulx 40(%1), %%r12, %%r13 ; " /* A[2]A[5] */  "adcx %%r12, %%r11 ;"  "adox %%r11, %%r11 ;"
    "mulx 48(%1), %%r14, %%rax ; " /* A[2]A[6] */  "adcx %%r14, %%r13 ;"  "adox %%r13, %%r13 ;"
    "movq 48(%1), %%rdx        ; " /* A[6]     */
    "mulx 24(%1), %%r10, %%rbx ; " /* A[6]A[3] */  "adcx %%r10, %%rax ;"  "adox %%rax, %%rax ;"
    "mulx 32(%1), %%r12, %%rcx ; " /* A[6]A[4] */  "adcx %%r12, %%rbx ;"  "adox %%rbx, %%rbx ;"
    "mulx 40(%1), %%r14, %%rdx ; " /* A[6]A[5] */  "adcx %%r14, %%rcx ;"  "adox %%rcx, %%rcx ;"
    /*******************************************/  "movq    $0, %%r12 ;"  "movq    $0, %%r10 ;"
    /*******************************************/  "adcx %%r12, %%rdx ;"  "adox %%rdx, %%rdx ;"
    /******************************************************************/  "adox %%r12, %%r10 ;"

    "addq  40(%0), %%r8;" "movq  %%r8, 40(%0);"
    "adcq  48(%0), %%r9;" "movq  %%r9, 48(%0);"
    "adcq  56(%0),%%r11;" "movq %%r11, 56(%0);"
    "adcq  64(%0),%%r13;" "movq %%r13, 64(%0);"
    "adcq  72(%0),%%rax;" "movq %%rax, 72(%0);"
    "adcq  80(%0),%%rbx;" "movq %%rbx, 80(%0);"
    "adcq  88(%0),%%rcx;" "movq %%rcx, 88(%0);"
    "adcq  96(%0),%%rdx;" "movq %%rdx, 96(%0);"
    "adcq 104(%0),%%r10;" "movq %%r10,104(%0);"
    :
    : "r"  (c), "r" (a)
    : "memory", "cc", "%rax", "%rbx", "%rcx", "%rdx",
      "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14"
    );
#else
  __asm__ __volatile__(
  "movq   (%1), %%rdx        ; " /* A[0]    */
  "mulx  %%rdx, %%rax, %%rbx ; " /* A[0]^2  */
  "movq  8(%1), %%rdx        ; " /* A[1]    */
  "mulx  %%rdx,  %%r8, %%r9  ; " /* A[1]^2  */
  "movq  %%rax,   (%0) ;"
  "movq  %%rbx,  8(%0) ;"
  "movq   %%r8, 16(%0) ;"
  "movq   %%r9, 24(%0) ;"
  "movq 16(%1), %%rdx        ; " /* A[2]    */
  "mulx  %%rdx, %%r10, %%r11 ; " /* A[2]^2  */
  "movq 24(%1), %%rdx        ; " /* A[3]    */
  "mulx  %%rdx, %%r12, %%r13 ; " /* A[3]^2  */
  "movq  %%r10, 32(%0) ;"
  "movq  %%r11, 40(%0) ;"
  "movq  %%r12, 48(%0) ;"
  "movq  %%r13, 56(%0) ;"
  "movq 32(%1), %%rdx        ; " /* A[4]    */
  "mulx  %%rdx, %%rax, %%rbx ; " /* A[4]^2  */
  "movq 40(%1), %%rdx        ; " /* A[5]    */
  "mulx  %%rdx,  %%r8, %%r9  ; " /* A[5]^2  */
  "movq  %%rax, 64(%0) ;"
  "movq  %%rbx, 72(%0) ;"
  "movq   %%r8, 80(%0) ;"
  "movq   %%r9, 88(%0) ;"
  "movq 48(%1), %%rdx        ; " /* A[6]    */
  "mulx  %%rdx, %%r10, %%r11 ; " /* A[6]^2  */
  "movq  %%r10, 96(%0) ;"
  "movq  %%r11,104(%0) ;"

  "movq   (%1), %%rdx        ; " /* A[0]     */
  "mulx  8(%1),  %%r8,  %%r9 ; " /* A[0]A[1] */
  "mulx 16(%1), %%r10, %%r11 ; " /* A[0]A[2] */   "addq %%r10,  %%r9 ;"
  "mulx 24(%1), %%r12, %%r13 ; " /* A[0]A[3] */   "adcq %%r12, %%r11 ;"
  "mulx 32(%1), %%r14, %%rax ; " /* A[0]A[4] */   "adcq %%r14, %%r13 ;"
  "mulx 40(%1), %%r10, %%rbx ; " /* A[0]A[5] */   "adcq %%r10, %%rax ;"
  "mulx 48(%1), %%r12, %%rcx ; " /* A[0]A[6] */   "adcq %%r12, %%rbx ;"
  "movq 24(%1), %%rdx        ; " /* A[3]     */
  "mulx 32(%1), %%r14, %%rdx ; " /* A[3]A[4] */   "adcq %%r14, %%rcx ;"
  /*******************************************/   "adcq    $0, %%rdx ;"

  "xorq  %%r10, %%r10  ;"
  "shldq $1,%%rdx,%%r10;"
  "shldq $1,%%rcx,%%rdx;"
  "shldq $1,%%rbx,%%rcx;"
  "shldq $1,%%rax,%%rbx;"
  "shldq $1,%%r13,%%rax;"
  "shldq $1,%%r11,%%r13;"
  "shldq $1, %%r9,%%r11;"
  "shldq $1, %%r8, %%r9;"
  "shlq  $1, %%r8      ;"

  "addq  8(%0), %%r8;"  "movq  %%r8, 8(%0);"
  "adcq 16(%0), %%r9;"  "movq  %%r9,16(%0);"
  "adcq 24(%0),%%r11;"  "movq %%r11,24(%0);"
  "adcq 32(%0),%%r13;"  "movq %%r13,32(%0);"
  "adcq 40(%0),%%rax;"  "movq %%rax,40(%0);"
  "adcq 48(%0),%%rbx;"  "movq %%rbx,48(%0);"
  "adcq 56(%0),%%rcx;"  "movq %%rcx,56(%0);"
  "adcq 64(%0),%%rdx;"  "movq %%rdx,64(%0);"
  "adcq 72(%0),%%r10;"  "movq %%r10,72(%0);"

  "movq  8(%1), %%rdx        ; " /* A[1]     */
  "mulx 16(%1),  %%r8,  %%r9 ; " /* A[1]A[2] */
  "mulx 24(%1), %%r10, %%r11 ; " /* A[1]A[3] */   "addq %%r10,  %%r9 ;"
  "mulx 32(%1), %%r12, %%r13 ; " /* A[1]A[4] */   "adcq %%r12, %%r11 ;"
  "mulx 40(%1), %%r14, %%rax ; " /* A[1]A[5] */   "adcq %%r14, %%r13 ;"
  "mulx 48(%1), %%r10, %%rbx ; " /* A[1]A[6] */   "adcq %%r10, %%rax ;"
  "movq 40(%1), %%rdx        ; " /* A[5]     */
  "mulx 24(%1), %%r12, %%rcx ; " /* A[5]A[3] */   "adcq %%r12, %%rbx ;"
  "mulx 32(%1), %%r14, %%rdx ; " /* A[5]A[4] */   "adcq %%r14, %%rcx ;"
  /*******************************************/   "adcq    $0, %%rdx ;"

  "xorq  %%r10, %%r10  ;"
  "shldq $1,%%rdx,%%r10;"
  "shldq $1,%%rcx,%%rdx;"
  "shldq $1,%%rbx,%%rcx;"
  "shldq $1,%%rax,%%rbx;"
  "shldq $1,%%r13,%%rax;"
  "shldq $1,%%r11,%%r13;"
  "shldq $1, %%r9,%%r11;"
  "shldq $1, %%r8, %%r9;"
  "shlq  $1, %%r8      ;"

  "addq 24(%0), %%r8;"  "movq  %%r8,24(%0);"
  "adcq 32(%0), %%r9;"  "movq  %%r9,32(%0);"
  "adcq 40(%0),%%r11;"  "movq %%r11,40(%0);"
  "adcq 48(%0),%%r13;"  "movq %%r13,48(%0);"
  "adcq 56(%0),%%rax;"  "movq %%rax,56(%0);"
  "adcq 64(%0),%%rbx;"  "movq %%rbx,64(%0);"
  "adcq 72(%0),%%rcx;"  "movq %%rcx,72(%0);"
  "adcq 80(%0),%%rdx;"  "movq %%rdx,80(%0);"
  "adcq 88(%0),%%r10;"  "movq %%r10,88(%0);"

  "movq 16(%1), %%rdx        ; " /* A[2]     */
  "mulx 24(%1),  %%r8,  %%r9 ; " /* A[2]A[3] */
  "mulx 32(%1), %%r10, %%r11 ; " /* A[2]A[4] */  "addq %%r10,  %%r9 ;"
  "mulx 40(%1), %%r12, %%r13 ; " /* A[2]A[5] */  "adcq %%r12, %%r11 ;"
  "mulx 48(%1), %%r14, %%rax ; " /* A[2]A[6] */  "adcq %%r14, %%r13 ;"
  "movq 48(%1), %%rdx        ; " /* A[6]     */
  "mulx 24(%1), %%r10, %%rbx ; " /* A[6]A[3] */  "adcq %%r10, %%rax ;"
  "mulx 32(%1), %%r12, %%rcx ; " /* A[6]A[4] */  "adcq %%r12, %%rbx ;"
  "mulx 40(%1), %%r14, %%rdx ; " /* A[6]A[5] */  "adcq %%r14, %%rcx ;"
  /*******************************************/  "adcq    $0, %%rdx ;"

  "xorq  %%r10, %%r10  ;"
  "shldq $1,%%rdx,%%r10;"
  "shldq $1,%%rcx,%%rdx;"
  "shldq $1,%%rbx,%%rcx;"
  "shldq $1,%%rax,%%rbx;"
  "shldq $1,%%r13,%%rax;"
  "shldq $1,%%r11,%%r13;"
  "shldq $1, %%r9,%%r11;"
  "shldq $1, %%r8, %%r9;"
  "shlq  $1, %%r8      ;"

  "addq  40(%0), %%r8;"   "movq  %%r8, 40(%0);"
  "adcq  48(%0), %%r9;"   "movq  %%r9, 48(%0);"
  "adcq  56(%0),%%r11;"   "movq %%r11, 56(%0);"
  "adcq  64(%0),%%r13;"   "movq %%r13, 64(%0);"
  "adcq  72(%0),%%rax;"   "movq %%rax, 72(%0);"
  "adcq  80(%0),%%rbx;"   "movq %%rbx, 80(%0);"
  "adcq  88(%0),%%rcx;"   "movq %%rcx, 88(%0);"
  "adcq  96(%0),%%rdx;"   "movq %%rdx, 96(%0);"
  "adcq 104(%0),%%r10;"   "movq %%r10,104(%0);"
  :
  : "r"  (c), "r" (a)
  : "memory", "cc", "%rax", "%rbx", "%rcx", "%rdx", "%r8",
  "%r9", "%r10", "%r11", "%r12", "%r13", "%r14"
  );
#endif
#else    /* Without BMI2 */
  /**
  * TODO: Multiplications using MULQ instruction.
  **/
#endif
}

void red_EltFp448_1w_x64(uint64_t *c, uint64_t *a) {
#if __ADX__
  __asm__ __volatile__ (
    /* [c13,c12,c11,c10] mod p  */
    "movq  80(%1),  %%r8 ;"  "movq  %%r8, %%rax ;"
    "movq  88(%1),  %%r9 ;"  "movq  %%r9, %%rbx ;"
    "movq  96(%1), %%r10 ;"  "movq %%r10, %%rcx ;"
    "movq 104(%1), %%r11 ;"  "movq %%r11, %%rdx ;"
    "shrq $32, %%r8 ;"
    "shlq $32, %%r8 ;"
    "movl  $0, 84(%1) ;"

    "shrdq $32, %%rbx, %%rax ;"
    "shrdq $32, %%rcx, %%rbx ;"
    "shrdq $32, %%rdx, %%rcx ;"
    "shrq  $32, %%rdx ;"

    "clc ;"
    "adcx 24(%1),  %%r8 ;"  "movq   %%r8, 24(%0) ;"
    "adcx 32(%1),  %%r9 ;"  "movq   %%r9, 32(%0) ;"
    "adcx 40(%1), %%r10 ;"  "movq  %%r10, 40(%0) ;"
    "adcx 48(%1), %%r11 ;"  "movq  %%r11, 48(%0) ;"
    "adcx 56(%1), %%rax ;"  "movq  %%rax,   %%r8 ;"
    "adcx 64(%1), %%rbx ;"  "movq  %%rbx,   %%r9 ;"
    "adcx 72(%1), %%rcx ;"  "movq  %%rcx,  %%r10 ;"
    "adcx 80(%1), %%rdx ;"  "movq  %%rdx,  %%r11 ;"

    /* [c10,c9,c8,c7] mod p  */
    "xorq  %%r12, %%r12 ;"
    "shldq  $32, %%rdx, %%r12 ;"
    "shldq  $32, %%rcx, %%rdx ;"
    "shldq  $32, %%rbx, %%rcx ;"
    "shldq  $32, %%rax, %%rbx ;"
    "shlq   $32, %%rax ;"

    "addq %%r11, %%rax ;"
    "adcq $0, 32(%0) ;"

    "clc ;"
    "xorq  %%r11, %%r11 ;"
    "adcx   (%1),  %%r8 ;"
    "adcx  8(%1),  %%r9 ;"
    "adcx 16(%1), %%r10 ;"
    "adcx 24(%0), %%rax ;"
    "adcx 32(%0), %%rbx ;"
    "adcx 40(%0), %%rcx ;"
    "adcx 48(%0), %%rdx ;"
    "adcx  %%r11, %%r12 ;"

    /* [c7] mod p  */
    "addq %%r12,   %%r8 ;"
    "adcq    $0,   %%r9 ;"
    "shlq   $32,  %%r12 ;"
    "addq %%r12,  %%rax ;"
    "adcq    $0,  %%rbx ;"

    "movq  %%r8,   (%0) ;"
    "movq  %%r9,  8(%0) ;"
    "movq %%r10, 16(%0) ;"
    "movq %%rax, 24(%0) ;"
    "movq %%rbx, 32(%0) ;"
    "movq %%rcx, 40(%0) ;"
    "movq %%rdx, 48(%0) ;"
  :
  : "r" (c), "r" (a)
  : "memory", "cc", "%rax", "%rbx", "%rcx", "%rdx",
    "%r8", "%r9", "%r10", "%r11", "%r12"
  );
#else
  __asm__ __volatile__ (
  /* [c13,c12,c11,c10] mod p  */
  "movq  80(%1),  %%r8 ;"  "movq  %%r8, %%rax ;"
  "movq  88(%1),  %%r9 ;"  "movq  %%r9, %%rbx ;"
  "movq  96(%1), %%r10 ;"  "movq %%r10, %%rcx ;"
  "movq 104(%1), %%r11 ;"  "movq %%r11, %%rdx ;"
  "shrq $32, %%r8 ;"
  "shlq $32, %%r8 ;"
  "movl  $0, 84(%1) ;"

  "shrdq $32, %%rbx, %%rax ;"
  "shrdq $32, %%rcx, %%rbx ;"
  "shrdq $32, %%rdx, %%rcx ;"
  "shrq  $32, %%rdx ;"

  "addq 24(%1),  %%r8 ;"  "movq   %%r8, 24(%0) ;"
  "adcq 32(%1),  %%r9 ;"  "movq   %%r9, 32(%0) ;"
  "adcq 40(%1), %%r10 ;"  "movq  %%r10, 40(%0) ;"
  "adcq 48(%1), %%r11 ;"  "movq  %%r11, 48(%0) ;"
  "adcq 56(%1), %%rax ;"  "movq  %%rax,   %%r8 ;"
  "adcq 64(%1), %%rbx ;"  "movq  %%rbx,   %%r9 ;"
  "adcq 72(%1), %%rcx ;"  "movq  %%rcx,  %%r10 ;"
  "adcq 80(%1), %%rdx ;"  "movq  %%rdx,  %%r11 ;"

  /* [c10,c9,c8,c7] mod p  */
  "xorq  %%r12, %%r12 ;"
  "shldq  $32, %%rdx, %%r12 ;"
  "shldq  $32, %%rcx, %%rdx ;"
  "shldq  $32, %%rbx, %%rcx ;"
  "shldq  $32, %%rax, %%rbx ;"
  "shlq   $32, %%rax ;"

  "addq %%r11, %%rax ;"
  "adcq $0, 32(%0) ;"

  "addq   (%1),  %%r8 ;"
  "adcq  8(%1),  %%r9 ;"
  "adcq 16(%1), %%r10 ;"
  "adcq 24(%0), %%rax ;"
  "adcq 32(%0), %%rbx ;"
  "adcq 40(%0), %%rcx ;"
  "adcq 48(%0), %%rdx ;"
  "adcq     $0, %%r12 ;"

  /* [c7] mod p  */
  "addq %%r12,   %%r8 ;"
  "adcq    $0,   %%r9 ;"
  "shlq   $32,  %%r12 ;"
  "addq %%r12,  %%rax ;"
  "adcq    $0,  %%rbx ;"

  "movq  %%r8,   (%0) ;"
  "movq  %%r9,  8(%0) ;"
  "movq %%r10, 16(%0) ;"
  "movq %%rax, 24(%0) ;"
  "movq %%rbx, 32(%0) ;"
  "movq %%rcx, 40(%0) ;"
  "movq %%rdx, 48(%0) ;"
  :
  : "r" (c), "r" (a)
  : "memory", "cc", "%rax", "%rbx", "%rcx", "%rdx",
  "%r8", "%r9", "%r10", "%r11", "%r12"
  );
#endif
}

inline void add_EltFp448_1w_x64(uint64_t *c, uint64_t *a, uint64_t *b) {
#if __ADX__
  __asm__ __volatile__(
    "movq    (%2),  %%rax ;"
    "movq   8(%2),  %%rcx ;"
    "movq  16(%2),  %%rdx ;"
    "movq  24(%2),  %%r8  ;"
    "movq  32(%2),  %%r9  ;"
    "movq  40(%2),  %%r10 ;"
    "movq  48(%2),  %%r11 ;"
    "clc ;"
    "adcx    (%1),  %%rax ;"
    "adcx   8(%1),  %%rcx ;"
    "adcx  16(%1),  %%rdx ;"
    "adcx  24(%1),  %%r8  ;"
    "adcx  32(%1),  %%r9  ;"
    "adcx  40(%1),  %%r10 ;"
    "adcx  48(%1),  %%r11 ;"
    "setc    %%bl         ;"
    "movzx   %%bl,  %%rbx ;"
    "addq   %%rbx,  %%rax ;"
    "adcq   $0,     %%rcx ;"
    "shlq   $32,    %%rbx ;"
    "addq   %%rbx,  %%r8  ;"
    "adcq   $0,     %%r9  ;"
    "movq   %%rax,   (%0) ;"
    "movq   %%rcx,  8(%0) ;"
    "movq   %%rdx, 16(%0) ;"
    "movq   %%r8 , 24(%0) ;"
    "movq   %%r9 , 32(%0) ;"
    "movq   %%r10, 40(%0) ;"
    "movq   %%r11, 48(%0) ;"
  :
  : "r" (c), "r" (a), "r"  (b)
  : "memory", "cc", "%rax", "%rbx", "%rcx", "%rdx",
    "%r8", "%r9", "%r10", "%r11"
  );
#else
  __asm__ __volatile__(
  "movq    (%2),  %%rax ;"
  "movq   8(%2),  %%rcx ;"
  "movq  16(%2),  %%rdx ;"
  "movq  24(%2),  %%r8  ;"
  "movq  32(%2),  %%r9  ;"
  "movq  40(%2),  %%r10 ;"
  "movq  48(%2),  %%r11 ;"
  "addq    (%1),  %%rax ;"
  "adcq   8(%1),  %%rcx ;"
  "adcq  16(%1),  %%rdx ;"
  "adcq  24(%1),  %%r8  ;"
  "adcq  32(%1),  %%r9  ;"
  "adcq  40(%1),  %%r10 ;"
  "adcq  48(%1),  %%r11 ;"
  "setc    %%bl         ;"
  "movzx   %%bl,  %%rbx ;"
  "addq   %%rbx,  %%rax ;"
  "adcq   $0,     %%rcx ;"
  "shlq   $32,    %%rbx ;"
  "addq   %%rbx,  %%r8  ;"
  "adcq   $0,     %%r9  ;"
  "movq   %%rax,   (%0) ;"
  "movq   %%rcx,  8(%0) ;"
  "movq   %%rdx, 16(%0) ;"
  "movq   %%r8 , 24(%0) ;"
  "movq   %%r9 , 32(%0) ;"
  "movq   %%r10, 40(%0) ;"
  "movq   %%r11, 48(%0) ;"
  :
  : "r" (c), "r" (a), "r"  (b)
  : "memory", "cc", "%rax", "%rbx", "%rcx", "%rdx",
  "%r8", "%r9", "%r10", "%r11"
  );
#endif
}

inline void sub_EltFp448_1w_x64(uint64_t *c, uint64_t *a, uint64_t *b) {
  __asm__ __volatile__(
  "movq   (%1),  %%rax ;"
  "movq  8(%1),  %%rcx ;"
  "movq 16(%1),  %%rdx ;"
  "movq 24(%1),  %%r8  ;"
  "movq 32(%1),  %%r9  ;"
  "movq 40(%1),  %%r10 ;"
  "movq 48(%1),  %%r11 ;"
  "subq   (%2),  %%rax ;"
  "sbbq  8(%2),  %%rcx ;"
  "sbbq 16(%2),  %%rdx ;"
  "sbbq 24(%2),  %%r8  ;"
  "sbbq 32(%2),  %%r9  ;"
  "sbbq 40(%2),  %%r10 ;"
  "sbbq 48(%2),  %%r11 ;"
  "setc   %%bl         ;"
  "movzx  %%bl,  %%rbx ;"
  "subq  %%rbx,  %%rax ;"
  "sbbq  $0,     %%rcx ;"
  "shlq  $32,    %%rbx ;"
  "subq  %%rbx,  %%r8  ;"
  "sbbq  $0,     %%r9  ;"
  "movq  %%rax,   (%0) ;"
  "movq  %%rcx,  8(%0) ;"
  "movq  %%rdx, 16(%0) ;"
  "movq  %%r8 , 24(%0) ;"
  "movq  %%r9 , 32(%0) ;"
  "movq  %%r10, 40(%0) ;"
  "movq  %%r11, 48(%0) ;"
  :
  : "r" (c), "r" (a), "r"  (b)
  : "memory", "cc", "%rax", "%rbx", "%rcx", "%rdx",
  "%r8", "%r9", "%r10", "%r11"
  );
}

void mul_a24_EltFp448_1w_x64(uint64_t *c, uint64_t *a) {
#ifdef __BMI2__
  /**
  * a24 = (A+2)/4 = (156326+2)/4 = 39082
  **/
  const uint64_t a24 = 39082;
  __asm__ __volatile__(
  "movq %2, %%rdx ;"
  "mulx   (%1), %%rax,  %%r8 ;"  "movq %%rax,   (%0) ;"
  "mulx  8(%1), %%rcx,  %%r9 ;"  "movq %%rcx,  8(%0) ;"
  "mulx 16(%1), %%rax, %%r10 ;"  "movq %%rax, 16(%0) ;"
  "mulx 24(%1), %%rcx, %%r11 ;"  "movq %%rcx, 24(%0) ;"
  "mulx 32(%1), %%rax, %%r12 ;"  "movq %%rax, 32(%0) ;"
  "mulx 40(%1), %%rcx, %%r13 ;"  "movq %%rcx, 40(%0) ;"
  "mulx 48(%1), %%rax, %%rdx ;"  "movq %%rax, 48(%0) ;"

  "movq %%rdx,  %%rcx ;"
  "shlq   $32,  %%rcx ;"
  "addq %%rcx,  %%r10 ;"
  "adcq    $0,  %%r11 ;"

  "addq %%rdx,   (%0) ;"
  "adcq  %%r8,  8(%0) ;"
  "adcq  %%r9, 16(%0) ;"
  "adcq %%r10, 24(%0) ;"
  "adcq %%r11, 32(%0) ;"
  "adcq %%r12, 40(%0) ;"
  "adcq %%r13, 48(%0) ;"
  :
  : "r" (c), "r" (a), "r" (a24)
  : "cc", "%rax", "%rcx", "%rdx", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13"
  );
#else /* Without BMI2 */
  /**
* TODO: Multiplications using MULQ instruction.
**/
#endif
}

/**
 *
 * @param pC
 * @param pA
 * @param only_inverse
 */
void inv_EltFp448_1w_x64(uint64_t *__restrict pC, uint64_t *__restrict pA) {
#define sqrn_EltFp448_1w_x64(a, times)\
  counter = times;\
  while (counter-- > 0) {\
      sqr_EltFp448_1w_x64(a);\
  }

  EltFp448_1w_x64 x0, x1;
  uint64_t *T[4];
  unsigned int counter = 0;
  EltFp448_1w_Buffer_x64 buffer_1w;

  T[0] = x0;
  T[1] = pC;
  T[2] = x1;
  T[3] = pA;

  copy_EltFp448_1w_x64(T[1], T[3]);
  sqrn_EltFp448_1w_x64(T[1], 1);
  mul_EltFp448_1w_x64(T[1], T[1], T[3]);

  copy_EltFp448_1w_x64(T[0], T[1]);
  sqrn_EltFp448_1w_x64(T[0], 1);
  mul_EltFp448_1w_x64(T[0], T[0], T[3]);

  copy_EltFp448_1w_x64(T[1], T[0]);
  sqrn_EltFp448_1w_x64(T[1], 3);
  mul_EltFp448_1w_x64(T[1], T[1], T[0]);

  copy_EltFp448_1w_x64(T[2], T[1]);
  sqrn_EltFp448_1w_x64(T[2], 6);
  mul_EltFp448_1w_x64(T[2], T[2], T[1]);

  copy_EltFp448_1w_x64(T[1], T[2]);
  sqrn_EltFp448_1w_x64(T[1], 12);
  mul_EltFp448_1w_x64(T[1], T[1], T[2]);

  sqrn_EltFp448_1w_x64(T[1], 3);
  mul_EltFp448_1w_x64(T[1], T[1], T[0]);

  copy_EltFp448_1w_x64(T[2], T[1]);
  sqrn_EltFp448_1w_x64(T[2], 27);
  mul_EltFp448_1w_x64(T[2], T[2], T[1]);

  copy_EltFp448_1w_x64(T[1], T[2]);
  sqrn_EltFp448_1w_x64(T[1], 54);
  mul_EltFp448_1w_x64(T[1], T[1], T[2]);

  sqrn_EltFp448_1w_x64(T[1], 3);
  mul_EltFp448_1w_x64(T[1], T[1], T[0]);

  copy_EltFp448_1w_x64(T[2], T[1]);
  sqrn_EltFp448_1w_x64(T[2], 111);
  mul_EltFp448_1w_x64(T[2], T[2], T[1]);

  copy_EltFp448_1w_x64(T[1], T[2]);
  sqrn_EltFp448_1w_x64(T[1], 1);
  mul_EltFp448_1w_x64(T[1], T[1], T[3]);

  sqrn_EltFp448_1w_x64(T[1], 223);
  mul_EltFp448_1w_x64(T[1], T[1], T[2]);

  sqrn_EltFp448_1w_x64(T[1], 2);
  mul_EltFp448_1w_x64(T[1], T[1], T[3]);

#undef sqrn_EltFp448_1w_x64
}

void fred_EltFp448_1w_x64(uint64_t *c) {
  EltFp448_1w_x64 p = {
      0xffffffffffffffff,
      0xffffffffffffffff,
      0xffffffffffffffff,
      0xfffffffeffffffff,
      0xffffffffffffffff,
      0xffffffffffffffff,
      0xffffffffffffffff
  };
  sub_EltFp448_1w_x64(c, c, p);
}
