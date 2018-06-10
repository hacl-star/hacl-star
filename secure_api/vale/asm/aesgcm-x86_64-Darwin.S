.text
.global _aes_key_expansion
_aes_key_expansion:
  movdqu 0(%rdi), %xmm1
  mov %rsi, %rdx
  movdqu %xmm1, 0(%rdx)
  aeskeygenassist $1, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 16(%rdx)
  aeskeygenassist $2, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 32(%rdx)
  aeskeygenassist $4, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 48(%rdx)
  aeskeygenassist $8, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 64(%rdx)
  aeskeygenassist $16, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 80(%rdx)
  aeskeygenassist $32, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 96(%rdx)
  aeskeygenassist $64, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 112(%rdx)
  aeskeygenassist $128, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 128(%rdx)
  aeskeygenassist $27, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 144(%rdx)
  aeskeygenassist $54, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 160(%rdx)
  pxor %xmm1, %xmm1
  pxor %xmm2, %xmm2
  pxor %xmm3, %xmm3
  ret

.global _gcm_encrypt
_gcm_encrypt:
  mov %rdi, %r9
  push %r15
  push %r14
  push %r13
  push %r12
  push %rsi
  push %rdi
  push %rbp
  push %rbx
  movq 0(%r9), %r14
  movq 8(%r9), %r13
  movq 16(%r9), %rax
  movq 24(%r9), %r11
  movq 32(%r9), %r10
  movq 40(%r9), %r8
  movq 48(%r9), %rbx
  movq 56(%r9), %r15
  movdqu 0(%r10), %xmm7
  pxor %xmm0, %xmm0
  movdqu 0(%r8), %xmm2
  pxor %xmm2, %xmm0
  movdqu 16(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 32(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 48(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 64(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 80(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 96(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 112(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 128(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 144(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 160(%r8), %xmm2
  aesenclast %xmm2, %xmm0
  pxor %xmm2, %xmm2
  movdqu %xmm0, %xmm11
  mov $579005069656919567, %r12
  pinsrq $0, %r12, %xmm8
  mov $283686952306183, %r12
  pinsrq $1, %r12, %xmm8
  pshufb %xmm8, %xmm7
  mov $2, %r12
  pinsrd $0, %r12d, %xmm7
  pxor %xmm1, %xmm1
  cmp $0, %r11
  jbe L100
  mov %r11, %rcx
  shr $4, %rcx
  mov %rax, %r9
  cmp $0, %rcx
  je L102
  mov $0, %rdx
  jmp L105
.align 16
L104:
  movdqu 0(%r9), %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
  pshufb %xmm8, %xmm2
  movdqu %xmm1, %xmm5
  pclmulqdq $16, %xmm2, %xmm1
  movdqu %xmm1, %xmm3
  movdqu %xmm5, %xmm1
  pclmulqdq $1, %xmm2, %xmm1
  movdqu %xmm1, %xmm4
  movdqu %xmm5, %xmm1
  pclmulqdq $0, %xmm2, %xmm1
  pclmulqdq $17, %xmm2, %xmm5
  movdqu %xmm5, %xmm2
  movdqu %xmm1, %xmm5
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm4, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm1
  pshufd $79, %xmm1, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm4
  pshufd $79, %xmm4, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm5, %xmm1
  movdqu %xmm1, %xmm3
  psrld $31, %xmm3
  movdqu %xmm2, %xmm4
  psrld $31, %xmm4
  pslld $1, %xmm1
  pslld $1, %xmm2
  vpslldq $4, %xmm3, %xmm5
  vpslldq $4, %xmm4, %xmm4
  mov $0, %r12
  pinsrd $0, %r12d, %xmm3
  pshufd $3, %xmm3, %xmm3
  pxor %xmm4, %xmm3
  pxor %xmm5, %xmm1
  pxor %xmm3, %xmm2
  movdqu %xmm2, %xmm6
  pxor %xmm2, %xmm2
  mov $3774873600, %r12
  pinsrd $3, %r12d, %xmm2
  movdqu %xmm1, %xmm5
  pclmulqdq $16, %xmm2, %xmm1
  movdqu %xmm1, %xmm3
  movdqu %xmm5, %xmm1
  pclmulqdq $1, %xmm2, %xmm1
  movdqu %xmm1, %xmm4
  movdqu %xmm5, %xmm1
  pclmulqdq $0, %xmm2, %xmm1
  pclmulqdq $17, %xmm2, %xmm5
  movdqu %xmm5, %xmm2
  movdqu %xmm1, %xmm5
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm4, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm1
  pshufd $79, %xmm1, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm4
  pshufd $79, %xmm4, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm5, %xmm1
  movdqu %xmm1, %xmm3
  psrld $31, %xmm3
  movdqu %xmm2, %xmm4
  psrld $31, %xmm4
  pslld $1, %xmm1
  pslld $1, %xmm2
  vpslldq $4, %xmm3, %xmm5
  vpslldq $4, %xmm4, %xmm4
  mov $0, %r12
  pinsrd $0, %r12d, %xmm3
  pshufd $3, %xmm3, %xmm3
  pxor %xmm4, %xmm3
  pxor %xmm5, %xmm1
  pxor %xmm3, %xmm2
  movdqu %xmm2, %xmm5
  pxor %xmm2, %xmm2
  mov $3774873600, %r12
  pinsrd $3, %r12d, %xmm2
  pclmulqdq $17, %xmm2, %xmm1
  movdqu %xmm1, %xmm2
  psrld $31, %xmm2
  pslld $1, %xmm1
  vpslldq $4, %xmm2, %xmm2
  pxor %xmm2, %xmm1
  pxor %xmm5, %xmm1
  pxor %xmm6, %xmm1
  pshufb %xmm8, %xmm1
  add $1, %rdx
  add $16, %r9
.align 16
L105:
  cmp %rcx, %rdx
  jne L104
  jmp L103
L102:
L103:
  mov %r11, %rax
  and $15, %rax
  cmp $0, %rax
  jne L106
  jmp L107
L106:
  movdqu 0(%r9), %xmm2
  cmp $8, %rax
  jae L108
  mov $0, %rcx
  pinsrq $1, %rcx, %xmm2
  mov %rax, %rcx
  shl $3, %rcx
  mov $1, %rdx
  shl %cl, %rdx
  sub $1, %rdx
  pextrq $0, %xmm2, %rcx
  and %rdx, %rcx
  pinsrq $0, %rcx, %xmm2
  jmp L109
L108:
  mov %rax, %rcx
  sub $8, %rcx
  shl $3, %rcx
  mov $1, %rdx
  shl %cl, %rdx
  sub $1, %rdx
  pextrq $1, %xmm2, %rcx
  and %rdx, %rcx
  pinsrq $1, %rcx, %xmm2
L109:
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
  pshufb %xmm8, %xmm2
  movdqu %xmm1, %xmm5
  pclmulqdq $16, %xmm2, %xmm1
  movdqu %xmm1, %xmm3
  movdqu %xmm5, %xmm1
  pclmulqdq $1, %xmm2, %xmm1
  movdqu %xmm1, %xmm4
  movdqu %xmm5, %xmm1
  pclmulqdq $0, %xmm2, %xmm1
  pclmulqdq $17, %xmm2, %xmm5
  movdqu %xmm5, %xmm2
  movdqu %xmm1, %xmm5
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm4, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm1
  pshufd $79, %xmm1, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm4
  pshufd $79, %xmm4, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm5, %xmm1
  movdqu %xmm1, %xmm3
  psrld $31, %xmm3
  movdqu %xmm2, %xmm4
  psrld $31, %xmm4
  pslld $1, %xmm1
  pslld $1, %xmm2
  vpslldq $4, %xmm3, %xmm5
  vpslldq $4, %xmm4, %xmm4
  mov $0, %r12
  pinsrd $0, %r12d, %xmm3
  pshufd $3, %xmm3, %xmm3
  pxor %xmm4, %xmm3
  pxor %xmm5, %xmm1
  pxor %xmm3, %xmm2
  movdqu %xmm2, %xmm6
  pxor %xmm2, %xmm2
  mov $3774873600, %r12
  pinsrd $3, %r12d, %xmm2
  movdqu %xmm1, %xmm5
  pclmulqdq $16, %xmm2, %xmm1
  movdqu %xmm1, %xmm3
  movdqu %xmm5, %xmm1
  pclmulqdq $1, %xmm2, %xmm1
  movdqu %xmm1, %xmm4
  movdqu %xmm5, %xmm1
  pclmulqdq $0, %xmm2, %xmm1
  pclmulqdq $17, %xmm2, %xmm5
  movdqu %xmm5, %xmm2
  movdqu %xmm1, %xmm5
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm4, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm1
  pshufd $79, %xmm1, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm4
  pshufd $79, %xmm4, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm5, %xmm1
  movdqu %xmm1, %xmm3
  psrld $31, %xmm3
  movdqu %xmm2, %xmm4
  psrld $31, %xmm4
  pslld $1, %xmm1
  pslld $1, %xmm2
  vpslldq $4, %xmm3, %xmm5
  vpslldq $4, %xmm4, %xmm4
  mov $0, %r12
  pinsrd $0, %r12d, %xmm3
  pshufd $3, %xmm3, %xmm3
  pxor %xmm4, %xmm3
  pxor %xmm5, %xmm1
  pxor %xmm3, %xmm2
  movdqu %xmm2, %xmm5
  pxor %xmm2, %xmm2
  mov $3774873600, %r12
  pinsrd $3, %r12d, %xmm2
  pclmulqdq $17, %xmm2, %xmm1
  movdqu %xmm1, %xmm2
  psrld $31, %xmm2
  pslld $1, %xmm1
  vpslldq $4, %xmm2, %xmm2
  pxor %xmm2, %xmm1
  pxor %xmm5, %xmm1
  pxor %xmm6, %xmm1
  pshufb %xmm8, %xmm1
L107:
  jmp L101
L100:
L101:
  mov %r14, %rax
  mov %r13, %rcx
  cmp $0, %rcx
  jbe L110
  mov %rcx, %rsi
  and $15, %rsi
  shr $4, %rcx
  mov $0, %rdx
  mov %rax, %r9
  mov %rbx, %r10
  pxor %xmm10, %xmm10
  mov $1, %r12
  pinsrd $0, %r12d, %xmm10
  jmp L113
.align 16
L112:
  movdqu %xmm7, %xmm0
  pshufb %xmm8, %xmm0
  movdqu 0(%r8), %xmm2
  pxor %xmm2, %xmm0
  movdqu 16(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 32(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 48(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 64(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 80(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 96(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 112(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 128(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 144(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 160(%r8), %xmm2
  aesenclast %xmm2, %xmm0
  pxor %xmm2, %xmm2
  movdqu 0(%r9), %xmm2
  pxor %xmm0, %xmm2
  movdqu %xmm2, 0(%r10)
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
  pshufb %xmm8, %xmm2
  movdqu %xmm1, %xmm5
  pclmulqdq $16, %xmm2, %xmm1
  movdqu %xmm1, %xmm3
  movdqu %xmm5, %xmm1
  pclmulqdq $1, %xmm2, %xmm1
  movdqu %xmm1, %xmm4
  movdqu %xmm5, %xmm1
  pclmulqdq $0, %xmm2, %xmm1
  pclmulqdq $17, %xmm2, %xmm5
  movdqu %xmm5, %xmm2
  movdqu %xmm1, %xmm5
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm4, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm1
  pshufd $79, %xmm1, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm4
  pshufd $79, %xmm4, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm5, %xmm1
  movdqu %xmm1, %xmm3
  psrld $31, %xmm3
  movdqu %xmm2, %xmm4
  psrld $31, %xmm4
  pslld $1, %xmm1
  pslld $1, %xmm2
  vpslldq $4, %xmm3, %xmm5
  vpslldq $4, %xmm4, %xmm4
  mov $0, %r12
  pinsrd $0, %r12d, %xmm3
  pshufd $3, %xmm3, %xmm3
  pxor %xmm4, %xmm3
  pxor %xmm5, %xmm1
  pxor %xmm3, %xmm2
  movdqu %xmm2, %xmm6
  pxor %xmm2, %xmm2
  mov $3774873600, %r12
  pinsrd $3, %r12d, %xmm2
  movdqu %xmm1, %xmm5
  pclmulqdq $16, %xmm2, %xmm1
  movdqu %xmm1, %xmm3
  movdqu %xmm5, %xmm1
  pclmulqdq $1, %xmm2, %xmm1
  movdqu %xmm1, %xmm4
  movdqu %xmm5, %xmm1
  pclmulqdq $0, %xmm2, %xmm1
  pclmulqdq $17, %xmm2, %xmm5
  movdqu %xmm5, %xmm2
  movdqu %xmm1, %xmm5
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm4, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm1
  pshufd $79, %xmm1, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm4
  pshufd $79, %xmm4, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm5, %xmm1
  movdqu %xmm1, %xmm3
  psrld $31, %xmm3
  movdqu %xmm2, %xmm4
  psrld $31, %xmm4
  pslld $1, %xmm1
  pslld $1, %xmm2
  vpslldq $4, %xmm3, %xmm5
  vpslldq $4, %xmm4, %xmm4
  mov $0, %r12
  pinsrd $0, %r12d, %xmm3
  pshufd $3, %xmm3, %xmm3
  pxor %xmm4, %xmm3
  pxor %xmm5, %xmm1
  pxor %xmm3, %xmm2
  movdqu %xmm2, %xmm5
  pxor %xmm2, %xmm2
  mov $3774873600, %r12
  pinsrd $3, %r12d, %xmm2
  pclmulqdq $17, %xmm2, %xmm1
  movdqu %xmm1, %xmm2
  psrld $31, %xmm2
  pslld $1, %xmm1
  vpslldq $4, %xmm2, %xmm2
  pxor %xmm2, %xmm1
  pxor %xmm5, %xmm1
  pxor %xmm6, %xmm1
  pshufb %xmm8, %xmm1
  add $1, %rdx
  add $16, %r9
  add $16, %r10
  paddd %xmm10, %xmm7
.align 16
L113:
  cmp %rcx, %rdx
  jne L112
  cmp $0, %rsi
  jne L114
  jmp L115
L114:
  movdqu %xmm1, %xmm3
  movdqu 0(%r9), %xmm2
  movdqu %xmm2, %xmm1
  movdqu %xmm7, %xmm0
  mov $579005069656919567, %r12
  pinsrq $0, %r12, %xmm2
  mov $283686952306183, %r12
  pinsrq $1, %r12, %xmm2
  pshufb %xmm2, %xmm0
  movdqu 0(%r8), %xmm2
  pxor %xmm2, %xmm0
  movdqu 16(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 32(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 48(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 64(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 80(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 96(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 112(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 128(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 144(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 160(%r8), %xmm2
  aesenclast %xmm2, %xmm0
  pxor %xmm2, %xmm2
  pxor %xmm0, %xmm1
  movdqu %xmm1, 0(%r10)
  mov %rsi, %rax
  mov %r10, %r9
  movdqu %xmm3, %xmm1
  movdqu 0(%r9), %xmm2
  cmp $8, %rax
  jae L116
  mov $0, %rcx
  pinsrq $1, %rcx, %xmm2
  mov %rax, %rcx
  shl $3, %rcx
  mov $1, %rdx
  shl %cl, %rdx
  sub $1, %rdx
  pextrq $0, %xmm2, %rcx
  and %rdx, %rcx
  pinsrq $0, %rcx, %xmm2
  jmp L117
L116:
  mov %rax, %rcx
  sub $8, %rcx
  shl $3, %rcx
  mov $1, %rdx
  shl %cl, %rdx
  sub $1, %rdx
  pextrq $1, %xmm2, %rcx
  and %rdx, %rcx
  pinsrq $1, %rcx, %xmm2
L117:
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
  pshufb %xmm8, %xmm2
  movdqu %xmm1, %xmm5
  pclmulqdq $16, %xmm2, %xmm1
  movdqu %xmm1, %xmm3
  movdqu %xmm5, %xmm1
  pclmulqdq $1, %xmm2, %xmm1
  movdqu %xmm1, %xmm4
  movdqu %xmm5, %xmm1
  pclmulqdq $0, %xmm2, %xmm1
  pclmulqdq $17, %xmm2, %xmm5
  movdqu %xmm5, %xmm2
  movdqu %xmm1, %xmm5
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm4, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm1
  pshufd $79, %xmm1, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm4
  pshufd $79, %xmm4, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm5, %xmm1
  movdqu %xmm1, %xmm3
  psrld $31, %xmm3
  movdqu %xmm2, %xmm4
  psrld $31, %xmm4
  pslld $1, %xmm1
  pslld $1, %xmm2
  vpslldq $4, %xmm3, %xmm5
  vpslldq $4, %xmm4, %xmm4
  mov $0, %r12
  pinsrd $0, %r12d, %xmm3
  pshufd $3, %xmm3, %xmm3
  pxor %xmm4, %xmm3
  pxor %xmm5, %xmm1
  pxor %xmm3, %xmm2
  movdqu %xmm2, %xmm6
  pxor %xmm2, %xmm2
  mov $3774873600, %r12
  pinsrd $3, %r12d, %xmm2
  movdqu %xmm1, %xmm5
  pclmulqdq $16, %xmm2, %xmm1
  movdqu %xmm1, %xmm3
  movdqu %xmm5, %xmm1
  pclmulqdq $1, %xmm2, %xmm1
  movdqu %xmm1, %xmm4
  movdqu %xmm5, %xmm1
  pclmulqdq $0, %xmm2, %xmm1
  pclmulqdq $17, %xmm2, %xmm5
  movdqu %xmm5, %xmm2
  movdqu %xmm1, %xmm5
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm4, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm1
  pshufd $79, %xmm1, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm4
  pshufd $79, %xmm4, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm5, %xmm1
  movdqu %xmm1, %xmm3
  psrld $31, %xmm3
  movdqu %xmm2, %xmm4
  psrld $31, %xmm4
  pslld $1, %xmm1
  pslld $1, %xmm2
  vpslldq $4, %xmm3, %xmm5
  vpslldq $4, %xmm4, %xmm4
  mov $0, %r12
  pinsrd $0, %r12d, %xmm3
  pshufd $3, %xmm3, %xmm3
  pxor %xmm4, %xmm3
  pxor %xmm5, %xmm1
  pxor %xmm3, %xmm2
  movdqu %xmm2, %xmm5
  pxor %xmm2, %xmm2
  mov $3774873600, %r12
  pinsrd $3, %r12d, %xmm2
  pclmulqdq $17, %xmm2, %xmm1
  movdqu %xmm1, %xmm2
  psrld $31, %xmm2
  pslld $1, %xmm1
  vpslldq $4, %xmm2, %xmm2
  pxor %xmm2, %xmm1
  pxor %xmm5, %xmm1
  pxor %xmm6, %xmm1
  pshufb %xmm8, %xmm1
L115:
  jmp L111
L110:
L111:
  pxor %xmm2, %xmm2
  mov %r13, %rax
  imul $8, %rax
  pinsrd $0, %eax, %xmm2
  mov %r11, %rax
  imul $8, %rax
  pinsrd $2, %eax, %xmm2
  pshufb %xmm8, %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
  pshufb %xmm8, %xmm2
  movdqu %xmm1, %xmm5
  pclmulqdq $16, %xmm2, %xmm1
  movdqu %xmm1, %xmm3
  movdqu %xmm5, %xmm1
  pclmulqdq $1, %xmm2, %xmm1
  movdqu %xmm1, %xmm4
  movdqu %xmm5, %xmm1
  pclmulqdq $0, %xmm2, %xmm1
  pclmulqdq $17, %xmm2, %xmm5
  movdqu %xmm5, %xmm2
  movdqu %xmm1, %xmm5
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm4, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm1
  pshufd $79, %xmm1, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm4
  pshufd $79, %xmm4, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm5, %xmm1
  movdqu %xmm1, %xmm3
  psrld $31, %xmm3
  movdqu %xmm2, %xmm4
  psrld $31, %xmm4
  pslld $1, %xmm1
  pslld $1, %xmm2
  vpslldq $4, %xmm3, %xmm5
  vpslldq $4, %xmm4, %xmm4
  mov $0, %r12
  pinsrd $0, %r12d, %xmm3
  pshufd $3, %xmm3, %xmm3
  pxor %xmm4, %xmm3
  pxor %xmm5, %xmm1
  pxor %xmm3, %xmm2
  movdqu %xmm2, %xmm6
  pxor %xmm2, %xmm2
  mov $3774873600, %r12
  pinsrd $3, %r12d, %xmm2
  movdqu %xmm1, %xmm5
  pclmulqdq $16, %xmm2, %xmm1
  movdqu %xmm1, %xmm3
  movdqu %xmm5, %xmm1
  pclmulqdq $1, %xmm2, %xmm1
  movdqu %xmm1, %xmm4
  movdqu %xmm5, %xmm1
  pclmulqdq $0, %xmm2, %xmm1
  pclmulqdq $17, %xmm2, %xmm5
  movdqu %xmm5, %xmm2
  movdqu %xmm1, %xmm5
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm4, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm1
  pshufd $79, %xmm1, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm4
  pshufd $79, %xmm4, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm5, %xmm1
  movdqu %xmm1, %xmm3
  psrld $31, %xmm3
  movdqu %xmm2, %xmm4
  psrld $31, %xmm4
  pslld $1, %xmm1
  pslld $1, %xmm2
  vpslldq $4, %xmm3, %xmm5
  vpslldq $4, %xmm4, %xmm4
  mov $0, %r12
  pinsrd $0, %r12d, %xmm3
  pshufd $3, %xmm3, %xmm3
  pxor %xmm4, %xmm3
  pxor %xmm5, %xmm1
  pxor %xmm3, %xmm2
  movdqu %xmm2, %xmm5
  pxor %xmm2, %xmm2
  mov $3774873600, %r12
  pinsrd $3, %r12d, %xmm2
  pclmulqdq $17, %xmm2, %xmm1
  movdqu %xmm1, %xmm2
  psrld $31, %xmm2
  pslld $1, %xmm1
  vpslldq $4, %xmm2, %xmm2
  pxor %xmm2, %xmm1
  pxor %xmm5, %xmm1
  pxor %xmm6, %xmm1
  pshufb %xmm8, %xmm1
  mov $1, %r12
  pinsrd $0, %r12d, %xmm7
  movdqu %xmm7, %xmm0
  mov $579005069656919567, %r12
  pinsrq $0, %r12, %xmm2
  mov $283686952306183, %r12
  pinsrq $1, %r12, %xmm2
  pshufb %xmm2, %xmm0
  movdqu 0(%r8), %xmm2
  pxor %xmm2, %xmm0
  movdqu 16(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 32(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 48(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 64(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 80(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 96(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 112(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 128(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 144(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 160(%r8), %xmm2
  aesenclast %xmm2, %xmm0
  pxor %xmm2, %xmm2
  pxor %xmm0, %xmm1
  movdqu %xmm1, 0(%r15)
  pop %rbx
  pop %rbp
  pop %rdi
  pop %rsi
  pop %r12
  pop %r13
  pop %r14
  pop %r15
  ret

.global _gcm_decrypt
_gcm_decrypt:
  mov %rdi, %r9
  push %r15
  push %r14
  push %r13
  push %r12
  push %rsi
  push %rdi
  push %rbp
  push %rbx
  movq 0(%r9), %r14
  movq 8(%r9), %r13
  movq 16(%r9), %rax
  movq 24(%r9), %r11
  movq 32(%r9), %r10
  movq 40(%r9), %r8
  movq 48(%r9), %rbx
  movq 56(%r9), %r15
  movdqu 0(%r10), %xmm7
  pxor %xmm0, %xmm0
  movdqu 0(%r8), %xmm2
  pxor %xmm2, %xmm0
  movdqu 16(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 32(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 48(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 64(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 80(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 96(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 112(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 128(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 144(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 160(%r8), %xmm2
  aesenclast %xmm2, %xmm0
  pxor %xmm2, %xmm2
  movdqu %xmm0, %xmm11
  mov $579005069656919567, %r12
  pinsrq $0, %r12, %xmm8
  mov $283686952306183, %r12
  pinsrq $1, %r12, %xmm8
  pshufb %xmm8, %xmm7
  mov $2, %r12
  pinsrd $0, %r12d, %xmm7
  pxor %xmm1, %xmm1
  cmp $0, %r11
  jbe L200
  mov %r11, %rcx
  shr $4, %rcx
  mov %rax, %r9
  cmp $0, %rcx
  je L202
  mov $0, %rdx
  jmp L205
.align 16
L204:
  movdqu 0(%r9), %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
  pshufb %xmm8, %xmm2
  movdqu %xmm1, %xmm5
  pclmulqdq $16, %xmm2, %xmm1
  movdqu %xmm1, %xmm3
  movdqu %xmm5, %xmm1
  pclmulqdq $1, %xmm2, %xmm1
  movdqu %xmm1, %xmm4
  movdqu %xmm5, %xmm1
  pclmulqdq $0, %xmm2, %xmm1
  pclmulqdq $17, %xmm2, %xmm5
  movdqu %xmm5, %xmm2
  movdqu %xmm1, %xmm5
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm4, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm1
  pshufd $79, %xmm1, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm4
  pshufd $79, %xmm4, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm5, %xmm1
  movdqu %xmm1, %xmm3
  psrld $31, %xmm3
  movdqu %xmm2, %xmm4
  psrld $31, %xmm4
  pslld $1, %xmm1
  pslld $1, %xmm2
  vpslldq $4, %xmm3, %xmm5
  vpslldq $4, %xmm4, %xmm4
  mov $0, %r12
  pinsrd $0, %r12d, %xmm3
  pshufd $3, %xmm3, %xmm3
  pxor %xmm4, %xmm3
  pxor %xmm5, %xmm1
  pxor %xmm3, %xmm2
  movdqu %xmm2, %xmm6
  pxor %xmm2, %xmm2
  mov $3774873600, %r12
  pinsrd $3, %r12d, %xmm2
  movdqu %xmm1, %xmm5
  pclmulqdq $16, %xmm2, %xmm1
  movdqu %xmm1, %xmm3
  movdqu %xmm5, %xmm1
  pclmulqdq $1, %xmm2, %xmm1
  movdqu %xmm1, %xmm4
  movdqu %xmm5, %xmm1
  pclmulqdq $0, %xmm2, %xmm1
  pclmulqdq $17, %xmm2, %xmm5
  movdqu %xmm5, %xmm2
  movdqu %xmm1, %xmm5
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm4, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm1
  pshufd $79, %xmm1, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm4
  pshufd $79, %xmm4, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm5, %xmm1
  movdqu %xmm1, %xmm3
  psrld $31, %xmm3
  movdqu %xmm2, %xmm4
  psrld $31, %xmm4
  pslld $1, %xmm1
  pslld $1, %xmm2
  vpslldq $4, %xmm3, %xmm5
  vpslldq $4, %xmm4, %xmm4
  mov $0, %r12
  pinsrd $0, %r12d, %xmm3
  pshufd $3, %xmm3, %xmm3
  pxor %xmm4, %xmm3
  pxor %xmm5, %xmm1
  pxor %xmm3, %xmm2
  movdqu %xmm2, %xmm5
  pxor %xmm2, %xmm2
  mov $3774873600, %r12
  pinsrd $3, %r12d, %xmm2
  pclmulqdq $17, %xmm2, %xmm1
  movdqu %xmm1, %xmm2
  psrld $31, %xmm2
  pslld $1, %xmm1
  vpslldq $4, %xmm2, %xmm2
  pxor %xmm2, %xmm1
  pxor %xmm5, %xmm1
  pxor %xmm6, %xmm1
  pshufb %xmm8, %xmm1
  add $1, %rdx
  add $16, %r9
.align 16
L205:
  cmp %rcx, %rdx
  jne L204
  jmp L203
L202:
L203:
  mov %r11, %rax
  and $15, %rax
  cmp $0, %rax
  jne L206
  jmp L207
L206:
  movdqu 0(%r9), %xmm2
  cmp $8, %rax
  jae L208
  mov $0, %rcx
  pinsrq $1, %rcx, %xmm2
  mov %rax, %rcx
  shl $3, %rcx
  mov $1, %rdx
  shl %cl, %rdx
  sub $1, %rdx
  pextrq $0, %xmm2, %rcx
  and %rdx, %rcx
  pinsrq $0, %rcx, %xmm2
  jmp L209
L208:
  mov %rax, %rcx
  sub $8, %rcx
  shl $3, %rcx
  mov $1, %rdx
  shl %cl, %rdx
  sub $1, %rdx
  pextrq $1, %xmm2, %rcx
  and %rdx, %rcx
  pinsrq $1, %rcx, %xmm2
L209:
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
  pshufb %xmm8, %xmm2
  movdqu %xmm1, %xmm5
  pclmulqdq $16, %xmm2, %xmm1
  movdqu %xmm1, %xmm3
  movdqu %xmm5, %xmm1
  pclmulqdq $1, %xmm2, %xmm1
  movdqu %xmm1, %xmm4
  movdqu %xmm5, %xmm1
  pclmulqdq $0, %xmm2, %xmm1
  pclmulqdq $17, %xmm2, %xmm5
  movdqu %xmm5, %xmm2
  movdqu %xmm1, %xmm5
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm4, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm1
  pshufd $79, %xmm1, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm4
  pshufd $79, %xmm4, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm5, %xmm1
  movdqu %xmm1, %xmm3
  psrld $31, %xmm3
  movdqu %xmm2, %xmm4
  psrld $31, %xmm4
  pslld $1, %xmm1
  pslld $1, %xmm2
  vpslldq $4, %xmm3, %xmm5
  vpslldq $4, %xmm4, %xmm4
  mov $0, %r12
  pinsrd $0, %r12d, %xmm3
  pshufd $3, %xmm3, %xmm3
  pxor %xmm4, %xmm3
  pxor %xmm5, %xmm1
  pxor %xmm3, %xmm2
  movdqu %xmm2, %xmm6
  pxor %xmm2, %xmm2
  mov $3774873600, %r12
  pinsrd $3, %r12d, %xmm2
  movdqu %xmm1, %xmm5
  pclmulqdq $16, %xmm2, %xmm1
  movdqu %xmm1, %xmm3
  movdqu %xmm5, %xmm1
  pclmulqdq $1, %xmm2, %xmm1
  movdqu %xmm1, %xmm4
  movdqu %xmm5, %xmm1
  pclmulqdq $0, %xmm2, %xmm1
  pclmulqdq $17, %xmm2, %xmm5
  movdqu %xmm5, %xmm2
  movdqu %xmm1, %xmm5
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm4, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm1
  pshufd $79, %xmm1, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm4
  pshufd $79, %xmm4, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm5, %xmm1
  movdqu %xmm1, %xmm3
  psrld $31, %xmm3
  movdqu %xmm2, %xmm4
  psrld $31, %xmm4
  pslld $1, %xmm1
  pslld $1, %xmm2
  vpslldq $4, %xmm3, %xmm5
  vpslldq $4, %xmm4, %xmm4
  mov $0, %r12
  pinsrd $0, %r12d, %xmm3
  pshufd $3, %xmm3, %xmm3
  pxor %xmm4, %xmm3
  pxor %xmm5, %xmm1
  pxor %xmm3, %xmm2
  movdqu %xmm2, %xmm5
  pxor %xmm2, %xmm2
  mov $3774873600, %r12
  pinsrd $3, %r12d, %xmm2
  pclmulqdq $17, %xmm2, %xmm1
  movdqu %xmm1, %xmm2
  psrld $31, %xmm2
  pslld $1, %xmm1
  vpslldq $4, %xmm2, %xmm2
  pxor %xmm2, %xmm1
  pxor %xmm5, %xmm1
  pxor %xmm6, %xmm1
  pshufb %xmm8, %xmm1
L207:
  jmp L201
L200:
L201:
  mov %r14, %rax
  mov %r13, %rcx
  cmp $0, %rcx
  jbe L210
  mov %rcx, %rsi
  and $15, %rsi
  shr $4, %rcx
  mov $0, %rdx
  mov %rax, %r9
  mov %rbx, %r10
  pxor %xmm10, %xmm10
  mov $1, %r12
  pinsrd $0, %r12d, %xmm10
  jmp L213
.align 16
L212:
  movdqu %xmm7, %xmm0
  pshufb %xmm8, %xmm0
  movdqu 0(%r8), %xmm2
  pxor %xmm2, %xmm0
  movdqu 16(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 32(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 48(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 64(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 80(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 96(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 112(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 128(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 144(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 160(%r8), %xmm2
  aesenclast %xmm2, %xmm0
  pxor %xmm2, %xmm2
  movdqu 0(%r9), %xmm2
  pxor %xmm0, %xmm2
  movdqu %xmm2, 0(%r10)
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
  pshufb %xmm8, %xmm2
  movdqu %xmm1, %xmm5
  pclmulqdq $16, %xmm2, %xmm1
  movdqu %xmm1, %xmm3
  movdqu %xmm5, %xmm1
  pclmulqdq $1, %xmm2, %xmm1
  movdqu %xmm1, %xmm4
  movdqu %xmm5, %xmm1
  pclmulqdq $0, %xmm2, %xmm1
  pclmulqdq $17, %xmm2, %xmm5
  movdqu %xmm5, %xmm2
  movdqu %xmm1, %xmm5
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm4, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm1
  pshufd $79, %xmm1, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm4
  pshufd $79, %xmm4, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm5, %xmm1
  movdqu %xmm1, %xmm3
  psrld $31, %xmm3
  movdqu %xmm2, %xmm4
  psrld $31, %xmm4
  pslld $1, %xmm1
  pslld $1, %xmm2
  vpslldq $4, %xmm3, %xmm5
  vpslldq $4, %xmm4, %xmm4
  mov $0, %r12
  pinsrd $0, %r12d, %xmm3
  pshufd $3, %xmm3, %xmm3
  pxor %xmm4, %xmm3
  pxor %xmm5, %xmm1
  pxor %xmm3, %xmm2
  movdqu %xmm2, %xmm6
  pxor %xmm2, %xmm2
  mov $3774873600, %r12
  pinsrd $3, %r12d, %xmm2
  movdqu %xmm1, %xmm5
  pclmulqdq $16, %xmm2, %xmm1
  movdqu %xmm1, %xmm3
  movdqu %xmm5, %xmm1
  pclmulqdq $1, %xmm2, %xmm1
  movdqu %xmm1, %xmm4
  movdqu %xmm5, %xmm1
  pclmulqdq $0, %xmm2, %xmm1
  pclmulqdq $17, %xmm2, %xmm5
  movdqu %xmm5, %xmm2
  movdqu %xmm1, %xmm5
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm4, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm1
  pshufd $79, %xmm1, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm4
  pshufd $79, %xmm4, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm5, %xmm1
  movdqu %xmm1, %xmm3
  psrld $31, %xmm3
  movdqu %xmm2, %xmm4
  psrld $31, %xmm4
  pslld $1, %xmm1
  pslld $1, %xmm2
  vpslldq $4, %xmm3, %xmm5
  vpslldq $4, %xmm4, %xmm4
  mov $0, %r12
  pinsrd $0, %r12d, %xmm3
  pshufd $3, %xmm3, %xmm3
  pxor %xmm4, %xmm3
  pxor %xmm5, %xmm1
  pxor %xmm3, %xmm2
  movdqu %xmm2, %xmm5
  pxor %xmm2, %xmm2
  mov $3774873600, %r12
  pinsrd $3, %r12d, %xmm2
  pclmulqdq $17, %xmm2, %xmm1
  movdqu %xmm1, %xmm2
  psrld $31, %xmm2
  pslld $1, %xmm1
  vpslldq $4, %xmm2, %xmm2
  pxor %xmm2, %xmm1
  pxor %xmm5, %xmm1
  pxor %xmm6, %xmm1
  pshufb %xmm8, %xmm1
  add $1, %rdx
  add $16, %r9
  add $16, %r10
  paddd %xmm10, %xmm7
.align 16
L213:
  cmp %rcx, %rdx
  jne L212
  cmp $0, %rsi
  jne L214
  jmp L215
L214:
  movdqu %xmm1, %xmm3
  movdqu 0(%r9), %xmm2
  movdqu %xmm2, %xmm1
  movdqu %xmm7, %xmm0
  mov $579005069656919567, %r12
  pinsrq $0, %r12, %xmm2
  mov $283686952306183, %r12
  pinsrq $1, %r12, %xmm2
  pshufb %xmm2, %xmm0
  movdqu 0(%r8), %xmm2
  pxor %xmm2, %xmm0
  movdqu 16(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 32(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 48(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 64(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 80(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 96(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 112(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 128(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 144(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 160(%r8), %xmm2
  aesenclast %xmm2, %xmm0
  pxor %xmm2, %xmm2
  pxor %xmm0, %xmm1
  movdqu %xmm1, 0(%r10)
  mov %rsi, %rax
  mov %r10, %r9
  movdqu %xmm3, %xmm1
  movdqu 0(%r9), %xmm2
  cmp $8, %rax
  jae L216
  mov $0, %rcx
  pinsrq $1, %rcx, %xmm2
  mov %rax, %rcx
  shl $3, %rcx
  mov $1, %rdx
  shl %cl, %rdx
  sub $1, %rdx
  pextrq $0, %xmm2, %rcx
  and %rdx, %rcx
  pinsrq $0, %rcx, %xmm2
  jmp L217
L216:
  mov %rax, %rcx
  sub $8, %rcx
  shl $3, %rcx
  mov $1, %rdx
  shl %cl, %rdx
  sub $1, %rdx
  pextrq $1, %xmm2, %rcx
  and %rdx, %rcx
  pinsrq $1, %rcx, %xmm2
L217:
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
  pshufb %xmm8, %xmm2
  movdqu %xmm1, %xmm5
  pclmulqdq $16, %xmm2, %xmm1
  movdqu %xmm1, %xmm3
  movdqu %xmm5, %xmm1
  pclmulqdq $1, %xmm2, %xmm1
  movdqu %xmm1, %xmm4
  movdqu %xmm5, %xmm1
  pclmulqdq $0, %xmm2, %xmm1
  pclmulqdq $17, %xmm2, %xmm5
  movdqu %xmm5, %xmm2
  movdqu %xmm1, %xmm5
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm4, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm1
  pshufd $79, %xmm1, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm4
  pshufd $79, %xmm4, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm5, %xmm1
  movdqu %xmm1, %xmm3
  psrld $31, %xmm3
  movdqu %xmm2, %xmm4
  psrld $31, %xmm4
  pslld $1, %xmm1
  pslld $1, %xmm2
  vpslldq $4, %xmm3, %xmm5
  vpslldq $4, %xmm4, %xmm4
  mov $0, %r12
  pinsrd $0, %r12d, %xmm3
  pshufd $3, %xmm3, %xmm3
  pxor %xmm4, %xmm3
  pxor %xmm5, %xmm1
  pxor %xmm3, %xmm2
  movdqu %xmm2, %xmm6
  pxor %xmm2, %xmm2
  mov $3774873600, %r12
  pinsrd $3, %r12d, %xmm2
  movdqu %xmm1, %xmm5
  pclmulqdq $16, %xmm2, %xmm1
  movdqu %xmm1, %xmm3
  movdqu %xmm5, %xmm1
  pclmulqdq $1, %xmm2, %xmm1
  movdqu %xmm1, %xmm4
  movdqu %xmm5, %xmm1
  pclmulqdq $0, %xmm2, %xmm1
  pclmulqdq $17, %xmm2, %xmm5
  movdqu %xmm5, %xmm2
  movdqu %xmm1, %xmm5
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm4, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm1
  pshufd $79, %xmm1, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm4
  pshufd $79, %xmm4, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm5, %xmm1
  movdqu %xmm1, %xmm3
  psrld $31, %xmm3
  movdqu %xmm2, %xmm4
  psrld $31, %xmm4
  pslld $1, %xmm1
  pslld $1, %xmm2
  vpslldq $4, %xmm3, %xmm5
  vpslldq $4, %xmm4, %xmm4
  mov $0, %r12
  pinsrd $0, %r12d, %xmm3
  pshufd $3, %xmm3, %xmm3
  pxor %xmm4, %xmm3
  pxor %xmm5, %xmm1
  pxor %xmm3, %xmm2
  movdqu %xmm2, %xmm5
  pxor %xmm2, %xmm2
  mov $3774873600, %r12
  pinsrd $3, %r12d, %xmm2
  pclmulqdq $17, %xmm2, %xmm1
  movdqu %xmm1, %xmm2
  psrld $31, %xmm2
  pslld $1, %xmm1
  vpslldq $4, %xmm2, %xmm2
  pxor %xmm2, %xmm1
  pxor %xmm5, %xmm1
  pxor %xmm6, %xmm1
  pshufb %xmm8, %xmm1
L215:
  jmp L211
L210:
L211:
  pxor %xmm2, %xmm2
  mov %r13, %rax
  imul $8, %rax
  pinsrd $0, %eax, %xmm2
  mov %r11, %rax
  imul $8, %rax
  pinsrd $2, %eax, %xmm2
  pshufb %xmm8, %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
  pshufb %xmm8, %xmm2
  movdqu %xmm1, %xmm5
  pclmulqdq $16, %xmm2, %xmm1
  movdqu %xmm1, %xmm3
  movdqu %xmm5, %xmm1
  pclmulqdq $1, %xmm2, %xmm1
  movdqu %xmm1, %xmm4
  movdqu %xmm5, %xmm1
  pclmulqdq $0, %xmm2, %xmm1
  pclmulqdq $17, %xmm2, %xmm5
  movdqu %xmm5, %xmm2
  movdqu %xmm1, %xmm5
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm4, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm1
  pshufd $79, %xmm1, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm4
  pshufd $79, %xmm4, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm5, %xmm1
  movdqu %xmm1, %xmm3
  psrld $31, %xmm3
  movdqu %xmm2, %xmm4
  psrld $31, %xmm4
  pslld $1, %xmm1
  pslld $1, %xmm2
  vpslldq $4, %xmm3, %xmm5
  vpslldq $4, %xmm4, %xmm4
  mov $0, %r12
  pinsrd $0, %r12d, %xmm3
  pshufd $3, %xmm3, %xmm3
  pxor %xmm4, %xmm3
  pxor %xmm5, %xmm1
  pxor %xmm3, %xmm2
  movdqu %xmm2, %xmm6
  pxor %xmm2, %xmm2
  mov $3774873600, %r12
  pinsrd $3, %r12d, %xmm2
  movdqu %xmm1, %xmm5
  pclmulqdq $16, %xmm2, %xmm1
  movdqu %xmm1, %xmm3
  movdqu %xmm5, %xmm1
  pclmulqdq $1, %xmm2, %xmm1
  movdqu %xmm1, %xmm4
  movdqu %xmm5, %xmm1
  pclmulqdq $0, %xmm2, %xmm1
  pclmulqdq $17, %xmm2, %xmm5
  movdqu %xmm5, %xmm2
  movdqu %xmm1, %xmm5
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm4, %xmm1
  mov $0, %r12
  pinsrd $0, %r12d, %xmm1
  pshufd $14, %xmm1, %xmm1
  pxor %xmm1, %xmm2
  movdqu %xmm3, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm1
  pshufd $79, %xmm1, %xmm1
  mov $0, %r12
  pinsrd $3, %r12d, %xmm4
  pshufd $79, %xmm4, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm5, %xmm1
  movdqu %xmm1, %xmm3
  psrld $31, %xmm3
  movdqu %xmm2, %xmm4
  psrld $31, %xmm4
  pslld $1, %xmm1
  pslld $1, %xmm2
  vpslldq $4, %xmm3, %xmm5
  vpslldq $4, %xmm4, %xmm4
  mov $0, %r12
  pinsrd $0, %r12d, %xmm3
  pshufd $3, %xmm3, %xmm3
  pxor %xmm4, %xmm3
  pxor %xmm5, %xmm1
  pxor %xmm3, %xmm2
  movdqu %xmm2, %xmm5
  pxor %xmm2, %xmm2
  mov $3774873600, %r12
  pinsrd $3, %r12d, %xmm2
  pclmulqdq $17, %xmm2, %xmm1
  movdqu %xmm1, %xmm2
  psrld $31, %xmm2
  pslld $1, %xmm1
  vpslldq $4, %xmm2, %xmm2
  pxor %xmm2, %xmm1
  pxor %xmm5, %xmm1
  pxor %xmm6, %xmm1
  pshufb %xmm8, %xmm1
  mov $1, %r12
  pinsrd $0, %r12d, %xmm7
  movdqu %xmm7, %xmm0
  mov $579005069656919567, %r12
  pinsrq $0, %r12, %xmm2
  mov $283686952306183, %r12
  pinsrq $1, %r12, %xmm2
  pshufb %xmm2, %xmm0
  movdqu 0(%r8), %xmm2
  pxor %xmm2, %xmm0
  movdqu 16(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 32(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 48(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 64(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 80(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 96(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 112(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 128(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 144(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 160(%r8), %xmm2
  aesenclast %xmm2, %xmm0
  pxor %xmm2, %xmm2
  pxor %xmm0, %xmm1
  movdqu 0(%r15), %xmm0
  pcmpeqd %xmm1, %xmm0
  pextrq $0, %xmm0, %rdx
  cmp $18446744073709551615, %rdx
  jne L218
  mov $0, %rax
  jmp L219
L218:
  mov $1, %rax
L219:
  pextrq $1, %xmm0, %rdx
  cmp $18446744073709551615, %rdx
  jne L220
  mov $0, %rdx
  jmp L221
L220:
  mov $1, %rdx
L221:
  add %rdx, %rax
  mov %rax, %rdx
  pop %rbx
  pop %rbp
  pop %rdi
  pop %rsi
  pop %r12
  pop %r13
  pop %r14
  pop %r15
  mov %rdx, %rax
  ret


