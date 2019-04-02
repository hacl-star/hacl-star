.text
.global old_aes128_key_expansion
old_aes128_key_expansion:
  movdqu 0(%rcx), %xmm1
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

.global aes128_key_expansion
aes128_key_expansion:
  movdqu 0(%rcx), %xmm1
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

.global aes128_keyhash_init
aes128_keyhash_init:
  mov $579005069656919567, %r8
  pinsrq $0, %r8, %xmm4
  mov $283686952306183, %r8
  pinsrq $1, %r8, %xmm4
  pxor %xmm0, %xmm0
  movdqu %xmm0, 80(%rdx)
  mov %rcx, %r8
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
  pshufb %xmm4, %xmm0
  mov %rdx, %rcx
  movdqu %xmm0, 32(%rcx)
  movdqu %xmm6, %xmm0
  mov %r12, %rax
  movdqu 32(%rcx), %xmm1
  movdqu %xmm1, %xmm6
  movdqu %xmm1, %xmm3
  pxor %xmm4, %xmm4
  pxor %xmm5, %xmm5
  mov $3254779904, %r12
  pinsrd $3, %r12d, %xmm4
  mov $1, %r12
  pinsrd $0, %r12d, %xmm4
  mov $2147483648, %r12
  pinsrd $3, %r12d, %xmm5
  movdqu %xmm3, %xmm1
  movdqu %xmm1, %xmm2
  psrld $31, %xmm2
  pslld $1, %xmm1
  vpslldq $4, %xmm2, %xmm2
  pxor %xmm2, %xmm1
  pand %xmm5, %xmm3
  pcmpeqd %xmm5, %xmm3
  pshufd $255, %xmm3, %xmm3
  pand %xmm4, %xmm3
  vpxor %xmm3, %xmm1, %xmm1
  movdqu %xmm1, 0(%rcx)
  movdqu %xmm6, %xmm1
  movdqu %xmm6, %xmm2
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
  movdqu %xmm1, %xmm6
  movdqu %xmm1, %xmm3
  pxor %xmm4, %xmm4
  pxor %xmm5, %xmm5
  mov $3254779904, %r12
  pinsrd $3, %r12d, %xmm4
  mov $1, %r12
  pinsrd $0, %r12d, %xmm4
  mov $2147483648, %r12
  pinsrd $3, %r12d, %xmm5
  movdqu %xmm3, %xmm1
  movdqu %xmm1, %xmm2
  psrld $31, %xmm2
  pslld $1, %xmm1
  vpslldq $4, %xmm2, %xmm2
  pxor %xmm2, %xmm1
  pand %xmm5, %xmm3
  pcmpeqd %xmm5, %xmm3
  pshufd $255, %xmm3, %xmm3
  pand %xmm4, %xmm3
  vpxor %xmm3, %xmm1, %xmm1
  movdqu %xmm1, 16(%rcx)
  movdqu %xmm6, %xmm2
  movdqu 32(%rcx), %xmm1
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
  movdqu %xmm1, %xmm6
  movdqu %xmm1, %xmm3
  pxor %xmm4, %xmm4
  pxor %xmm5, %xmm5
  mov $3254779904, %r12
  pinsrd $3, %r12d, %xmm4
  mov $1, %r12
  pinsrd $0, %r12d, %xmm4
  mov $2147483648, %r12
  pinsrd $3, %r12d, %xmm5
  movdqu %xmm3, %xmm1
  movdqu %xmm1, %xmm2
  psrld $31, %xmm2
  pslld $1, %xmm1
  vpslldq $4, %xmm2, %xmm2
  pxor %xmm2, %xmm1
  pand %xmm5, %xmm3
  pcmpeqd %xmm5, %xmm3
  pshufd $255, %xmm3, %xmm3
  pand %xmm4, %xmm3
  vpxor %xmm3, %xmm1, %xmm1
  movdqu %xmm1, 48(%rcx)
  movdqu %xmm6, %xmm2
  movdqu 32(%rcx), %xmm1
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
  movdqu %xmm1, %xmm6
  movdqu %xmm1, %xmm3
  pxor %xmm4, %xmm4
  pxor %xmm5, %xmm5
  mov $3254779904, %r12
  pinsrd $3, %r12d, %xmm4
  mov $1, %r12
  pinsrd $0, %r12d, %xmm4
  mov $2147483648, %r12
  pinsrd $3, %r12d, %xmm5
  movdqu %xmm3, %xmm1
  movdqu %xmm1, %xmm2
  psrld $31, %xmm2
  pslld $1, %xmm1
  vpslldq $4, %xmm2, %xmm2
  pxor %xmm2, %xmm1
  pand %xmm5, %xmm3
  pcmpeqd %xmm5, %xmm3
  pshufd $255, %xmm3, %xmm3
  pand %xmm4, %xmm3
  vpxor %xmm3, %xmm1, %xmm1
  movdqu %xmm1, 64(%rcx)
  movdqu %xmm6, %xmm2
  movdqu 32(%rcx), %xmm1
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
  movdqu %xmm1, %xmm6
  movdqu %xmm1, %xmm3
  pxor %xmm4, %xmm4
  pxor %xmm5, %xmm5
  mov $3254779904, %r12
  pinsrd $3, %r12d, %xmm4
  mov $1, %r12
  pinsrd $0, %r12d, %xmm4
  mov $2147483648, %r12
  pinsrd $3, %r12d, %xmm5
  movdqu %xmm3, %xmm1
  movdqu %xmm1, %xmm2
  psrld $31, %xmm2
  pslld $1, %xmm1
  vpslldq $4, %xmm2, %xmm2
  pxor %xmm2, %xmm1
  pand %xmm5, %xmm3
  pcmpeqd %xmm5, %xmm3
  pshufd $255, %xmm3, %xmm3
  pand %xmm4, %xmm3
  vpxor %xmm3, %xmm1, %xmm1
  movdqu %xmm1, 96(%rcx)
  movdqu %xmm6, %xmm2
  movdqu 32(%rcx), %xmm1
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
  movdqu %xmm1, %xmm6
  movdqu %xmm1, %xmm3
  pxor %xmm4, %xmm4
  pxor %xmm5, %xmm5
  mov $3254779904, %r12
  pinsrd $3, %r12d, %xmm4
  mov $1, %r12
  pinsrd $0, %r12d, %xmm4
  mov $2147483648, %r12
  pinsrd $3, %r12d, %xmm5
  movdqu %xmm3, %xmm1
  movdqu %xmm1, %xmm2
  psrld $31, %xmm2
  pslld $1, %xmm1
  vpslldq $4, %xmm2, %xmm2
  pxor %xmm2, %xmm1
  pand %xmm5, %xmm3
  pcmpeqd %xmm5, %xmm3
  pshufd $255, %xmm3, %xmm3
  pand %xmm4, %xmm3
  vpxor %xmm3, %xmm1, %xmm1
  movdqu %xmm1, 112(%rcx)
  movdqu %xmm0, %xmm6
  mov %rax, %r12
  ret

.global old_aes256_key_expansion
old_aes256_key_expansion:
  movdqu 0(%rcx), %xmm1
  movdqu 16(%rcx), %xmm3
  movdqu %xmm1, 0(%rdx)
  movdqu %xmm3, 16(%rdx)
  aeskeygenassist $1, %xmm3, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 32(%rdx)
  aeskeygenassist $0, %xmm1, %xmm2
  pshufd $170, %xmm2, %xmm2
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  pxor %xmm2, %xmm3
  movdqu %xmm3, 48(%rdx)
  aeskeygenassist $2, %xmm3, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 64(%rdx)
  aeskeygenassist $0, %xmm1, %xmm2
  pshufd $170, %xmm2, %xmm2
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  pxor %xmm2, %xmm3
  movdqu %xmm3, 80(%rdx)
  aeskeygenassist $4, %xmm3, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 96(%rdx)
  aeskeygenassist $0, %xmm1, %xmm2
  pshufd $170, %xmm2, %xmm2
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  pxor %xmm2, %xmm3
  movdqu %xmm3, 112(%rdx)
  aeskeygenassist $8, %xmm3, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 128(%rdx)
  aeskeygenassist $0, %xmm1, %xmm2
  pshufd $170, %xmm2, %xmm2
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  pxor %xmm2, %xmm3
  movdqu %xmm3, 144(%rdx)
  aeskeygenassist $16, %xmm3, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 160(%rdx)
  aeskeygenassist $0, %xmm1, %xmm2
  pshufd $170, %xmm2, %xmm2
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  pxor %xmm2, %xmm3
  movdqu %xmm3, 176(%rdx)
  aeskeygenassist $32, %xmm3, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 192(%rdx)
  aeskeygenassist $0, %xmm1, %xmm2
  pshufd $170, %xmm2, %xmm2
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  pxor %xmm2, %xmm3
  movdqu %xmm3, 208(%rdx)
  aeskeygenassist $64, %xmm3, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 224(%rdx)
  pxor %xmm1, %xmm1
  pxor %xmm2, %xmm2
  pxor %xmm3, %xmm3
  pxor %xmm4, %xmm4
  ret

.global aes256_key_expansion
aes256_key_expansion:
  movdqu 0(%rcx), %xmm1
  movdqu 16(%rcx), %xmm3
  movdqu %xmm1, 0(%rdx)
  movdqu %xmm3, 16(%rdx)
  aeskeygenassist $1, %xmm3, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 32(%rdx)
  aeskeygenassist $0, %xmm1, %xmm2
  pshufd $170, %xmm2, %xmm2
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  pxor %xmm2, %xmm3
  movdqu %xmm3, 48(%rdx)
  aeskeygenassist $2, %xmm3, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 64(%rdx)
  aeskeygenassist $0, %xmm1, %xmm2
  pshufd $170, %xmm2, %xmm2
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  pxor %xmm2, %xmm3
  movdqu %xmm3, 80(%rdx)
  aeskeygenassist $4, %xmm3, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 96(%rdx)
  aeskeygenassist $0, %xmm1, %xmm2
  pshufd $170, %xmm2, %xmm2
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  pxor %xmm2, %xmm3
  movdqu %xmm3, 112(%rdx)
  aeskeygenassist $8, %xmm3, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 128(%rdx)
  aeskeygenassist $0, %xmm1, %xmm2
  pshufd $170, %xmm2, %xmm2
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  pxor %xmm2, %xmm3
  movdqu %xmm3, 144(%rdx)
  aeskeygenassist $16, %xmm3, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 160(%rdx)
  aeskeygenassist $0, %xmm1, %xmm2
  pshufd $170, %xmm2, %xmm2
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  pxor %xmm2, %xmm3
  movdqu %xmm3, 176(%rdx)
  aeskeygenassist $32, %xmm3, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 192(%rdx)
  aeskeygenassist $0, %xmm1, %xmm2
  pshufd $170, %xmm2, %xmm2
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  vpslldq $4, %xmm3, %xmm4
  pxor %xmm4, %xmm3
  pxor %xmm2, %xmm3
  movdqu %xmm3, 208(%rdx)
  aeskeygenassist $64, %xmm3, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  vpslldq $4, %xmm1, %xmm4
  pxor %xmm4, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 224(%rdx)
  pxor %xmm1, %xmm1
  pxor %xmm2, %xmm2
  pxor %xmm3, %xmm3
  pxor %xmm4, %xmm4
  ret

.global aes256_keyhash_init
aes256_keyhash_init:
  mov $579005069656919567, %r8
  pinsrq $0, %r8, %xmm4
  mov $283686952306183, %r8
  pinsrq $1, %r8, %xmm4
  pxor %xmm0, %xmm0
  movdqu %xmm0, 80(%rdx)
  mov %rcx, %r8
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
  aesenc %xmm2, %xmm0
  movdqu 176(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 192(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 208(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 224(%r8), %xmm2
  aesenclast %xmm2, %xmm0
  pxor %xmm2, %xmm2
  pshufb %xmm4, %xmm0
  mov %rdx, %rcx
  movdqu %xmm0, 32(%rcx)
  movdqu %xmm6, %xmm0
  mov %r12, %rax
  movdqu 32(%rcx), %xmm1
  movdqu %xmm1, %xmm6
  movdqu %xmm1, %xmm3
  pxor %xmm4, %xmm4
  pxor %xmm5, %xmm5
  mov $3254779904, %r12
  pinsrd $3, %r12d, %xmm4
  mov $1, %r12
  pinsrd $0, %r12d, %xmm4
  mov $2147483648, %r12
  pinsrd $3, %r12d, %xmm5
  movdqu %xmm3, %xmm1
  movdqu %xmm1, %xmm2
  psrld $31, %xmm2
  pslld $1, %xmm1
  vpslldq $4, %xmm2, %xmm2
  pxor %xmm2, %xmm1
  pand %xmm5, %xmm3
  pcmpeqd %xmm5, %xmm3
  pshufd $255, %xmm3, %xmm3
  pand %xmm4, %xmm3
  vpxor %xmm3, %xmm1, %xmm1
  movdqu %xmm1, 0(%rcx)
  movdqu %xmm6, %xmm1
  movdqu %xmm6, %xmm2
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
  movdqu %xmm1, %xmm6
  movdqu %xmm1, %xmm3
  pxor %xmm4, %xmm4
  pxor %xmm5, %xmm5
  mov $3254779904, %r12
  pinsrd $3, %r12d, %xmm4
  mov $1, %r12
  pinsrd $0, %r12d, %xmm4
  mov $2147483648, %r12
  pinsrd $3, %r12d, %xmm5
  movdqu %xmm3, %xmm1
  movdqu %xmm1, %xmm2
  psrld $31, %xmm2
  pslld $1, %xmm1
  vpslldq $4, %xmm2, %xmm2
  pxor %xmm2, %xmm1
  pand %xmm5, %xmm3
  pcmpeqd %xmm5, %xmm3
  pshufd $255, %xmm3, %xmm3
  pand %xmm4, %xmm3
  vpxor %xmm3, %xmm1, %xmm1
  movdqu %xmm1, 16(%rcx)
  movdqu %xmm6, %xmm2
  movdqu 32(%rcx), %xmm1
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
  movdqu %xmm1, %xmm6
  movdqu %xmm1, %xmm3
  pxor %xmm4, %xmm4
  pxor %xmm5, %xmm5
  mov $3254779904, %r12
  pinsrd $3, %r12d, %xmm4
  mov $1, %r12
  pinsrd $0, %r12d, %xmm4
  mov $2147483648, %r12
  pinsrd $3, %r12d, %xmm5
  movdqu %xmm3, %xmm1
  movdqu %xmm1, %xmm2
  psrld $31, %xmm2
  pslld $1, %xmm1
  vpslldq $4, %xmm2, %xmm2
  pxor %xmm2, %xmm1
  pand %xmm5, %xmm3
  pcmpeqd %xmm5, %xmm3
  pshufd $255, %xmm3, %xmm3
  pand %xmm4, %xmm3
  vpxor %xmm3, %xmm1, %xmm1
  movdqu %xmm1, 48(%rcx)
  movdqu %xmm6, %xmm2
  movdqu 32(%rcx), %xmm1
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
  movdqu %xmm1, %xmm6
  movdqu %xmm1, %xmm3
  pxor %xmm4, %xmm4
  pxor %xmm5, %xmm5
  mov $3254779904, %r12
  pinsrd $3, %r12d, %xmm4
  mov $1, %r12
  pinsrd $0, %r12d, %xmm4
  mov $2147483648, %r12
  pinsrd $3, %r12d, %xmm5
  movdqu %xmm3, %xmm1
  movdqu %xmm1, %xmm2
  psrld $31, %xmm2
  pslld $1, %xmm1
  vpslldq $4, %xmm2, %xmm2
  pxor %xmm2, %xmm1
  pand %xmm5, %xmm3
  pcmpeqd %xmm5, %xmm3
  pshufd $255, %xmm3, %xmm3
  pand %xmm4, %xmm3
  vpxor %xmm3, %xmm1, %xmm1
  movdqu %xmm1, 64(%rcx)
  movdqu %xmm6, %xmm2
  movdqu 32(%rcx), %xmm1
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
  movdqu %xmm1, %xmm6
  movdqu %xmm1, %xmm3
  pxor %xmm4, %xmm4
  pxor %xmm5, %xmm5
  mov $3254779904, %r12
  pinsrd $3, %r12d, %xmm4
  mov $1, %r12
  pinsrd $0, %r12d, %xmm4
  mov $2147483648, %r12
  pinsrd $3, %r12d, %xmm5
  movdqu %xmm3, %xmm1
  movdqu %xmm1, %xmm2
  psrld $31, %xmm2
  pslld $1, %xmm1
  vpslldq $4, %xmm2, %xmm2
  pxor %xmm2, %xmm1
  pand %xmm5, %xmm3
  pcmpeqd %xmm5, %xmm3
  pshufd $255, %xmm3, %xmm3
  pand %xmm4, %xmm3
  vpxor %xmm3, %xmm1, %xmm1
  movdqu %xmm1, 96(%rcx)
  movdqu %xmm6, %xmm2
  movdqu 32(%rcx), %xmm1
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
  movdqu %xmm1, %xmm6
  movdqu %xmm1, %xmm3
  pxor %xmm4, %xmm4
  pxor %xmm5, %xmm5
  mov $3254779904, %r12
  pinsrd $3, %r12d, %xmm4
  mov $1, %r12
  pinsrd $0, %r12d, %xmm4
  mov $2147483648, %r12
  pinsrd $3, %r12d, %xmm5
  movdqu %xmm3, %xmm1
  movdqu %xmm1, %xmm2
  psrld $31, %xmm2
  pslld $1, %xmm1
  vpslldq $4, %xmm2, %xmm2
  pxor %xmm2, %xmm1
  pand %xmm5, %xmm3
  pcmpeqd %xmm5, %xmm3
  pshufd $255, %xmm3, %xmm3
  pand %xmm4, %xmm3
  vpxor %xmm3, %xmm1, %xmm1
  movdqu %xmm1, 112(%rcx)
  movdqu %xmm0, %xmm6
  mov %rax, %r12
  ret

.global old_gcm128_encrypt
old_gcm128_encrypt:
  mov %rcx, %r9
  push %r15
  push %r14
  push %r13
  push %r12
  push %rsi
  push %rdi
  push %rbp
  push %rbx
  pextrq $0, %xmm15, %rax
  push %rax
  pextrq $1, %xmm15, %rax
  push %rax
  pextrq $0, %xmm14, %rax
  push %rax
  pextrq $1, %xmm14, %rax
  push %rax
  pextrq $0, %xmm13, %rax
  push %rax
  pextrq $1, %xmm13, %rax
  push %rax
  pextrq $0, %xmm12, %rax
  push %rax
  pextrq $1, %xmm12, %rax
  push %rax
  pextrq $0, %xmm11, %rax
  push %rax
  pextrq $1, %xmm11, %rax
  push %rax
  pextrq $0, %xmm10, %rax
  push %rax
  pextrq $1, %xmm10, %rax
  push %rax
  pextrq $0, %xmm9, %rax
  push %rax
  pextrq $1, %xmm9, %rax
  push %rax
  pextrq $0, %xmm8, %rax
  push %rax
  pextrq $1, %xmm8, %rax
  push %rax
  pextrq $0, %xmm7, %rax
  push %rax
  pextrq $1, %xmm7, %rax
  push %rax
  pextrq $0, %xmm6, %rax
  push %rax
  pextrq $1, %xmm6, %rax
  push %rax
  movq 0(%r9), %r14
  movq 8(%r9), %r13
  movq 16(%r9), %rax
  movq 24(%r9), %r11
  movq 32(%r9), %r10
  movq 40(%r9), %r8
  movq 48(%r9), %rbx
  movq 56(%r9), %r15
  movdqu 0(%r10), %xmm7
  mov $579005069656919567, %r12
  pinsrq $0, %r12, %xmm8
  mov $283686952306183, %r12
  pinsrq $1, %r12, %xmm8
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
  pshufb %xmm8, %xmm0
  movdqu %xmm0, %xmm11
  pshufb %xmm8, %xmm7
  mov $2, %r12
  pinsrd $0, %r12d, %xmm7
  pxor %xmm1, %xmm1
  cmp $0, %r11
  jbe L0
  mov %r11, %rcx
  shr $4, %rcx
  mov %rax, %r9
  cmp $0, %rcx
  je L2
  mov $0, %rdx
  jmp L5
.balign 16
L4:
  movdqu 0(%r9), %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
.balign 16
L5:
  cmp %rcx, %rdx
  jne L4
  jmp L3
L2:
L3:
  mov %r11, %rax
  and $15, %rax
  cmp $0, %rax
  jne L6
  jmp L7
L6:
  movdqu 0(%r9), %xmm2
  cmp $8, %rax
  jae L8
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
  jmp L9
L8:
  mov %rax, %rcx
  sub $8, %rcx
  shl $3, %rcx
  mov $1, %rdx
  shl %cl, %rdx
  sub $1, %rdx
  pextrq $1, %xmm2, %rcx
  and %rdx, %rcx
  pinsrq $1, %rcx, %xmm2
L9:
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
L7:
  jmp L1
L0:
L1:
  mov %r14, %rax
  mov %r13, %rcx
  cmp $0, %rcx
  jbe L10
  mov %rcx, %rsi
  and $15, %rsi
  shr $4, %rcx
  mov %rcx, %rdx
  shr $2, %rdx
  and $3, %rcx
  cmp $0, %rdx
  jbe L12
  mov %rax, %r9
  mov %rbx, %r10
  pshufb %xmm8, %xmm7
  movdqu %xmm7, %xmm9
  mov $579005069656919567, %rax
  pinsrq $0, %rax, %xmm0
  mov $579005069656919567, %rax
  pinsrq $1, %rax, %xmm0
  pshufb %xmm0, %xmm9
  movdqu %xmm9, %xmm10
  pxor %xmm3, %xmm3
  mov $1, %rax
  pinsrd $2, %eax, %xmm3
  paddd %xmm3, %xmm9
  mov $3, %rax
  pinsrd $2, %eax, %xmm3
  mov $2, %rax
  pinsrd $0, %eax, %xmm3
  paddd %xmm3, %xmm10
  pshufb %xmm8, %xmm9
  pshufb %xmm8, %xmm10
  pextrq $0, %xmm7, %rdi
  mov $283686952306183, %rax
  pinsrq $0, %rax, %xmm0
  mov $579005069656919567, %rax
  pinsrq $1, %rax, %xmm0
  pxor %xmm15, %xmm15
  mov $4, %rax
  pinsrd $0, %eax, %xmm15
  mov $4, %rax
  pinsrd $2, %eax, %xmm15
  jmp L15
.balign 16
L14:
  pinsrq $0, %rdi, %xmm2
  pinsrq $0, %rdi, %xmm12
  pinsrq $0, %rdi, %xmm13
  pinsrq $0, %rdi, %xmm14
  shufpd $2, %xmm9, %xmm2
  shufpd $0, %xmm9, %xmm12
  shufpd $2, %xmm10, %xmm13
  shufpd $0, %xmm10, %xmm14
  pshufb %xmm0, %xmm9
  pshufb %xmm0, %xmm10
  movdqu 0(%r8), %xmm3
  movdqu 16(%r8), %xmm4
  movdqu 32(%r8), %xmm5
  movdqu 48(%r8), %xmm6
  paddd %xmm15, %xmm9
  paddd %xmm15, %xmm10
  pxor %xmm3, %xmm2
  pxor %xmm3, %xmm12
  pxor %xmm3, %xmm13
  pxor %xmm3, %xmm14
  pshufb %xmm0, %xmm9
  pshufb %xmm0, %xmm10
  aesenc %xmm4, %xmm2
  aesenc %xmm4, %xmm12
  aesenc %xmm4, %xmm13
  aesenc %xmm4, %xmm14
  aesenc %xmm5, %xmm2
  aesenc %xmm5, %xmm12
  aesenc %xmm5, %xmm13
  aesenc %xmm5, %xmm14
  aesenc %xmm6, %xmm2
  aesenc %xmm6, %xmm12
  aesenc %xmm6, %xmm13
  aesenc %xmm6, %xmm14
  movdqu 64(%r8), %xmm3
  movdqu 80(%r8), %xmm4
  movdqu 96(%r8), %xmm5
  movdqu 112(%r8), %xmm6
  aesenc %xmm3, %xmm2
  aesenc %xmm3, %xmm12
  aesenc %xmm3, %xmm13
  aesenc %xmm3, %xmm14
  aesenc %xmm4, %xmm2
  aesenc %xmm4, %xmm12
  aesenc %xmm4, %xmm13
  aesenc %xmm4, %xmm14
  aesenc %xmm5, %xmm2
  aesenc %xmm5, %xmm12
  aesenc %xmm5, %xmm13
  aesenc %xmm5, %xmm14
  aesenc %xmm6, %xmm2
  aesenc %xmm6, %xmm12
  aesenc %xmm6, %xmm13
  aesenc %xmm6, %xmm14
  movdqu 128(%r8), %xmm3
  movdqu 144(%r8), %xmm4
  movdqu 160(%r8), %xmm5
  aesenc %xmm3, %xmm2
  aesenc %xmm3, %xmm12
  aesenc %xmm3, %xmm13
  aesenc %xmm3, %xmm14
  aesenc %xmm4, %xmm2
  aesenc %xmm4, %xmm12
  aesenc %xmm4, %xmm13
  aesenc %xmm4, %xmm14
  aesenclast %xmm5, %xmm2
  aesenclast %xmm5, %xmm12
  aesenclast %xmm5, %xmm13
  aesenclast %xmm5, %xmm14
  movdqu 0(%r9), %xmm7
  pxor %xmm7, %xmm2
  movdqu 16(%r9), %xmm7
  pxor %xmm7, %xmm12
  movdqu 32(%r9), %xmm7
  pxor %xmm7, %xmm13
  movdqu 48(%r9), %xmm7
  pxor %xmm7, %xmm14
  movdqu %xmm2, 0(%r10)
  movdqu %xmm12, 16(%r10)
  movdqu %xmm13, 32(%r10)
  movdqu %xmm14, 48(%r10)
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
  movdqu %xmm12, %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
  movdqu %xmm13, %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
  movdqu %xmm14, %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
  sub $1, %rdx
  add $64, %r9
  add $64, %r10
.balign 16
L15:
  cmp $0, %rdx
  ja L14
  movdqu %xmm9, %xmm7
  pinsrq $0, %rdi, %xmm7
  pshufb %xmm8, %xmm7
  mov %r9, %rax
  mov %r10, %rbx
  jmp L13
L12:
L13:
  mov $0, %rdx
  mov %rax, %r9
  mov %rbx, %r10
  pxor %xmm10, %xmm10
  mov $1, %r12
  pinsrd $0, %r12d, %xmm10
  jmp L17
.balign 16
L16:
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
.balign 16
L17:
  cmp %rcx, %rdx
  jne L16
  cmp $0, %rsi
  jne L18
  jmp L19
L18:
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
  jae L20
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
  jmp L21
L20:
  mov %rax, %rcx
  sub $8, %rcx
  shl $3, %rcx
  mov $1, %rdx
  shl %cl, %rdx
  sub $1, %rdx
  pextrq $1, %xmm2, %rcx
  and %rdx, %rcx
  pinsrq $1, %rcx, %xmm2
L21:
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
L19:
  jmp L11
L10:
L11:
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
  pop %rax
  pinsrq $1, %rax, %xmm6
  pop %rax
  pinsrq $0, %rax, %xmm6
  pop %rax
  pinsrq $1, %rax, %xmm7
  pop %rax
  pinsrq $0, %rax, %xmm7
  pop %rax
  pinsrq $1, %rax, %xmm8
  pop %rax
  pinsrq $0, %rax, %xmm8
  pop %rax
  pinsrq $1, %rax, %xmm9
  pop %rax
  pinsrq $0, %rax, %xmm9
  pop %rax
  pinsrq $1, %rax, %xmm10
  pop %rax
  pinsrq $0, %rax, %xmm10
  pop %rax
  pinsrq $1, %rax, %xmm11
  pop %rax
  pinsrq $0, %rax, %xmm11
  pop %rax
  pinsrq $1, %rax, %xmm12
  pop %rax
  pinsrq $0, %rax, %xmm12
  pop %rax
  pinsrq $1, %rax, %xmm13
  pop %rax
  pinsrq $0, %rax, %xmm13
  pop %rax
  pinsrq $1, %rax, %xmm14
  pop %rax
  pinsrq $0, %rax, %xmm14
  pop %rax
  pinsrq $1, %rax, %xmm15
  pop %rax
  pinsrq $0, %rax, %xmm15
  pop %rbx
  pop %rbp
  pop %rdi
  pop %rsi
  pop %r12
  pop %r13
  pop %r14
  pop %r15
  ret

.global gcm128_encrypt
gcm128_encrypt:
  push %r15
  push %r14
  push %r13
  push %r12
  push %rsi
  push %rdi
  push %rbp
  push %rbx
  pextrq $0, %xmm15, %rax
  push %rax
  pextrq $1, %xmm15, %rax
  push %rax
  pextrq $0, %xmm14, %rax
  push %rax
  pextrq $1, %xmm14, %rax
  push %rax
  pextrq $0, %xmm13, %rax
  push %rax
  pextrq $1, %xmm13, %rax
  push %rax
  pextrq $0, %xmm12, %rax
  push %rax
  pextrq $1, %xmm12, %rax
  push %rax
  pextrq $0, %xmm11, %rax
  push %rax
  pextrq $1, %xmm11, %rax
  push %rax
  pextrq $0, %xmm10, %rax
  push %rax
  pextrq $1, %xmm10, %rax
  push %rax
  pextrq $0, %xmm9, %rax
  push %rax
  pextrq $1, %xmm9, %rax
  push %rax
  pextrq $0, %xmm8, %rax
  push %rax
  pextrq $1, %xmm8, %rax
  push %rax
  pextrq $0, %xmm7, %rax
  push %rax
  pextrq $1, %xmm7, %rax
  push %rax
  pextrq $0, %xmm6, %rax
  push %rax
  pextrq $1, %xmm6, %rax
  push %rax
  mov %rcx, %r14
  mov %rdx, %r13
  mov %r8, %rax
  mov %r9, %r11
  mov 264(%rsp), %r10
  mov 272(%rsp), %r8
  mov 280(%rsp), %rbx
  mov 288(%rsp), %r15
  movdqu 0(%r10), %xmm7
  mov $579005069656919567, %r12
  pinsrq $0, %r12, %xmm8
  mov $283686952306183, %r12
  pinsrq $1, %r12, %xmm8
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
  pshufb %xmm8, %xmm0
  movdqu %xmm0, %xmm11
  pshufb %xmm8, %xmm7
  mov $2, %r12
  pinsrd $0, %r12d, %xmm7
  pxor %xmm1, %xmm1
  cmp $0, %r11
  jbe L22
  mov %r11, %rcx
  shr $4, %rcx
  mov %rax, %r9
  cmp $0, %rcx
  je L24
  mov $0, %rdx
  jmp L27
.balign 16
L26:
  movdqu 0(%r9), %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
.balign 16
L27:
  cmp %rcx, %rdx
  jne L26
  jmp L25
L24:
L25:
  mov %r11, %rax
  and $15, %rax
  cmp $0, %rax
  jne L28
  jmp L29
L28:
  movdqu 0(%r9), %xmm2
  cmp $8, %rax
  jae L30
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
  jmp L31
L30:
  mov %rax, %rcx
  sub $8, %rcx
  shl $3, %rcx
  mov $1, %rdx
  shl %cl, %rdx
  sub $1, %rdx
  pextrq $1, %xmm2, %rcx
  and %rdx, %rcx
  pinsrq $1, %rcx, %xmm2
L31:
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
L29:
  jmp L23
L22:
L23:
  mov %r14, %rax
  mov %r13, %rcx
  cmp $0, %rcx
  jbe L32
  mov %rcx, %rsi
  and $15, %rsi
  shr $4, %rcx
  mov %rcx, %rdx
  shr $2, %rdx
  and $3, %rcx
  cmp $0, %rdx
  jbe L34
  mov %rax, %r9
  mov %rbx, %r10
  pshufb %xmm8, %xmm7
  movdqu %xmm7, %xmm9
  mov $579005069656919567, %rax
  pinsrq $0, %rax, %xmm0
  mov $579005069656919567, %rax
  pinsrq $1, %rax, %xmm0
  pshufb %xmm0, %xmm9
  movdqu %xmm9, %xmm10
  pxor %xmm3, %xmm3
  mov $1, %rax
  pinsrd $2, %eax, %xmm3
  paddd %xmm3, %xmm9
  mov $3, %rax
  pinsrd $2, %eax, %xmm3
  mov $2, %rax
  pinsrd $0, %eax, %xmm3
  paddd %xmm3, %xmm10
  pshufb %xmm8, %xmm9
  pshufb %xmm8, %xmm10
  pextrq $0, %xmm7, %rdi
  mov $283686952306183, %rax
  pinsrq $0, %rax, %xmm0
  mov $579005069656919567, %rax
  pinsrq $1, %rax, %xmm0
  pxor %xmm15, %xmm15
  mov $4, %rax
  pinsrd $0, %eax, %xmm15
  mov $4, %rax
  pinsrd $2, %eax, %xmm15
  jmp L37
.balign 16
L36:
  pinsrq $0, %rdi, %xmm2
  pinsrq $0, %rdi, %xmm12
  pinsrq $0, %rdi, %xmm13
  pinsrq $0, %rdi, %xmm14
  shufpd $2, %xmm9, %xmm2
  shufpd $0, %xmm9, %xmm12
  shufpd $2, %xmm10, %xmm13
  shufpd $0, %xmm10, %xmm14
  pshufb %xmm0, %xmm9
  pshufb %xmm0, %xmm10
  movdqu 0(%r8), %xmm3
  movdqu 16(%r8), %xmm4
  movdqu 32(%r8), %xmm5
  movdqu 48(%r8), %xmm6
  paddd %xmm15, %xmm9
  paddd %xmm15, %xmm10
  pxor %xmm3, %xmm2
  pxor %xmm3, %xmm12
  pxor %xmm3, %xmm13
  pxor %xmm3, %xmm14
  pshufb %xmm0, %xmm9
  pshufb %xmm0, %xmm10
  aesenc %xmm4, %xmm2
  aesenc %xmm4, %xmm12
  aesenc %xmm4, %xmm13
  aesenc %xmm4, %xmm14
  aesenc %xmm5, %xmm2
  aesenc %xmm5, %xmm12
  aesenc %xmm5, %xmm13
  aesenc %xmm5, %xmm14
  aesenc %xmm6, %xmm2
  aesenc %xmm6, %xmm12
  aesenc %xmm6, %xmm13
  aesenc %xmm6, %xmm14
  movdqu 64(%r8), %xmm3
  movdqu 80(%r8), %xmm4
  movdqu 96(%r8), %xmm5
  movdqu 112(%r8), %xmm6
  aesenc %xmm3, %xmm2
  aesenc %xmm3, %xmm12
  aesenc %xmm3, %xmm13
  aesenc %xmm3, %xmm14
  aesenc %xmm4, %xmm2
  aesenc %xmm4, %xmm12
  aesenc %xmm4, %xmm13
  aesenc %xmm4, %xmm14
  aesenc %xmm5, %xmm2
  aesenc %xmm5, %xmm12
  aesenc %xmm5, %xmm13
  aesenc %xmm5, %xmm14
  aesenc %xmm6, %xmm2
  aesenc %xmm6, %xmm12
  aesenc %xmm6, %xmm13
  aesenc %xmm6, %xmm14
  movdqu 128(%r8), %xmm3
  movdqu 144(%r8), %xmm4
  movdqu 160(%r8), %xmm5
  aesenc %xmm3, %xmm2
  aesenc %xmm3, %xmm12
  aesenc %xmm3, %xmm13
  aesenc %xmm3, %xmm14
  aesenc %xmm4, %xmm2
  aesenc %xmm4, %xmm12
  aesenc %xmm4, %xmm13
  aesenc %xmm4, %xmm14
  aesenclast %xmm5, %xmm2
  aesenclast %xmm5, %xmm12
  aesenclast %xmm5, %xmm13
  aesenclast %xmm5, %xmm14
  movdqu 0(%r9), %xmm7
  pxor %xmm7, %xmm2
  movdqu 16(%r9), %xmm7
  pxor %xmm7, %xmm12
  movdqu 32(%r9), %xmm7
  pxor %xmm7, %xmm13
  movdqu 48(%r9), %xmm7
  pxor %xmm7, %xmm14
  movdqu %xmm2, 0(%r10)
  movdqu %xmm12, 16(%r10)
  movdqu %xmm13, 32(%r10)
  movdqu %xmm14, 48(%r10)
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
  movdqu %xmm12, %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
  movdqu %xmm13, %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
  movdqu %xmm14, %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
  sub $1, %rdx
  add $64, %r9
  add $64, %r10
.balign 16
L37:
  cmp $0, %rdx
  ja L36
  movdqu %xmm9, %xmm7
  pinsrq $0, %rdi, %xmm7
  pshufb %xmm8, %xmm7
  mov %r9, %rax
  mov %r10, %rbx
  jmp L35
L34:
L35:
  mov $0, %rdx
  mov %rax, %r9
  mov %rbx, %r10
  pxor %xmm10, %xmm10
  mov $1, %r12
  pinsrd $0, %r12d, %xmm10
  jmp L39
.balign 16
L38:
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
.balign 16
L39:
  cmp %rcx, %rdx
  jne L38
  cmp $0, %rsi
  jne L40
  jmp L41
L40:
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
  jae L42
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
  jmp L43
L42:
  mov %rax, %rcx
  sub $8, %rcx
  shl $3, %rcx
  mov $1, %rdx
  shl %cl, %rdx
  sub $1, %rdx
  pextrq $1, %xmm2, %rcx
  and %rdx, %rcx
  pinsrq $1, %rcx, %xmm2
L43:
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
L41:
  jmp L33
L32:
L33:
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
  pop %rax
  pinsrq $1, %rax, %xmm6
  pop %rax
  pinsrq $0, %rax, %xmm6
  pop %rax
  pinsrq $1, %rax, %xmm7
  pop %rax
  pinsrq $0, %rax, %xmm7
  pop %rax
  pinsrq $1, %rax, %xmm8
  pop %rax
  pinsrq $0, %rax, %xmm8
  pop %rax
  pinsrq $1, %rax, %xmm9
  pop %rax
  pinsrq $0, %rax, %xmm9
  pop %rax
  pinsrq $1, %rax, %xmm10
  pop %rax
  pinsrq $0, %rax, %xmm10
  pop %rax
  pinsrq $1, %rax, %xmm11
  pop %rax
  pinsrq $0, %rax, %xmm11
  pop %rax
  pinsrq $1, %rax, %xmm12
  pop %rax
  pinsrq $0, %rax, %xmm12
  pop %rax
  pinsrq $1, %rax, %xmm13
  pop %rax
  pinsrq $0, %rax, %xmm13
  pop %rax
  pinsrq $1, %rax, %xmm14
  pop %rax
  pinsrq $0, %rax, %xmm14
  pop %rax
  pinsrq $1, %rax, %xmm15
  pop %rax
  pinsrq $0, %rax, %xmm15
  pop %rbx
  pop %rbp
  pop %rdi
  pop %rsi
  pop %r12
  pop %r13
  pop %r14
  pop %r15
  ret

.global old_gcm128_decrypt
old_gcm128_decrypt:
  mov %rcx, %r9
  push %r15
  push %r14
  push %r13
  push %r12
  push %rsi
  push %rdi
  push %rbp
  push %rbx
  pextrq $0, %xmm15, %rax
  push %rax
  pextrq $1, %xmm15, %rax
  push %rax
  pextrq $0, %xmm14, %rax
  push %rax
  pextrq $1, %xmm14, %rax
  push %rax
  pextrq $0, %xmm13, %rax
  push %rax
  pextrq $1, %xmm13, %rax
  push %rax
  pextrq $0, %xmm12, %rax
  push %rax
  pextrq $1, %xmm12, %rax
  push %rax
  pextrq $0, %xmm11, %rax
  push %rax
  pextrq $1, %xmm11, %rax
  push %rax
  pextrq $0, %xmm10, %rax
  push %rax
  pextrq $1, %xmm10, %rax
  push %rax
  pextrq $0, %xmm9, %rax
  push %rax
  pextrq $1, %xmm9, %rax
  push %rax
  pextrq $0, %xmm8, %rax
  push %rax
  pextrq $1, %xmm8, %rax
  push %rax
  pextrq $0, %xmm7, %rax
  push %rax
  pextrq $1, %xmm7, %rax
  push %rax
  pextrq $0, %xmm6, %rax
  push %rax
  pextrq $1, %xmm6, %rax
  push %rax
  movq 0(%r9), %r14
  movq 8(%r9), %r13
  movq 16(%r9), %rax
  movq 24(%r9), %r11
  movq 32(%r9), %r10
  movq 40(%r9), %r8
  movq 48(%r9), %rbx
  movq 56(%r9), %r15
  movdqu 0(%r10), %xmm7
  mov $579005069656919567, %r12
  pinsrq $0, %r12, %xmm8
  mov $283686952306183, %r12
  pinsrq $1, %r12, %xmm8
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
  pshufb %xmm8, %xmm0
  movdqu %xmm0, %xmm11
  pshufb %xmm8, %xmm7
  mov $2, %r12
  pinsrd $0, %r12d, %xmm7
  pxor %xmm1, %xmm1
  cmp $0, %r11
  jbe L44
  mov %r11, %rcx
  shr $4, %rcx
  mov %rax, %r9
  cmp $0, %rcx
  je L46
  mov $0, %rdx
  jmp L49
.balign 16
L48:
  movdqu 0(%r9), %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
.balign 16
L49:
  cmp %rcx, %rdx
  jne L48
  jmp L47
L46:
L47:
  mov %r11, %rax
  and $15, %rax
  cmp $0, %rax
  jne L50
  jmp L51
L50:
  movdqu 0(%r9), %xmm2
  cmp $8, %rax
  jae L52
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
  jmp L53
L52:
  mov %rax, %rcx
  sub $8, %rcx
  shl $3, %rcx
  mov $1, %rdx
  shl %cl, %rdx
  sub $1, %rdx
  pextrq $1, %xmm2, %rcx
  and %rdx, %rcx
  pinsrq $1, %rcx, %xmm2
L53:
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
L51:
  jmp L45
L44:
L45:
  mov %r14, %rax
  mov %r13, %rcx
  cmp $0, %rcx
  jbe L54
  mov %rcx, %rsi
  and $15, %rsi
  shr $4, %rcx
  mov $0, %rdx
  mov %rax, %r9
  mov %rbx, %r10
  pxor %xmm10, %xmm10
  mov $1, %r12
  pinsrd $0, %r12d, %xmm10
  jmp L57
.balign 16
L56:
  movdqu 0(%r9), %xmm0
  movdqu %xmm0, %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
  movdqu %xmm0, %xmm3
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
  pxor %xmm0, %xmm3
  movdqu %xmm3, 0(%r10)
  add $1, %rdx
  add $16, %r9
  add $16, %r10
  paddd %xmm10, %xmm7
.balign 16
L57:
  cmp %rcx, %rdx
  jne L56
  cmp $0, %rsi
  jne L58
  jmp L59
L58:
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
  movdqu %xmm3, %xmm1
  movdqu 0(%r9), %xmm2
  cmp $8, %rax
  jae L60
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
  jmp L61
L60:
  mov %rax, %rcx
  sub $8, %rcx
  shl $3, %rcx
  mov $1, %rdx
  shl %cl, %rdx
  sub $1, %rdx
  pextrq $1, %xmm2, %rcx
  and %rdx, %rcx
  pinsrq $1, %rcx, %xmm2
L61:
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
L59:
  jmp L55
L54:
L55:
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
  jne L62
  mov $0, %rax
  jmp L63
L62:
  mov $1, %rax
L63:
  pextrq $1, %xmm0, %rdx
  cmp $18446744073709551615, %rdx
  jne L64
  mov $0, %rdx
  jmp L65
L64:
  mov $1, %rdx
L65:
  add %rdx, %rax
  mov %rax, %rdx
  pop %rax
  pinsrq $1, %rax, %xmm6
  pop %rax
  pinsrq $0, %rax, %xmm6
  pop %rax
  pinsrq $1, %rax, %xmm7
  pop %rax
  pinsrq $0, %rax, %xmm7
  pop %rax
  pinsrq $1, %rax, %xmm8
  pop %rax
  pinsrq $0, %rax, %xmm8
  pop %rax
  pinsrq $1, %rax, %xmm9
  pop %rax
  pinsrq $0, %rax, %xmm9
  pop %rax
  pinsrq $1, %rax, %xmm10
  pop %rax
  pinsrq $0, %rax, %xmm10
  pop %rax
  pinsrq $1, %rax, %xmm11
  pop %rax
  pinsrq $0, %rax, %xmm11
  pop %rax
  pinsrq $1, %rax, %xmm12
  pop %rax
  pinsrq $0, %rax, %xmm12
  pop %rax
  pinsrq $1, %rax, %xmm13
  pop %rax
  pinsrq $0, %rax, %xmm13
  pop %rax
  pinsrq $1, %rax, %xmm14
  pop %rax
  pinsrq $0, %rax, %xmm14
  pop %rax
  pinsrq $1, %rax, %xmm15
  pop %rax
  pinsrq $0, %rax, %xmm15
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

.global gcm128_decrypt
gcm128_decrypt:
  push %r15
  push %r14
  push %r13
  push %r12
  push %rsi
  push %rdi
  push %rbp
  push %rbx
  pextrq $0, %xmm15, %rax
  push %rax
  pextrq $1, %xmm15, %rax
  push %rax
  pextrq $0, %xmm14, %rax
  push %rax
  pextrq $1, %xmm14, %rax
  push %rax
  pextrq $0, %xmm13, %rax
  push %rax
  pextrq $1, %xmm13, %rax
  push %rax
  pextrq $0, %xmm12, %rax
  push %rax
  pextrq $1, %xmm12, %rax
  push %rax
  pextrq $0, %xmm11, %rax
  push %rax
  pextrq $1, %xmm11, %rax
  push %rax
  pextrq $0, %xmm10, %rax
  push %rax
  pextrq $1, %xmm10, %rax
  push %rax
  pextrq $0, %xmm9, %rax
  push %rax
  pextrq $1, %xmm9, %rax
  push %rax
  pextrq $0, %xmm8, %rax
  push %rax
  pextrq $1, %xmm8, %rax
  push %rax
  pextrq $0, %xmm7, %rax
  push %rax
  pextrq $1, %xmm7, %rax
  push %rax
  pextrq $0, %xmm6, %rax
  push %rax
  pextrq $1, %xmm6, %rax
  push %rax
  mov %rcx, %r14
  mov %rdx, %r13
  mov %r8, %rax
  mov %r9, %r11
  mov 264(%rsp), %r10
  mov 272(%rsp), %r8
  mov 280(%rsp), %rbx
  mov 288(%rsp), %r15
  movdqu 0(%r10), %xmm7
  mov $579005069656919567, %r12
  pinsrq $0, %r12, %xmm8
  mov $283686952306183, %r12
  pinsrq $1, %r12, %xmm8
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
  pshufb %xmm8, %xmm0
  movdqu %xmm0, %xmm11
  pshufb %xmm8, %xmm7
  mov $2, %r12
  pinsrd $0, %r12d, %xmm7
  pxor %xmm1, %xmm1
  cmp $0, %r11
  jbe L66
  mov %r11, %rcx
  shr $4, %rcx
  mov %rax, %r9
  cmp $0, %rcx
  je L68
  mov $0, %rdx
  jmp L71
.balign 16
L70:
  movdqu 0(%r9), %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
.balign 16
L71:
  cmp %rcx, %rdx
  jne L70
  jmp L69
L68:
L69:
  mov %r11, %rax
  and $15, %rax
  cmp $0, %rax
  jne L72
  jmp L73
L72:
  movdqu 0(%r9), %xmm2
  cmp $8, %rax
  jae L74
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
  jmp L75
L74:
  mov %rax, %rcx
  sub $8, %rcx
  shl $3, %rcx
  mov $1, %rdx
  shl %cl, %rdx
  sub $1, %rdx
  pextrq $1, %xmm2, %rcx
  and %rdx, %rcx
  pinsrq $1, %rcx, %xmm2
L75:
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
L73:
  jmp L67
L66:
L67:
  mov %r14, %rax
  mov %r13, %rcx
  cmp $0, %rcx
  jbe L76
  mov %rcx, %rsi
  and $15, %rsi
  shr $4, %rcx
  mov $0, %rdx
  mov %rax, %r9
  mov %rbx, %r10
  pxor %xmm10, %xmm10
  mov $1, %r12
  pinsrd $0, %r12d, %xmm10
  jmp L79
.balign 16
L78:
  movdqu 0(%r9), %xmm0
  movdqu %xmm0, %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
  movdqu %xmm0, %xmm3
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
  pxor %xmm0, %xmm3
  movdqu %xmm3, 0(%r10)
  add $1, %rdx
  add $16, %r9
  add $16, %r10
  paddd %xmm10, %xmm7
.balign 16
L79:
  cmp %rcx, %rdx
  jne L78
  cmp $0, %rsi
  jne L80
  jmp L81
L80:
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
  movdqu %xmm3, %xmm1
  movdqu 0(%r9), %xmm2
  cmp $8, %rax
  jae L82
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
  jmp L83
L82:
  mov %rax, %rcx
  sub $8, %rcx
  shl $3, %rcx
  mov $1, %rdx
  shl %cl, %rdx
  sub $1, %rdx
  pextrq $1, %xmm2, %rcx
  and %rdx, %rcx
  pinsrq $1, %rcx, %xmm2
L83:
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
L81:
  jmp L77
L76:
L77:
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
  jne L84
  mov $0, %rax
  jmp L85
L84:
  mov $1, %rax
L85:
  pextrq $1, %xmm0, %rdx
  cmp $18446744073709551615, %rdx
  jne L86
  mov $0, %rdx
  jmp L87
L86:
  mov $1, %rdx
L87:
  add %rdx, %rax
  pop %rdx
  pinsrq $1, %rdx, %xmm6
  pop %rdx
  pinsrq $0, %rdx, %xmm6
  pop %rdx
  pinsrq $1, %rdx, %xmm7
  pop %rdx
  pinsrq $0, %rdx, %xmm7
  pop %rdx
  pinsrq $1, %rdx, %xmm8
  pop %rdx
  pinsrq $0, %rdx, %xmm8
  pop %rdx
  pinsrq $1, %rdx, %xmm9
  pop %rdx
  pinsrq $0, %rdx, %xmm9
  pop %rdx
  pinsrq $1, %rdx, %xmm10
  pop %rdx
  pinsrq $0, %rdx, %xmm10
  pop %rdx
  pinsrq $1, %rdx, %xmm11
  pop %rdx
  pinsrq $0, %rdx, %xmm11
  pop %rdx
  pinsrq $1, %rdx, %xmm12
  pop %rdx
  pinsrq $0, %rdx, %xmm12
  pop %rdx
  pinsrq $1, %rdx, %xmm13
  pop %rdx
  pinsrq $0, %rdx, %xmm13
  pop %rdx
  pinsrq $1, %rdx, %xmm14
  pop %rdx
  pinsrq $0, %rdx, %xmm14
  pop %rdx
  pinsrq $1, %rdx, %xmm15
  pop %rdx
  pinsrq $0, %rdx, %xmm15
  pop %rbx
  pop %rbp
  pop %rdi
  pop %rsi
  pop %r12
  pop %r13
  pop %r14
  pop %r15
  ret

.global old_gcm256_encrypt
old_gcm256_encrypt:
  mov %rcx, %r9
  push %r15
  push %r14
  push %r13
  push %r12
  push %rsi
  push %rdi
  push %rbp
  push %rbx
  pextrq $0, %xmm15, %rax
  push %rax
  pextrq $1, %xmm15, %rax
  push %rax
  pextrq $0, %xmm14, %rax
  push %rax
  pextrq $1, %xmm14, %rax
  push %rax
  pextrq $0, %xmm13, %rax
  push %rax
  pextrq $1, %xmm13, %rax
  push %rax
  pextrq $0, %xmm12, %rax
  push %rax
  pextrq $1, %xmm12, %rax
  push %rax
  pextrq $0, %xmm11, %rax
  push %rax
  pextrq $1, %xmm11, %rax
  push %rax
  pextrq $0, %xmm10, %rax
  push %rax
  pextrq $1, %xmm10, %rax
  push %rax
  pextrq $0, %xmm9, %rax
  push %rax
  pextrq $1, %xmm9, %rax
  push %rax
  pextrq $0, %xmm8, %rax
  push %rax
  pextrq $1, %xmm8, %rax
  push %rax
  pextrq $0, %xmm7, %rax
  push %rax
  pextrq $1, %xmm7, %rax
  push %rax
  pextrq $0, %xmm6, %rax
  push %rax
  pextrq $1, %xmm6, %rax
  push %rax
  movq 0(%r9), %r14
  movq 8(%r9), %r13
  movq 16(%r9), %rax
  movq 24(%r9), %r11
  movq 32(%r9), %r10
  movq 40(%r9), %r8
  movq 48(%r9), %rbx
  movq 56(%r9), %r15
  movdqu 0(%r10), %xmm7
  mov $579005069656919567, %r12
  pinsrq $0, %r12, %xmm8
  mov $283686952306183, %r12
  pinsrq $1, %r12, %xmm8
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
  aesenc %xmm2, %xmm0
  movdqu 176(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 192(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 208(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 224(%r8), %xmm2
  aesenclast %xmm2, %xmm0
  pxor %xmm2, %xmm2
  pshufb %xmm8, %xmm0
  movdqu %xmm0, %xmm11
  pshufb %xmm8, %xmm7
  mov $2, %r12
  pinsrd $0, %r12d, %xmm7
  pxor %xmm1, %xmm1
  cmp $0, %r11
  jbe L88
  mov %r11, %rcx
  shr $4, %rcx
  mov %rax, %r9
  cmp $0, %rcx
  je L90
  mov $0, %rdx
  jmp L93
.balign 16
L92:
  movdqu 0(%r9), %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
.balign 16
L93:
  cmp %rcx, %rdx
  jne L92
  jmp L91
L90:
L91:
  mov %r11, %rax
  and $15, %rax
  cmp $0, %rax
  jne L94
  jmp L95
L94:
  movdqu 0(%r9), %xmm2
  cmp $8, %rax
  jae L96
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
  jmp L97
L96:
  mov %rax, %rcx
  sub $8, %rcx
  shl $3, %rcx
  mov $1, %rdx
  shl %cl, %rdx
  sub $1, %rdx
  pextrq $1, %xmm2, %rcx
  and %rdx, %rcx
  pinsrq $1, %rcx, %xmm2
L97:
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
L95:
  jmp L89
L88:
L89:
  mov %r14, %rax
  mov %r13, %rcx
  cmp $0, %rcx
  jbe L98
  mov %rcx, %rsi
  and $15, %rsi
  shr $4, %rcx
  mov %rcx, %rdx
  shr $2, %rdx
  and $3, %rcx
  cmp $0, %rdx
  jbe L100
  mov %rax, %r9
  mov %rbx, %r10
  pshufb %xmm8, %xmm7
  movdqu %xmm7, %xmm9
  mov $579005069656919567, %rax
  pinsrq $0, %rax, %xmm0
  mov $579005069656919567, %rax
  pinsrq $1, %rax, %xmm0
  pshufb %xmm0, %xmm9
  movdqu %xmm9, %xmm10
  pxor %xmm3, %xmm3
  mov $1, %rax
  pinsrd $2, %eax, %xmm3
  paddd %xmm3, %xmm9
  mov $3, %rax
  pinsrd $2, %eax, %xmm3
  mov $2, %rax
  pinsrd $0, %eax, %xmm3
  paddd %xmm3, %xmm10
  pshufb %xmm8, %xmm9
  pshufb %xmm8, %xmm10
  pextrq $0, %xmm7, %rdi
  mov $283686952306183, %rax
  pinsrq $0, %rax, %xmm0
  mov $579005069656919567, %rax
  pinsrq $1, %rax, %xmm0
  pxor %xmm15, %xmm15
  mov $4, %rax
  pinsrd $0, %eax, %xmm15
  mov $4, %rax
  pinsrd $2, %eax, %xmm15
  jmp L103
.balign 16
L102:
  pinsrq $0, %rdi, %xmm2
  pinsrq $0, %rdi, %xmm12
  pinsrq $0, %rdi, %xmm13
  pinsrq $0, %rdi, %xmm14
  shufpd $2, %xmm9, %xmm2
  shufpd $0, %xmm9, %xmm12
  shufpd $2, %xmm10, %xmm13
  shufpd $0, %xmm10, %xmm14
  pshufb %xmm0, %xmm9
  pshufb %xmm0, %xmm10
  movdqu 0(%r8), %xmm3
  movdqu 16(%r8), %xmm4
  movdqu 32(%r8), %xmm5
  movdqu 48(%r8), %xmm6
  paddd %xmm15, %xmm9
  paddd %xmm15, %xmm10
  pxor %xmm3, %xmm2
  pxor %xmm3, %xmm12
  pxor %xmm3, %xmm13
  pxor %xmm3, %xmm14
  pshufb %xmm0, %xmm9
  pshufb %xmm0, %xmm10
  aesenc %xmm4, %xmm2
  aesenc %xmm4, %xmm12
  aesenc %xmm4, %xmm13
  aesenc %xmm4, %xmm14
  aesenc %xmm5, %xmm2
  aesenc %xmm5, %xmm12
  aesenc %xmm5, %xmm13
  aesenc %xmm5, %xmm14
  aesenc %xmm6, %xmm2
  aesenc %xmm6, %xmm12
  aesenc %xmm6, %xmm13
  aesenc %xmm6, %xmm14
  movdqu 64(%r8), %xmm3
  movdqu 80(%r8), %xmm4
  movdqu 96(%r8), %xmm5
  movdqu 112(%r8), %xmm6
  aesenc %xmm3, %xmm2
  aesenc %xmm3, %xmm12
  aesenc %xmm3, %xmm13
  aesenc %xmm3, %xmm14
  aesenc %xmm4, %xmm2
  aesenc %xmm4, %xmm12
  aesenc %xmm4, %xmm13
  aesenc %xmm4, %xmm14
  aesenc %xmm5, %xmm2
  aesenc %xmm5, %xmm12
  aesenc %xmm5, %xmm13
  aesenc %xmm5, %xmm14
  aesenc %xmm6, %xmm2
  aesenc %xmm6, %xmm12
  aesenc %xmm6, %xmm13
  aesenc %xmm6, %xmm14
  movdqu 128(%r8), %xmm3
  movdqu 144(%r8), %xmm4
  movdqu 160(%r8), %xmm5
  aesenc %xmm3, %xmm2
  aesenc %xmm3, %xmm12
  aesenc %xmm3, %xmm13
  aesenc %xmm3, %xmm14
  aesenc %xmm4, %xmm2
  aesenc %xmm4, %xmm12
  aesenc %xmm4, %xmm13
  aesenc %xmm4, %xmm14
  movdqu %xmm5, %xmm3
  movdqu 176(%r8), %xmm4
  movdqu 192(%r8), %xmm5
  movdqu 208(%r8), %xmm6
  aesenc %xmm3, %xmm2
  aesenc %xmm3, %xmm12
  aesenc %xmm3, %xmm13
  aesenc %xmm3, %xmm14
  aesenc %xmm4, %xmm2
  aesenc %xmm4, %xmm12
  aesenc %xmm4, %xmm13
  aesenc %xmm4, %xmm14
  aesenc %xmm5, %xmm2
  aesenc %xmm5, %xmm12
  aesenc %xmm5, %xmm13
  aesenc %xmm5, %xmm14
  aesenc %xmm6, %xmm2
  aesenc %xmm6, %xmm12
  aesenc %xmm6, %xmm13
  aesenc %xmm6, %xmm14
  movdqu 224(%r8), %xmm5
  aesenclast %xmm5, %xmm2
  aesenclast %xmm5, %xmm12
  aesenclast %xmm5, %xmm13
  aesenclast %xmm5, %xmm14
  movdqu 0(%r9), %xmm7
  pxor %xmm7, %xmm2
  movdqu 16(%r9), %xmm7
  pxor %xmm7, %xmm12
  movdqu 32(%r9), %xmm7
  pxor %xmm7, %xmm13
  movdqu 48(%r9), %xmm7
  pxor %xmm7, %xmm14
  movdqu %xmm2, 0(%r10)
  movdqu %xmm12, 16(%r10)
  movdqu %xmm13, 32(%r10)
  movdqu %xmm14, 48(%r10)
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
  movdqu %xmm12, %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
  movdqu %xmm13, %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
  movdqu %xmm14, %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
  sub $1, %rdx
  add $64, %r9
  add $64, %r10
.balign 16
L103:
  cmp $0, %rdx
  ja L102
  movdqu %xmm9, %xmm7
  pinsrq $0, %rdi, %xmm7
  pshufb %xmm8, %xmm7
  mov %r9, %rax
  mov %r10, %rbx
  jmp L101
L100:
L101:
  mov $0, %rdx
  mov %rax, %r9
  mov %rbx, %r10
  pxor %xmm10, %xmm10
  mov $1, %r12
  pinsrd $0, %r12d, %xmm10
  jmp L105
.balign 16
L104:
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
  aesenc %xmm2, %xmm0
  movdqu 176(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 192(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 208(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 224(%r8), %xmm2
  aesenclast %xmm2, %xmm0
  pxor %xmm2, %xmm2
  movdqu 0(%r9), %xmm2
  pxor %xmm0, %xmm2
  movdqu %xmm2, 0(%r10)
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
.balign 16
L105:
  cmp %rcx, %rdx
  jne L104
  cmp $0, %rsi
  jne L106
  jmp L107
L106:
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
  aesenc %xmm2, %xmm0
  movdqu 176(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 192(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 208(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 224(%r8), %xmm2
  aesenclast %xmm2, %xmm0
  pxor %xmm2, %xmm2
  pxor %xmm0, %xmm1
  movdqu %xmm1, 0(%r10)
  mov %rsi, %rax
  mov %r10, %r9
  movdqu %xmm3, %xmm1
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
  jmp L99
L98:
L99:
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
  aesenc %xmm2, %xmm0
  movdqu 176(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 192(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 208(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 224(%r8), %xmm2
  aesenclast %xmm2, %xmm0
  pxor %xmm2, %xmm2
  pxor %xmm0, %xmm1
  movdqu %xmm1, 0(%r15)
  pop %rax
  pinsrq $1, %rax, %xmm6
  pop %rax
  pinsrq $0, %rax, %xmm6
  pop %rax
  pinsrq $1, %rax, %xmm7
  pop %rax
  pinsrq $0, %rax, %xmm7
  pop %rax
  pinsrq $1, %rax, %xmm8
  pop %rax
  pinsrq $0, %rax, %xmm8
  pop %rax
  pinsrq $1, %rax, %xmm9
  pop %rax
  pinsrq $0, %rax, %xmm9
  pop %rax
  pinsrq $1, %rax, %xmm10
  pop %rax
  pinsrq $0, %rax, %xmm10
  pop %rax
  pinsrq $1, %rax, %xmm11
  pop %rax
  pinsrq $0, %rax, %xmm11
  pop %rax
  pinsrq $1, %rax, %xmm12
  pop %rax
  pinsrq $0, %rax, %xmm12
  pop %rax
  pinsrq $1, %rax, %xmm13
  pop %rax
  pinsrq $0, %rax, %xmm13
  pop %rax
  pinsrq $1, %rax, %xmm14
  pop %rax
  pinsrq $0, %rax, %xmm14
  pop %rax
  pinsrq $1, %rax, %xmm15
  pop %rax
  pinsrq $0, %rax, %xmm15
  pop %rbx
  pop %rbp
  pop %rdi
  pop %rsi
  pop %r12
  pop %r13
  pop %r14
  pop %r15
  ret

.global gcm256_encrypt
gcm256_encrypt:
  push %r15
  push %r14
  push %r13
  push %r12
  push %rsi
  push %rdi
  push %rbp
  push %rbx
  pextrq $0, %xmm15, %rax
  push %rax
  pextrq $1, %xmm15, %rax
  push %rax
  pextrq $0, %xmm14, %rax
  push %rax
  pextrq $1, %xmm14, %rax
  push %rax
  pextrq $0, %xmm13, %rax
  push %rax
  pextrq $1, %xmm13, %rax
  push %rax
  pextrq $0, %xmm12, %rax
  push %rax
  pextrq $1, %xmm12, %rax
  push %rax
  pextrq $0, %xmm11, %rax
  push %rax
  pextrq $1, %xmm11, %rax
  push %rax
  pextrq $0, %xmm10, %rax
  push %rax
  pextrq $1, %xmm10, %rax
  push %rax
  pextrq $0, %xmm9, %rax
  push %rax
  pextrq $1, %xmm9, %rax
  push %rax
  pextrq $0, %xmm8, %rax
  push %rax
  pextrq $1, %xmm8, %rax
  push %rax
  pextrq $0, %xmm7, %rax
  push %rax
  pextrq $1, %xmm7, %rax
  push %rax
  pextrq $0, %xmm6, %rax
  push %rax
  pextrq $1, %xmm6, %rax
  push %rax
  mov %rcx, %r14
  mov %rdx, %r13
  mov %r8, %rax
  mov %r9, %r11
  mov 264(%rsp), %r10
  mov 272(%rsp), %r8
  mov 280(%rsp), %rbx
  mov 288(%rsp), %r15
  movdqu 0(%r10), %xmm7
  mov $579005069656919567, %r12
  pinsrq $0, %r12, %xmm8
  mov $283686952306183, %r12
  pinsrq $1, %r12, %xmm8
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
  aesenc %xmm2, %xmm0
  movdqu 176(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 192(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 208(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 224(%r8), %xmm2
  aesenclast %xmm2, %xmm0
  pxor %xmm2, %xmm2
  pshufb %xmm8, %xmm0
  movdqu %xmm0, %xmm11
  pshufb %xmm8, %xmm7
  mov $2, %r12
  pinsrd $0, %r12d, %xmm7
  pxor %xmm1, %xmm1
  cmp $0, %r11
  jbe L110
  mov %r11, %rcx
  shr $4, %rcx
  mov %rax, %r9
  cmp $0, %rcx
  je L112
  mov $0, %rdx
  jmp L115
.balign 16
L114:
  movdqu 0(%r9), %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
.balign 16
L115:
  cmp %rcx, %rdx
  jne L114
  jmp L113
L112:
L113:
  mov %r11, %rax
  and $15, %rax
  cmp $0, %rax
  jne L116
  jmp L117
L116:
  movdqu 0(%r9), %xmm2
  cmp $8, %rax
  jae L118
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
  jmp L119
L118:
  mov %rax, %rcx
  sub $8, %rcx
  shl $3, %rcx
  mov $1, %rdx
  shl %cl, %rdx
  sub $1, %rdx
  pextrq $1, %xmm2, %rcx
  and %rdx, %rcx
  pinsrq $1, %rcx, %xmm2
L119:
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
L117:
  jmp L111
L110:
L111:
  mov %r14, %rax
  mov %r13, %rcx
  cmp $0, %rcx
  jbe L120
  mov %rcx, %rsi
  and $15, %rsi
  shr $4, %rcx
  mov %rcx, %rdx
  shr $2, %rdx
  and $3, %rcx
  cmp $0, %rdx
  jbe L122
  mov %rax, %r9
  mov %rbx, %r10
  pshufb %xmm8, %xmm7
  movdqu %xmm7, %xmm9
  mov $579005069656919567, %rax
  pinsrq $0, %rax, %xmm0
  mov $579005069656919567, %rax
  pinsrq $1, %rax, %xmm0
  pshufb %xmm0, %xmm9
  movdqu %xmm9, %xmm10
  pxor %xmm3, %xmm3
  mov $1, %rax
  pinsrd $2, %eax, %xmm3
  paddd %xmm3, %xmm9
  mov $3, %rax
  pinsrd $2, %eax, %xmm3
  mov $2, %rax
  pinsrd $0, %eax, %xmm3
  paddd %xmm3, %xmm10
  pshufb %xmm8, %xmm9
  pshufb %xmm8, %xmm10
  pextrq $0, %xmm7, %rdi
  mov $283686952306183, %rax
  pinsrq $0, %rax, %xmm0
  mov $579005069656919567, %rax
  pinsrq $1, %rax, %xmm0
  pxor %xmm15, %xmm15
  mov $4, %rax
  pinsrd $0, %eax, %xmm15
  mov $4, %rax
  pinsrd $2, %eax, %xmm15
  jmp L125
.balign 16
L124:
  pinsrq $0, %rdi, %xmm2
  pinsrq $0, %rdi, %xmm12
  pinsrq $0, %rdi, %xmm13
  pinsrq $0, %rdi, %xmm14
  shufpd $2, %xmm9, %xmm2
  shufpd $0, %xmm9, %xmm12
  shufpd $2, %xmm10, %xmm13
  shufpd $0, %xmm10, %xmm14
  pshufb %xmm0, %xmm9
  pshufb %xmm0, %xmm10
  movdqu 0(%r8), %xmm3
  movdqu 16(%r8), %xmm4
  movdqu 32(%r8), %xmm5
  movdqu 48(%r8), %xmm6
  paddd %xmm15, %xmm9
  paddd %xmm15, %xmm10
  pxor %xmm3, %xmm2
  pxor %xmm3, %xmm12
  pxor %xmm3, %xmm13
  pxor %xmm3, %xmm14
  pshufb %xmm0, %xmm9
  pshufb %xmm0, %xmm10
  aesenc %xmm4, %xmm2
  aesenc %xmm4, %xmm12
  aesenc %xmm4, %xmm13
  aesenc %xmm4, %xmm14
  aesenc %xmm5, %xmm2
  aesenc %xmm5, %xmm12
  aesenc %xmm5, %xmm13
  aesenc %xmm5, %xmm14
  aesenc %xmm6, %xmm2
  aesenc %xmm6, %xmm12
  aesenc %xmm6, %xmm13
  aesenc %xmm6, %xmm14
  movdqu 64(%r8), %xmm3
  movdqu 80(%r8), %xmm4
  movdqu 96(%r8), %xmm5
  movdqu 112(%r8), %xmm6
  aesenc %xmm3, %xmm2
  aesenc %xmm3, %xmm12
  aesenc %xmm3, %xmm13
  aesenc %xmm3, %xmm14
  aesenc %xmm4, %xmm2
  aesenc %xmm4, %xmm12
  aesenc %xmm4, %xmm13
  aesenc %xmm4, %xmm14
  aesenc %xmm5, %xmm2
  aesenc %xmm5, %xmm12
  aesenc %xmm5, %xmm13
  aesenc %xmm5, %xmm14
  aesenc %xmm6, %xmm2
  aesenc %xmm6, %xmm12
  aesenc %xmm6, %xmm13
  aesenc %xmm6, %xmm14
  movdqu 128(%r8), %xmm3
  movdqu 144(%r8), %xmm4
  movdqu 160(%r8), %xmm5
  aesenc %xmm3, %xmm2
  aesenc %xmm3, %xmm12
  aesenc %xmm3, %xmm13
  aesenc %xmm3, %xmm14
  aesenc %xmm4, %xmm2
  aesenc %xmm4, %xmm12
  aesenc %xmm4, %xmm13
  aesenc %xmm4, %xmm14
  movdqu %xmm5, %xmm3
  movdqu 176(%r8), %xmm4
  movdqu 192(%r8), %xmm5
  movdqu 208(%r8), %xmm6
  aesenc %xmm3, %xmm2
  aesenc %xmm3, %xmm12
  aesenc %xmm3, %xmm13
  aesenc %xmm3, %xmm14
  aesenc %xmm4, %xmm2
  aesenc %xmm4, %xmm12
  aesenc %xmm4, %xmm13
  aesenc %xmm4, %xmm14
  aesenc %xmm5, %xmm2
  aesenc %xmm5, %xmm12
  aesenc %xmm5, %xmm13
  aesenc %xmm5, %xmm14
  aesenc %xmm6, %xmm2
  aesenc %xmm6, %xmm12
  aesenc %xmm6, %xmm13
  aesenc %xmm6, %xmm14
  movdqu 224(%r8), %xmm5
  aesenclast %xmm5, %xmm2
  aesenclast %xmm5, %xmm12
  aesenclast %xmm5, %xmm13
  aesenclast %xmm5, %xmm14
  movdqu 0(%r9), %xmm7
  pxor %xmm7, %xmm2
  movdqu 16(%r9), %xmm7
  pxor %xmm7, %xmm12
  movdqu 32(%r9), %xmm7
  pxor %xmm7, %xmm13
  movdqu 48(%r9), %xmm7
  pxor %xmm7, %xmm14
  movdqu %xmm2, 0(%r10)
  movdqu %xmm12, 16(%r10)
  movdqu %xmm13, 32(%r10)
  movdqu %xmm14, 48(%r10)
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
  movdqu %xmm12, %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
  movdqu %xmm13, %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
  movdqu %xmm14, %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
  sub $1, %rdx
  add $64, %r9
  add $64, %r10
.balign 16
L125:
  cmp $0, %rdx
  ja L124
  movdqu %xmm9, %xmm7
  pinsrq $0, %rdi, %xmm7
  pshufb %xmm8, %xmm7
  mov %r9, %rax
  mov %r10, %rbx
  jmp L123
L122:
L123:
  mov $0, %rdx
  mov %rax, %r9
  mov %rbx, %r10
  pxor %xmm10, %xmm10
  mov $1, %r12
  pinsrd $0, %r12d, %xmm10
  jmp L127
.balign 16
L126:
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
  aesenc %xmm2, %xmm0
  movdqu 176(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 192(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 208(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 224(%r8), %xmm2
  aesenclast %xmm2, %xmm0
  pxor %xmm2, %xmm2
  movdqu 0(%r9), %xmm2
  pxor %xmm0, %xmm2
  movdqu %xmm2, 0(%r10)
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
.balign 16
L127:
  cmp %rcx, %rdx
  jne L126
  cmp $0, %rsi
  jne L128
  jmp L129
L128:
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
  aesenc %xmm2, %xmm0
  movdqu 176(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 192(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 208(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 224(%r8), %xmm2
  aesenclast %xmm2, %xmm0
  pxor %xmm2, %xmm2
  pxor %xmm0, %xmm1
  movdqu %xmm1, 0(%r10)
  mov %rsi, %rax
  mov %r10, %r9
  movdqu %xmm3, %xmm1
  movdqu 0(%r9), %xmm2
  cmp $8, %rax
  jae L130
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
  jmp L131
L130:
  mov %rax, %rcx
  sub $8, %rcx
  shl $3, %rcx
  mov $1, %rdx
  shl %cl, %rdx
  sub $1, %rdx
  pextrq $1, %xmm2, %rcx
  and %rdx, %rcx
  pinsrq $1, %rcx, %xmm2
L131:
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
L129:
  jmp L121
L120:
L121:
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
  aesenc %xmm2, %xmm0
  movdqu 176(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 192(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 208(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 224(%r8), %xmm2
  aesenclast %xmm2, %xmm0
  pxor %xmm2, %xmm2
  pxor %xmm0, %xmm1
  movdqu %xmm1, 0(%r15)
  pop %rax
  pinsrq $1, %rax, %xmm6
  pop %rax
  pinsrq $0, %rax, %xmm6
  pop %rax
  pinsrq $1, %rax, %xmm7
  pop %rax
  pinsrq $0, %rax, %xmm7
  pop %rax
  pinsrq $1, %rax, %xmm8
  pop %rax
  pinsrq $0, %rax, %xmm8
  pop %rax
  pinsrq $1, %rax, %xmm9
  pop %rax
  pinsrq $0, %rax, %xmm9
  pop %rax
  pinsrq $1, %rax, %xmm10
  pop %rax
  pinsrq $0, %rax, %xmm10
  pop %rax
  pinsrq $1, %rax, %xmm11
  pop %rax
  pinsrq $0, %rax, %xmm11
  pop %rax
  pinsrq $1, %rax, %xmm12
  pop %rax
  pinsrq $0, %rax, %xmm12
  pop %rax
  pinsrq $1, %rax, %xmm13
  pop %rax
  pinsrq $0, %rax, %xmm13
  pop %rax
  pinsrq $1, %rax, %xmm14
  pop %rax
  pinsrq $0, %rax, %xmm14
  pop %rax
  pinsrq $1, %rax, %xmm15
  pop %rax
  pinsrq $0, %rax, %xmm15
  pop %rbx
  pop %rbp
  pop %rdi
  pop %rsi
  pop %r12
  pop %r13
  pop %r14
  pop %r15
  ret

.global old_gcm256_decrypt
old_gcm256_decrypt:
  mov %rcx, %r9
  push %r15
  push %r14
  push %r13
  push %r12
  push %rsi
  push %rdi
  push %rbp
  push %rbx
  pextrq $0, %xmm15, %rax
  push %rax
  pextrq $1, %xmm15, %rax
  push %rax
  pextrq $0, %xmm14, %rax
  push %rax
  pextrq $1, %xmm14, %rax
  push %rax
  pextrq $0, %xmm13, %rax
  push %rax
  pextrq $1, %xmm13, %rax
  push %rax
  pextrq $0, %xmm12, %rax
  push %rax
  pextrq $1, %xmm12, %rax
  push %rax
  pextrq $0, %xmm11, %rax
  push %rax
  pextrq $1, %xmm11, %rax
  push %rax
  pextrq $0, %xmm10, %rax
  push %rax
  pextrq $1, %xmm10, %rax
  push %rax
  pextrq $0, %xmm9, %rax
  push %rax
  pextrq $1, %xmm9, %rax
  push %rax
  pextrq $0, %xmm8, %rax
  push %rax
  pextrq $1, %xmm8, %rax
  push %rax
  pextrq $0, %xmm7, %rax
  push %rax
  pextrq $1, %xmm7, %rax
  push %rax
  pextrq $0, %xmm6, %rax
  push %rax
  pextrq $1, %xmm6, %rax
  push %rax
  movq 0(%r9), %r14
  movq 8(%r9), %r13
  movq 16(%r9), %rax
  movq 24(%r9), %r11
  movq 32(%r9), %r10
  movq 40(%r9), %r8
  movq 48(%r9), %rbx
  movq 56(%r9), %r15
  movdqu 0(%r10), %xmm7
  mov $579005069656919567, %r12
  pinsrq $0, %r12, %xmm8
  mov $283686952306183, %r12
  pinsrq $1, %r12, %xmm8
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
  aesenc %xmm2, %xmm0
  movdqu 176(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 192(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 208(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 224(%r8), %xmm2
  aesenclast %xmm2, %xmm0
  pxor %xmm2, %xmm2
  pshufb %xmm8, %xmm0
  movdqu %xmm0, %xmm11
  pshufb %xmm8, %xmm7
  mov $2, %r12
  pinsrd $0, %r12d, %xmm7
  pxor %xmm1, %xmm1
  cmp $0, %r11
  jbe L132
  mov %r11, %rcx
  shr $4, %rcx
  mov %rax, %r9
  cmp $0, %rcx
  je L134
  mov $0, %rdx
  jmp L137
.balign 16
L136:
  movdqu 0(%r9), %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
.balign 16
L137:
  cmp %rcx, %rdx
  jne L136
  jmp L135
L134:
L135:
  mov %r11, %rax
  and $15, %rax
  cmp $0, %rax
  jne L138
  jmp L139
L138:
  movdqu 0(%r9), %xmm2
  cmp $8, %rax
  jae L140
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
  jmp L141
L140:
  mov %rax, %rcx
  sub $8, %rcx
  shl $3, %rcx
  mov $1, %rdx
  shl %cl, %rdx
  sub $1, %rdx
  pextrq $1, %xmm2, %rcx
  and %rdx, %rcx
  pinsrq $1, %rcx, %xmm2
L141:
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
L139:
  jmp L133
L132:
L133:
  mov %r14, %rax
  mov %r13, %rcx
  cmp $0, %rcx
  jbe L142
  mov %rcx, %rsi
  and $15, %rsi
  shr $4, %rcx
  mov $0, %rdx
  mov %rax, %r9
  mov %rbx, %r10
  pxor %xmm10, %xmm10
  mov $1, %r12
  pinsrd $0, %r12d, %xmm10
  jmp L145
.balign 16
L144:
  movdqu 0(%r9), %xmm0
  movdqu %xmm0, %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
  movdqu %xmm0, %xmm3
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
  aesenc %xmm2, %xmm0
  movdqu 176(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 192(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 208(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 224(%r8), %xmm2
  aesenclast %xmm2, %xmm0
  pxor %xmm2, %xmm2
  pxor %xmm0, %xmm3
  movdqu %xmm3, 0(%r10)
  add $1, %rdx
  add $16, %r9
  add $16, %r10
  paddd %xmm10, %xmm7
.balign 16
L145:
  cmp %rcx, %rdx
  jne L144
  cmp $0, %rsi
  jne L146
  jmp L147
L146:
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
  aesenc %xmm2, %xmm0
  movdqu 176(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 192(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 208(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 224(%r8), %xmm2
  aesenclast %xmm2, %xmm0
  pxor %xmm2, %xmm2
  pxor %xmm0, %xmm1
  movdqu %xmm1, 0(%r10)
  mov %rsi, %rax
  movdqu %xmm3, %xmm1
  movdqu 0(%r9), %xmm2
  cmp $8, %rax
  jae L148
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
  jmp L149
L148:
  mov %rax, %rcx
  sub $8, %rcx
  shl $3, %rcx
  mov $1, %rdx
  shl %cl, %rdx
  sub $1, %rdx
  pextrq $1, %xmm2, %rcx
  and %rdx, %rcx
  pinsrq $1, %rcx, %xmm2
L149:
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
L147:
  jmp L143
L142:
L143:
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
  aesenc %xmm2, %xmm0
  movdqu 176(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 192(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 208(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 224(%r8), %xmm2
  aesenclast %xmm2, %xmm0
  pxor %xmm2, %xmm2
  pxor %xmm0, %xmm1
  movdqu 0(%r15), %xmm0
  pcmpeqd %xmm1, %xmm0
  pextrq $0, %xmm0, %rdx
  cmp $18446744073709551615, %rdx
  jne L150
  mov $0, %rax
  jmp L151
L150:
  mov $1, %rax
L151:
  pextrq $1, %xmm0, %rdx
  cmp $18446744073709551615, %rdx
  jne L152
  mov $0, %rdx
  jmp L153
L152:
  mov $1, %rdx
L153:
  add %rdx, %rax
  mov %rax, %rdx
  pop %rax
  pinsrq $1, %rax, %xmm6
  pop %rax
  pinsrq $0, %rax, %xmm6
  pop %rax
  pinsrq $1, %rax, %xmm7
  pop %rax
  pinsrq $0, %rax, %xmm7
  pop %rax
  pinsrq $1, %rax, %xmm8
  pop %rax
  pinsrq $0, %rax, %xmm8
  pop %rax
  pinsrq $1, %rax, %xmm9
  pop %rax
  pinsrq $0, %rax, %xmm9
  pop %rax
  pinsrq $1, %rax, %xmm10
  pop %rax
  pinsrq $0, %rax, %xmm10
  pop %rax
  pinsrq $1, %rax, %xmm11
  pop %rax
  pinsrq $0, %rax, %xmm11
  pop %rax
  pinsrq $1, %rax, %xmm12
  pop %rax
  pinsrq $0, %rax, %xmm12
  pop %rax
  pinsrq $1, %rax, %xmm13
  pop %rax
  pinsrq $0, %rax, %xmm13
  pop %rax
  pinsrq $1, %rax, %xmm14
  pop %rax
  pinsrq $0, %rax, %xmm14
  pop %rax
  pinsrq $1, %rax, %xmm15
  pop %rax
  pinsrq $0, %rax, %xmm15
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

.global gcm256_decrypt
gcm256_decrypt:
  push %r15
  push %r14
  push %r13
  push %r12
  push %rsi
  push %rdi
  push %rbp
  push %rbx
  pextrq $0, %xmm15, %rax
  push %rax
  pextrq $1, %xmm15, %rax
  push %rax
  pextrq $0, %xmm14, %rax
  push %rax
  pextrq $1, %xmm14, %rax
  push %rax
  pextrq $0, %xmm13, %rax
  push %rax
  pextrq $1, %xmm13, %rax
  push %rax
  pextrq $0, %xmm12, %rax
  push %rax
  pextrq $1, %xmm12, %rax
  push %rax
  pextrq $0, %xmm11, %rax
  push %rax
  pextrq $1, %xmm11, %rax
  push %rax
  pextrq $0, %xmm10, %rax
  push %rax
  pextrq $1, %xmm10, %rax
  push %rax
  pextrq $0, %xmm9, %rax
  push %rax
  pextrq $1, %xmm9, %rax
  push %rax
  pextrq $0, %xmm8, %rax
  push %rax
  pextrq $1, %xmm8, %rax
  push %rax
  pextrq $0, %xmm7, %rax
  push %rax
  pextrq $1, %xmm7, %rax
  push %rax
  pextrq $0, %xmm6, %rax
  push %rax
  pextrq $1, %xmm6, %rax
  push %rax
  mov %rcx, %r14
  mov %rdx, %r13
  mov %r8, %rax
  mov %r9, %r11
  mov 264(%rsp), %r10
  mov 272(%rsp), %r8
  mov 280(%rsp), %rbx
  mov 288(%rsp), %r15
  movdqu 0(%r10), %xmm7
  mov $579005069656919567, %r12
  pinsrq $0, %r12, %xmm8
  mov $283686952306183, %r12
  pinsrq $1, %r12, %xmm8
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
  aesenc %xmm2, %xmm0
  movdqu 176(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 192(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 208(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 224(%r8), %xmm2
  aesenclast %xmm2, %xmm0
  pxor %xmm2, %xmm2
  pshufb %xmm8, %xmm0
  movdqu %xmm0, %xmm11
  pshufb %xmm8, %xmm7
  mov $2, %r12
  pinsrd $0, %r12d, %xmm7
  pxor %xmm1, %xmm1
  cmp $0, %r11
  jbe L154
  mov %r11, %rcx
  shr $4, %rcx
  mov %rax, %r9
  cmp $0, %rcx
  je L156
  mov $0, %rdx
  jmp L159
.balign 16
L158:
  movdqu 0(%r9), %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
.balign 16
L159:
  cmp %rcx, %rdx
  jne L158
  jmp L157
L156:
L157:
  mov %r11, %rax
  and $15, %rax
  cmp $0, %rax
  jne L160
  jmp L161
L160:
  movdqu 0(%r9), %xmm2
  cmp $8, %rax
  jae L162
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
  jmp L163
L162:
  mov %rax, %rcx
  sub $8, %rcx
  shl $3, %rcx
  mov $1, %rdx
  shl %cl, %rdx
  sub $1, %rdx
  pextrq $1, %xmm2, %rcx
  and %rdx, %rcx
  pinsrq $1, %rcx, %xmm2
L163:
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
L161:
  jmp L155
L154:
L155:
  mov %r14, %rax
  mov %r13, %rcx
  cmp $0, %rcx
  jbe L164
  mov %rcx, %rsi
  and $15, %rsi
  shr $4, %rcx
  mov $0, %rdx
  mov %rax, %r9
  mov %rbx, %r10
  pxor %xmm10, %xmm10
  mov $1, %r12
  pinsrd $0, %r12d, %xmm10
  jmp L167
.balign 16
L166:
  movdqu 0(%r9), %xmm0
  movdqu %xmm0, %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
  movdqu %xmm0, %xmm3
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
  aesenc %xmm2, %xmm0
  movdqu 176(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 192(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 208(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 224(%r8), %xmm2
  aesenclast %xmm2, %xmm0
  pxor %xmm2, %xmm2
  pxor %xmm0, %xmm3
  movdqu %xmm3, 0(%r10)
  add $1, %rdx
  add $16, %r9
  add $16, %r10
  paddd %xmm10, %xmm7
.balign 16
L167:
  cmp %rcx, %rdx
  jne L166
  cmp $0, %rsi
  jne L168
  jmp L169
L168:
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
  aesenc %xmm2, %xmm0
  movdqu 176(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 192(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 208(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 224(%r8), %xmm2
  aesenclast %xmm2, %xmm0
  pxor %xmm2, %xmm2
  pxor %xmm0, %xmm1
  movdqu %xmm1, 0(%r10)
  mov %rsi, %rax
  movdqu %xmm3, %xmm1
  movdqu 0(%r9), %xmm2
  cmp $8, %rax
  jae L170
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
  jmp L171
L170:
  mov %rax, %rcx
  sub $8, %rcx
  shl $3, %rcx
  mov $1, %rdx
  shl %cl, %rdx
  sub $1, %rdx
  pextrq $1, %xmm2, %rcx
  and %rdx, %rcx
  pinsrq $1, %rcx, %xmm2
L171:
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
L169:
  jmp L165
L164:
L165:
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
  aesenc %xmm2, %xmm0
  movdqu 176(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 192(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 208(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 224(%r8), %xmm2
  aesenclast %xmm2, %xmm0
  pxor %xmm2, %xmm2
  pxor %xmm0, %xmm1
  movdqu 0(%r15), %xmm0
  pcmpeqd %xmm1, %xmm0
  pextrq $0, %xmm0, %rdx
  cmp $18446744073709551615, %rdx
  jne L172
  mov $0, %rax
  jmp L173
L172:
  mov $1, %rax
L173:
  pextrq $1, %xmm0, %rdx
  cmp $18446744073709551615, %rdx
  jne L174
  mov $0, %rdx
  jmp L175
L174:
  mov $1, %rdx
L175:
  add %rdx, %rax
  pop %rdx
  pinsrq $1, %rdx, %xmm6
  pop %rdx
  pinsrq $0, %rdx, %xmm6
  pop %rdx
  pinsrq $1, %rdx, %xmm7
  pop %rdx
  pinsrq $0, %rdx, %xmm7
  pop %rdx
  pinsrq $1, %rdx, %xmm8
  pop %rdx
  pinsrq $0, %rdx, %xmm8
  pop %rdx
  pinsrq $1, %rdx, %xmm9
  pop %rdx
  pinsrq $0, %rdx, %xmm9
  pop %rdx
  pinsrq $1, %rdx, %xmm10
  pop %rdx
  pinsrq $0, %rdx, %xmm10
  pop %rdx
  pinsrq $1, %rdx, %xmm11
  pop %rdx
  pinsrq $0, %rdx, %xmm11
  pop %rdx
  pinsrq $1, %rdx, %xmm12
  pop %rdx
  pinsrq $0, %rdx, %xmm12
  pop %rdx
  pinsrq $1, %rdx, %xmm13
  pop %rdx
  pinsrq $0, %rdx, %xmm13
  pop %rdx
  pinsrq $1, %rdx, %xmm14
  pop %rdx
  pinsrq $0, %rdx, %xmm14
  pop %rdx
  pinsrq $1, %rdx, %xmm15
  pop %rdx
  pinsrq $0, %rdx, %xmm15
  pop %rbx
  pop %rbp
  pop %rdi
  pop %rsi
  pop %r12
  pop %r13
  pop %r14
  pop %r15
  ret

.global gcm128_encrypt_opt
gcm128_encrypt_opt:
  push %r15
  push %r14
  push %r13
  push %r12
  push %rsi
  push %rdi
  push %rbp
  push %rbx
  pextrq $0, %xmm15, %rax
  push %rax
  pextrq $1, %xmm15, %rax
  push %rax
  pextrq $0, %xmm14, %rax
  push %rax
  pextrq $1, %xmm14, %rax
  push %rax
  pextrq $0, %xmm13, %rax
  push %rax
  pextrq $1, %xmm13, %rax
  push %rax
  pextrq $0, %xmm12, %rax
  push %rax
  pextrq $1, %xmm12, %rax
  push %rax
  pextrq $0, %xmm11, %rax
  push %rax
  pextrq $1, %xmm11, %rax
  push %rax
  pextrq $0, %xmm10, %rax
  push %rax
  pextrq $1, %xmm10, %rax
  push %rax
  pextrq $0, %xmm9, %rax
  push %rax
  pextrq $1, %xmm9, %rax
  push %rax
  pextrq $0, %xmm8, %rax
  push %rax
  pextrq $1, %xmm8, %rax
  push %rax
  pextrq $0, %xmm7, %rax
  push %rax
  pextrq $1, %xmm7, %rax
  push %rax
  pextrq $0, %xmm6, %rax
  push %rax
  pextrq $1, %xmm6, %rax
  push %rax
  mov %rcx, %rdi
  mov %rdx, %rsi
  mov %r8, %rdx
  mov %r9, %rcx
  mov 264(%rsp), %r8
  mov 272(%rsp), %r9
  mov 352(%rsp), %rbp
  mov %r8, %r13
  mov %r9, %r14
  mov $579005069656919567, %r12
  pinsrq $0, %r12, %xmm8
  mov $283686952306183, %r12
  pinsrq $1, %r12, %xmm8
  mov %rdi, %rax
  mov %rcx, %r8
  mov %rdx, %r11
  movdqu 32(%r9), %xmm11
  pxor %xmm1, %xmm1
  mov %r11, %rcx
  cmp $0, %rcx
  je L176
  mov $0, %rdx
  mov %rax, %r9
  jmp L179
.balign 16
L178:
  movdqu 0(%r9), %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
.balign 16
L179:
  cmp %rcx, %rdx
  jne L178
  jmp L177
L176:
L177:
  imul $16, %r11
  cmp %r11, %rsi
  jbe L180
  mov 280(%rsp), %r11
  movdqu 0(%r11), %xmm2
  mov %rsi, %rax
  and $15, %rax
  cmp $8, %rax
  jae L182
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
  jmp L183
L182:
  mov %rax, %rcx
  sub $8, %rcx
  shl $3, %rcx
  mov $1, %rdx
  shl %cl, %rdx
  sub $1, %rdx
  pextrq $1, %xmm2, %rcx
  and %rdx, %rcx
  pinsrq $1, %rcx, %xmm2
L183:
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
  jmp L181
L180:
L181:
  mov %rsi, %r15
  mov 288(%rsp), %rdi
  mov 296(%rsp), %rsi
  mov 304(%rsp), %rdx
  mov %r8, %rcx
  mov %r13, %r8
  mov %r14, %r9
  movdqu %xmm1, %xmm8
  cmp $0, %rdx
  jne L184
  lea 32(%r9), %r9
  movdqu 0(%r8), %xmm1
  mov $579005069656919567, %r12
  pinsrq $0, %r12, %xmm0
  mov $283686952306183, %r12
  pinsrq $1, %r12, %xmm0
  vpshufb %xmm0, %xmm1, %xmm1
  mov $2, %rbx
  pinsrd $0, %ebx, %xmm1
  vpshufb %xmm0, %xmm1, %xmm1
  movdqu %xmm1, 0(%r8)
  jmp L185
L184:
  mov $579005069656919567, %r12
  pinsrq $0, %r12, %xmm0
  mov $283686952306183, %r12
  pinsrq $1, %r12, %xmm0
  movdqu 0(%r8), %xmm1
  vpshufb %xmm0, %xmm8, %xmm8
  movdqu %xmm8, 0(%r8)
  add $128, %rcx
  vpshufb %xmm0, %xmm1, %xmm1
  mov $2, %rbx
  pinsrd $0, %ebx, %xmm1
  vpshufb %xmm0, %xmm1, %xmm1
  lea 96(%rsi), %r14
  movdqu -128(%rcx), %xmm4
  pxor %xmm2, %xmm2
  mov $72057594037927936, %r11
  pinsrq $1, %r11, %xmm2
  movdqu -112(%rcx), %xmm15
  mov %rcx, %r12
  sub $96, %r12
  vpxor %xmm4, %xmm1, %xmm9
  vpaddd %xmm2, %xmm1, %xmm10
  vpaddd %xmm2, %xmm10, %xmm11
  vpxor %xmm4, %xmm10, %xmm10
  vpaddd %xmm2, %xmm11, %xmm12
  vpxor %xmm4, %xmm11, %xmm11
  vpaddd %xmm2, %xmm12, %xmm13
  vpxor %xmm4, %xmm12, %xmm12
  vpaddd %xmm2, %xmm13, %xmm14
  vpxor %xmm4, %xmm13, %xmm13
  vpaddd %xmm2, %xmm14, %xmm1
  vpxor %xmm4, %xmm14, %xmm14
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -96(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -80(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -64(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -48(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -32(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -16(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu 0(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu 16(%rcx), %xmm15
  movdqu 32(%rcx), %xmm3
  vaesenc %xmm15, %xmm9, %xmm9
  vpxor 0(%rdi), %xmm3, %xmm4
  vaesenc %xmm15, %xmm10, %xmm10
  vpxor 16(%rdi), %xmm3, %xmm5
  vaesenc %xmm15, %xmm11, %xmm11
  vpxor 32(%rdi), %xmm3, %xmm6
  vaesenc %xmm15, %xmm12, %xmm12
  vpxor 48(%rdi), %xmm3, %xmm8
  vaesenc %xmm15, %xmm13, %xmm13
  vpxor 64(%rdi), %xmm3, %xmm2
  vaesenc %xmm15, %xmm14, %xmm14
  vpxor 80(%rdi), %xmm3, %xmm3
  lea 96(%rdi), %rdi
  vaesenclast %xmm4, %xmm9, %xmm9
  vaesenclast %xmm5, %xmm10, %xmm10
  vaesenclast %xmm6, %xmm11, %xmm11
  vaesenclast %xmm8, %xmm12, %xmm12
  vaesenclast %xmm2, %xmm13, %xmm13
  vaesenclast %xmm3, %xmm14, %xmm14
  movdqu %xmm9, 0(%rsi)
  movdqu %xmm10, 16(%rsi)
  movdqu %xmm11, 32(%rsi)
  movdqu %xmm12, 48(%rsi)
  movdqu %xmm13, 64(%rsi)
  movdqu %xmm14, 80(%rsi)
  lea 96(%rsi), %rsi
  vpshufb %xmm0, %xmm9, %xmm8
  vpshufb %xmm0, %xmm10, %xmm2
  movdqu %xmm8, 112(%rbp)
  vpshufb %xmm0, %xmm11, %xmm4
  movdqu %xmm2, 96(%rbp)
  vpshufb %xmm0, %xmm12, %xmm5
  movdqu %xmm4, 80(%rbp)
  vpshufb %xmm0, %xmm13, %xmm6
  movdqu %xmm5, 64(%rbp)
  vpshufb %xmm0, %xmm14, %xmm7
  movdqu %xmm6, 48(%rbp)
  movdqu -128(%rcx), %xmm4
  pxor %xmm2, %xmm2
  mov $72057594037927936, %r11
  pinsrq $1, %r11, %xmm2
  movdqu -112(%rcx), %xmm15
  mov %rcx, %r12
  sub $96, %r12
  vpxor %xmm4, %xmm1, %xmm9
  vpaddd %xmm2, %xmm1, %xmm10
  vpaddd %xmm2, %xmm10, %xmm11
  vpxor %xmm4, %xmm10, %xmm10
  vpaddd %xmm2, %xmm11, %xmm12
  vpxor %xmm4, %xmm11, %xmm11
  vpaddd %xmm2, %xmm12, %xmm13
  vpxor %xmm4, %xmm12, %xmm12
  vpaddd %xmm2, %xmm13, %xmm14
  vpxor %xmm4, %xmm13, %xmm13
  vpaddd %xmm2, %xmm14, %xmm1
  vpxor %xmm4, %xmm14, %xmm14
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -96(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -80(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -64(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -48(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -32(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -16(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu 0(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu 16(%rcx), %xmm15
  movdqu 32(%rcx), %xmm3
  vaesenc %xmm15, %xmm9, %xmm9
  vpxor 0(%rdi), %xmm3, %xmm4
  vaesenc %xmm15, %xmm10, %xmm10
  vpxor 16(%rdi), %xmm3, %xmm5
  vaesenc %xmm15, %xmm11, %xmm11
  vpxor 32(%rdi), %xmm3, %xmm6
  vaesenc %xmm15, %xmm12, %xmm12
  vpxor 48(%rdi), %xmm3, %xmm8
  vaesenc %xmm15, %xmm13, %xmm13
  vpxor 64(%rdi), %xmm3, %xmm2
  vaesenc %xmm15, %xmm14, %xmm14
  vpxor 80(%rdi), %xmm3, %xmm3
  lea 96(%rdi), %rdi
  vaesenclast %xmm4, %xmm9, %xmm9
  vaesenclast %xmm5, %xmm10, %xmm10
  vaesenclast %xmm6, %xmm11, %xmm11
  vaesenclast %xmm8, %xmm12, %xmm12
  vaesenclast %xmm2, %xmm13, %xmm13
  vaesenclast %xmm3, %xmm14, %xmm14
  movdqu %xmm9, 0(%rsi)
  movdqu %xmm10, 16(%rsi)
  movdqu %xmm11, 32(%rsi)
  movdqu %xmm12, 48(%rsi)
  movdqu %xmm13, 64(%rsi)
  movdqu %xmm14, 80(%rsi)
  lea 96(%rsi), %rsi
  sub $12, %rdx
  movdqu 0(%r8), %xmm8
  lea 32(%r9), %r9
  pxor %xmm2, %xmm2
  mov $72057594037927936, %r11
  pinsrq $1, %r11, %xmm2
  vpxor %xmm4, %xmm4, %xmm4
  movdqu -128(%rcx), %xmm15
  vpaddd %xmm2, %xmm1, %xmm10
  vpaddd %xmm2, %xmm10, %xmm11
  vpaddd %xmm2, %xmm11, %xmm12
  vpaddd %xmm2, %xmm12, %xmm13
  vpaddd %xmm2, %xmm13, %xmm14
  vpxor %xmm15, %xmm1, %xmm9
  movdqu %xmm4, 16(%rbp)
  mov $14, %rbx
  jmp L187
.balign 16
L186:
  add $6, %rbx
  cmp $256, %rbx
  jb L188
  mov $579005069656919567, %r11
  pinsrq $0, %r11, %xmm0
  mov $283686952306183, %r11
  pinsrq $1, %r11, %xmm0
  vpshufb %xmm0, %xmm1, %xmm6
  pxor %xmm5, %xmm5
  mov $1, %r11
  pinsrq $0, %r11, %xmm5
  vpaddd %xmm5, %xmm6, %xmm10
  pxor %xmm5, %xmm5
  mov $2, %r11
  pinsrq $0, %r11, %xmm5
  vpaddd %xmm5, %xmm6, %xmm11
  movdqu -32(%r9), %xmm3
  vpaddd %xmm5, %xmm10, %xmm12
  vpshufb %xmm0, %xmm10, %xmm10
  vpaddd %xmm5, %xmm11, %xmm13
  vpshufb %xmm0, %xmm11, %xmm11
  vpxor %xmm15, %xmm10, %xmm10
  vpaddd %xmm5, %xmm12, %xmm14
  vpshufb %xmm0, %xmm12, %xmm12
  vpxor %xmm15, %xmm11, %xmm11
  vpaddd %xmm5, %xmm13, %xmm1
  vpshufb %xmm0, %xmm13, %xmm13
  vpshufb %xmm0, %xmm14, %xmm14
  vpshufb %xmm0, %xmm1, %xmm1
  sub $256, %rbx
  jmp L189
L188:
  movdqu -32(%r9), %xmm3
  vpaddd %xmm14, %xmm2, %xmm1
  vpxor %xmm15, %xmm10, %xmm10
  vpxor %xmm15, %xmm11, %xmm11
L189:
  movdqu %xmm1, 0(%r8)
  vpclmulqdq $16, %xmm3, %xmm7, %xmm5
  vpxor %xmm15, %xmm12, %xmm12
  movdqu -112(%rcx), %xmm2
  vpclmulqdq $1, %xmm3, %xmm7, %xmm6
  vaesenc %xmm2, %xmm9, %xmm9
  movdqu 48(%rbp), %xmm0
  vpxor %xmm15, %xmm13, %xmm13
  vpclmulqdq $0, %xmm3, %xmm7, %xmm1
  vaesenc %xmm2, %xmm10, %xmm10
  vpxor %xmm15, %xmm14, %xmm14
  vpclmulqdq $17, %xmm3, %xmm7, %xmm7
  vaesenc %xmm2, %xmm11, %xmm11
  movdqu -16(%r9), %xmm3
  vaesenc %xmm2, %xmm12, %xmm12
  vpxor %xmm5, %xmm6, %xmm6
  vpclmulqdq $0, %xmm3, %xmm0, %xmm5
  vpxor %xmm4, %xmm8, %xmm8
  vaesenc %xmm2, %xmm13, %xmm13
  vpxor %xmm5, %xmm1, %xmm4
  vpclmulqdq $16, %xmm3, %xmm0, %xmm1
  vaesenc %xmm2, %xmm14, %xmm14
  movdqu -96(%rcx), %xmm15
  vpclmulqdq $1, %xmm3, %xmm0, %xmm2
  vaesenc %xmm15, %xmm9, %xmm9
  vpxor 16(%rbp), %xmm8, %xmm8
  vpclmulqdq $17, %xmm3, %xmm0, %xmm3
  movdqu 64(%rbp), %xmm0
  vaesenc %xmm15, %xmm10, %xmm10
  movbeq 88(%r14), %r13
  vaesenc %xmm15, %xmm11, %xmm11
  movbeq 80(%r14), %r12
  vaesenc %xmm15, %xmm12, %xmm12
  movq %r13, 32(%rbp)
  vaesenc %xmm15, %xmm13, %xmm13
  movq %r12, 40(%rbp)
  movdqu 16(%r9), %xmm5
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -80(%rcx), %xmm15
  vpxor %xmm1, %xmm6, %xmm6
  vpclmulqdq $0, %xmm5, %xmm0, %xmm1
  vaesenc %xmm15, %xmm9, %xmm9
  vpxor %xmm2, %xmm6, %xmm6
  vpclmulqdq $16, %xmm5, %xmm0, %xmm2
  vaesenc %xmm15, %xmm10, %xmm10
  vpxor %xmm3, %xmm7, %xmm7
  vpclmulqdq $1, %xmm5, %xmm0, %xmm3
  vaesenc %xmm15, %xmm11, %xmm11
  vpclmulqdq $17, %xmm5, %xmm0, %xmm5
  movdqu 80(%rbp), %xmm0
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vpxor %xmm1, %xmm4, %xmm4
  movdqu 32(%r9), %xmm1
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -64(%rcx), %xmm15
  vpxor %xmm2, %xmm6, %xmm6
  vpclmulqdq $0, %xmm1, %xmm0, %xmm2
  vaesenc %xmm15, %xmm9, %xmm9
  vpxor %xmm3, %xmm6, %xmm6
  vpclmulqdq $16, %xmm1, %xmm0, %xmm3
  vaesenc %xmm15, %xmm10, %xmm10
  movbeq 72(%r14), %r13
  vpxor %xmm5, %xmm7, %xmm7
  vpclmulqdq $1, %xmm1, %xmm0, %xmm5
  vaesenc %xmm15, %xmm11, %xmm11
  movbeq 64(%r14), %r12
  vpclmulqdq $17, %xmm1, %xmm0, %xmm1
  movdqu 96(%rbp), %xmm0
  vaesenc %xmm15, %xmm12, %xmm12
  movq %r13, 48(%rbp)
  vaesenc %xmm15, %xmm13, %xmm13
  movq %r12, 56(%rbp)
  vpxor %xmm2, %xmm4, %xmm4
  movdqu 64(%r9), %xmm2
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -48(%rcx), %xmm15
  vpxor %xmm3, %xmm6, %xmm6
  vpclmulqdq $0, %xmm2, %xmm0, %xmm3
  vaesenc %xmm15, %xmm9, %xmm9
  vpxor %xmm5, %xmm6, %xmm6
  vpclmulqdq $16, %xmm2, %xmm0, %xmm5
  vaesenc %xmm15, %xmm10, %xmm10
  movbeq 56(%r14), %r13
  vpxor %xmm1, %xmm7, %xmm7
  vpclmulqdq $1, %xmm2, %xmm0, %xmm1
  vpxor 112(%rbp), %xmm8, %xmm8
  vaesenc %xmm15, %xmm11, %xmm11
  movbeq 48(%r14), %r12
  vpclmulqdq $17, %xmm2, %xmm0, %xmm2
  vaesenc %xmm15, %xmm12, %xmm12
  movq %r13, 64(%rbp)
  vaesenc %xmm15, %xmm13, %xmm13
  movq %r12, 72(%rbp)
  vpxor %xmm3, %xmm4, %xmm4
  movdqu 80(%r9), %xmm3
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -32(%rcx), %xmm15
  vpxor %xmm5, %xmm6, %xmm6
  vpclmulqdq $16, %xmm3, %xmm8, %xmm5
  vaesenc %xmm15, %xmm9, %xmm9
  vpxor %xmm1, %xmm6, %xmm6
  vpclmulqdq $1, %xmm3, %xmm8, %xmm1
  vaesenc %xmm15, %xmm10, %xmm10
  movbeq 40(%r14), %r13
  vpxor %xmm2, %xmm7, %xmm7
  vpclmulqdq $0, %xmm3, %xmm8, %xmm2
  vaesenc %xmm15, %xmm11, %xmm11
  movbeq 32(%r14), %r12
  vpclmulqdq $17, %xmm3, %xmm8, %xmm8
  vaesenc %xmm15, %xmm12, %xmm12
  movq %r13, 80(%rbp)
  vaesenc %xmm15, %xmm13, %xmm13
  movq %r12, 88(%rbp)
  vpxor %xmm5, %xmm6, %xmm6
  vaesenc %xmm15, %xmm14, %xmm14
  vpxor %xmm1, %xmm6, %xmm6
  movdqu -16(%rcx), %xmm15
  vpslldq $8, %xmm6, %xmm5
  vpxor %xmm2, %xmm4, %xmm4
  pxor %xmm3, %xmm3
  mov $13979173243358019584, %r11
  pinsrq $1, %r11, %xmm3
  vaesenc %xmm15, %xmm9, %xmm9
  vpxor %xmm8, %xmm7, %xmm7
  vaesenc %xmm15, %xmm10, %xmm10
  vpxor %xmm5, %xmm4, %xmm4
  movbeq 24(%r14), %r13
  vaesenc %xmm15, %xmm11, %xmm11
  movbeq 16(%r14), %r12
  vpalignr $8, %xmm4, %xmm4, %xmm0
  vpclmulqdq $16, %xmm3, %xmm4, %xmm4
  movq %r13, 96(%rbp)
  vaesenc %xmm15, %xmm12, %xmm12
  movq %r12, 104(%rbp)
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu 0(%rcx), %xmm1
  vaesenc %xmm1, %xmm9, %xmm9
  movdqu 16(%rcx), %xmm15
  vaesenc %xmm1, %xmm10, %xmm10
  vpsrldq $8, %xmm6, %xmm6
  vaesenc %xmm1, %xmm11, %xmm11
  vpxor %xmm6, %xmm7, %xmm7
  vaesenc %xmm1, %xmm12, %xmm12
  vpxor %xmm0, %xmm4, %xmm4
  movbeq 8(%r14), %r13
  vaesenc %xmm1, %xmm13, %xmm13
  movbeq 0(%r14), %r12
  vaesenc %xmm1, %xmm14, %xmm14
  movdqu 32(%rcx), %xmm1
  vaesenc %xmm15, %xmm9, %xmm9
  movdqu %xmm7, 16(%rbp)
  vpalignr $8, %xmm4, %xmm4, %xmm8
  vaesenc %xmm15, %xmm10, %xmm10
  vpclmulqdq $16, %xmm3, %xmm4, %xmm4
  vpxor 0(%rdi), %xmm1, %xmm2
  vaesenc %xmm15, %xmm11, %xmm11
  vpxor 16(%rdi), %xmm1, %xmm0
  vaesenc %xmm15, %xmm12, %xmm12
  vpxor 32(%rdi), %xmm1, %xmm5
  vaesenc %xmm15, %xmm13, %xmm13
  vpxor 48(%rdi), %xmm1, %xmm6
  vaesenc %xmm15, %xmm14, %xmm14
  vpxor 64(%rdi), %xmm1, %xmm7
  vpxor 80(%rdi), %xmm1, %xmm3
  movdqu 0(%r8), %xmm1
  vaesenclast %xmm2, %xmm9, %xmm9
  pxor %xmm2, %xmm2
  mov $72057594037927936, %r11
  pinsrq $1, %r11, %xmm2
  vaesenclast %xmm0, %xmm10, %xmm10
  vpaddd %xmm2, %xmm1, %xmm0
  movq %r13, 112(%rbp)
  lea 96(%rdi), %rdi
  vaesenclast %xmm5, %xmm11, %xmm11
  vpaddd %xmm2, %xmm0, %xmm5
  movq %r12, 120(%rbp)
  lea 96(%rsi), %rsi
  movdqu -128(%rcx), %xmm15
  vaesenclast %xmm6, %xmm12, %xmm12
  vpaddd %xmm2, %xmm5, %xmm6
  vaesenclast %xmm7, %xmm13, %xmm13
  vpaddd %xmm2, %xmm6, %xmm7
  vaesenclast %xmm3, %xmm14, %xmm14
  vpaddd %xmm2, %xmm7, %xmm3
  sub $6, %rdx
  add $96, %r14
  cmp $0, %rdx
  jbe L190
  movdqu %xmm9, -96(%rsi)
  vpxor %xmm15, %xmm1, %xmm9
  movdqu %xmm10, -80(%rsi)
  movdqu %xmm0, %xmm10
  movdqu %xmm11, -64(%rsi)
  movdqu %xmm5, %xmm11
  movdqu %xmm12, -48(%rsi)
  movdqu %xmm6, %xmm12
  movdqu %xmm13, -32(%rsi)
  movdqu %xmm7, %xmm13
  movdqu %xmm14, -16(%rsi)
  movdqu %xmm3, %xmm14
  movdqu 32(%rbp), %xmm7
  jmp L191
L190:
  vpxor 16(%rbp), %xmm8, %xmm8
  vpxor %xmm4, %xmm8, %xmm8
L191:
.balign 16
L187:
  cmp $0, %rdx
  ja L186
  movdqu %xmm1, 0(%r8)
  movdqu 32(%rbp), %xmm7
  pxor %xmm4, %xmm4
  movdqu %xmm4, 0(%rbp)
  movdqu -32(%r9), %xmm3
  vpclmulqdq $0, %xmm3, %xmm7, %xmm1
  vpclmulqdq $16, %xmm3, %xmm7, %xmm5
  movdqu 48(%rbp), %xmm0
  vpclmulqdq $1, %xmm3, %xmm7, %xmm6
  vpclmulqdq $17, %xmm3, %xmm7, %xmm7
  movdqu -16(%r9), %xmm3
  vpxor %xmm5, %xmm6, %xmm6
  vpclmulqdq $0, %xmm3, %xmm0, %xmm5
  vpxor %xmm4, %xmm8, %xmm8
  vpxor %xmm5, %xmm1, %xmm4
  vpclmulqdq $16, %xmm3, %xmm0, %xmm1
  vpclmulqdq $1, %xmm3, %xmm0, %xmm2
  vpxor 0(%rbp), %xmm8, %xmm8
  vpclmulqdq $17, %xmm3, %xmm0, %xmm3
  movdqu 64(%rbp), %xmm0
  movdqu 16(%r9), %xmm5
  vpxor %xmm1, %xmm6, %xmm6
  vpclmulqdq $0, %xmm5, %xmm0, %xmm1
  vpxor %xmm2, %xmm6, %xmm6
  vpclmulqdq $16, %xmm5, %xmm0, %xmm2
  vpxor %xmm3, %xmm7, %xmm7
  vpclmulqdq $1, %xmm5, %xmm0, %xmm3
  vpclmulqdq $17, %xmm5, %xmm0, %xmm5
  movdqu 80(%rbp), %xmm0
  vpxor %xmm1, %xmm4, %xmm4
  movdqu 32(%r9), %xmm1
  vpxor %xmm2, %xmm6, %xmm6
  vpclmulqdq $0, %xmm1, %xmm0, %xmm2
  vpxor %xmm3, %xmm6, %xmm6
  vpclmulqdq $16, %xmm1, %xmm0, %xmm3
  vpxor %xmm5, %xmm7, %xmm7
  vpclmulqdq $1, %xmm1, %xmm0, %xmm5
  vpclmulqdq $17, %xmm1, %xmm0, %xmm1
  movdqu 96(%rbp), %xmm0
  vpxor %xmm2, %xmm4, %xmm4
  movdqu 64(%r9), %xmm2
  vpxor %xmm3, %xmm6, %xmm6
  vpclmulqdq $0, %xmm2, %xmm0, %xmm3
  vpxor %xmm5, %xmm6, %xmm6
  vpclmulqdq $16, %xmm2, %xmm0, %xmm5
  vpxor %xmm1, %xmm7, %xmm7
  vpclmulqdq $1, %xmm2, %xmm0, %xmm1
  vpxor 112(%rbp), %xmm8, %xmm8
  vpclmulqdq $17, %xmm2, %xmm0, %xmm2
  vpxor %xmm3, %xmm4, %xmm4
  movdqu 80(%r9), %xmm3
  vpxor %xmm5, %xmm6, %xmm6
  vpclmulqdq $16, %xmm3, %xmm8, %xmm5
  vpxor %xmm1, %xmm6, %xmm6
  vpclmulqdq $1, %xmm3, %xmm8, %xmm1
  vpxor %xmm2, %xmm7, %xmm7
  vpclmulqdq $0, %xmm3, %xmm8, %xmm2
  vpclmulqdq $17, %xmm3, %xmm8, %xmm8
  vpxor %xmm5, %xmm6, %xmm6
  vpxor %xmm1, %xmm6, %xmm6
  vpxor %xmm2, %xmm4, %xmm4
  pxor %xmm3, %xmm3
  mov $3254779904, %rax
  pinsrd $3, %eax, %xmm3
  vpxor %xmm8, %xmm7, %xmm7
  vpslldq $8, %xmm6, %xmm5
  vpxor %xmm5, %xmm4, %xmm4
  vpalignr $8, %xmm4, %xmm4, %xmm0
  vpclmulqdq $16, %xmm3, %xmm4, %xmm4
  vpsrldq $8, %xmm6, %xmm6
  vpxor %xmm6, %xmm7, %xmm7
  vpxor %xmm4, %xmm0, %xmm4
  vpalignr $8, %xmm4, %xmm4, %xmm8
  vpclmulqdq $16, %xmm3, %xmm4, %xmm4
  vpxor %xmm7, %xmm8, %xmm8
  vpxor %xmm4, %xmm8, %xmm8
  mov $579005069656919567, %r12
  pinsrq $0, %r12, %xmm0
  mov $283686952306183, %r12
  pinsrq $1, %r12, %xmm0
  movdqu %xmm9, -96(%rsi)
  vpshufb %xmm0, %xmm9, %xmm9
  vpxor %xmm7, %xmm1, %xmm1
  movdqu %xmm10, -80(%rsi)
  vpshufb %xmm0, %xmm10, %xmm10
  movdqu %xmm11, -64(%rsi)
  vpshufb %xmm0, %xmm11, %xmm11
  movdqu %xmm12, -48(%rsi)
  vpshufb %xmm0, %xmm12, %xmm12
  movdqu %xmm13, -32(%rsi)
  vpshufb %xmm0, %xmm13, %xmm13
  movdqu %xmm14, -16(%rsi)
  vpshufb %xmm0, %xmm14, %xmm14
  pxor %xmm4, %xmm4
  movdqu %xmm14, %xmm7
  movdqu %xmm4, 0(%rbp)
  movdqu %xmm13, 48(%rbp)
  movdqu %xmm12, 64(%rbp)
  movdqu %xmm11, 80(%rbp)
  movdqu %xmm10, 96(%rbp)
  movdqu %xmm9, 112(%rbp)
  movdqu -32(%r9), %xmm3
  vpclmulqdq $0, %xmm3, %xmm7, %xmm1
  vpclmulqdq $16, %xmm3, %xmm7, %xmm5
  movdqu 48(%rbp), %xmm0
  vpclmulqdq $1, %xmm3, %xmm7, %xmm6
  vpclmulqdq $17, %xmm3, %xmm7, %xmm7
  movdqu -16(%r9), %xmm3
  vpxor %xmm5, %xmm6, %xmm6
  vpclmulqdq $0, %xmm3, %xmm0, %xmm5
  vpxor %xmm4, %xmm8, %xmm8
  vpxor %xmm5, %xmm1, %xmm4
  vpclmulqdq $16, %xmm3, %xmm0, %xmm1
  vpclmulqdq $1, %xmm3, %xmm0, %xmm2
  vpxor 0(%rbp), %xmm8, %xmm8
  vpclmulqdq $17, %xmm3, %xmm0, %xmm3
  movdqu 64(%rbp), %xmm0
  movdqu 16(%r9), %xmm5
  vpxor %xmm1, %xmm6, %xmm6
  vpclmulqdq $0, %xmm5, %xmm0, %xmm1
  vpxor %xmm2, %xmm6, %xmm6
  vpclmulqdq $16, %xmm5, %xmm0, %xmm2
  vpxor %xmm3, %xmm7, %xmm7
  vpclmulqdq $1, %xmm5, %xmm0, %xmm3
  vpclmulqdq $17, %xmm5, %xmm0, %xmm5
  movdqu 80(%rbp), %xmm0
  vpxor %xmm1, %xmm4, %xmm4
  movdqu 32(%r9), %xmm1
  vpxor %xmm2, %xmm6, %xmm6
  vpclmulqdq $0, %xmm1, %xmm0, %xmm2
  vpxor %xmm3, %xmm6, %xmm6
  vpclmulqdq $16, %xmm1, %xmm0, %xmm3
  vpxor %xmm5, %xmm7, %xmm7
  vpclmulqdq $1, %xmm1, %xmm0, %xmm5
  vpclmulqdq $17, %xmm1, %xmm0, %xmm1
  movdqu 96(%rbp), %xmm0
  vpxor %xmm2, %xmm4, %xmm4
  movdqu 64(%r9), %xmm2
  vpxor %xmm3, %xmm6, %xmm6
  vpclmulqdq $0, %xmm2, %xmm0, %xmm3
  vpxor %xmm5, %xmm6, %xmm6
  vpclmulqdq $16, %xmm2, %xmm0, %xmm5
  vpxor %xmm1, %xmm7, %xmm7
  vpclmulqdq $1, %xmm2, %xmm0, %xmm1
  vpxor 112(%rbp), %xmm8, %xmm8
  vpclmulqdq $17, %xmm2, %xmm0, %xmm2
  vpxor %xmm3, %xmm4, %xmm4
  movdqu 80(%r9), %xmm3
  vpxor %xmm5, %xmm6, %xmm6
  vpclmulqdq $16, %xmm3, %xmm8, %xmm5
  vpxor %xmm1, %xmm6, %xmm6
  vpclmulqdq $1, %xmm3, %xmm8, %xmm1
  vpxor %xmm2, %xmm7, %xmm7
  vpclmulqdq $0, %xmm3, %xmm8, %xmm2
  vpclmulqdq $17, %xmm3, %xmm8, %xmm8
  vpxor %xmm5, %xmm6, %xmm6
  vpxor %xmm1, %xmm6, %xmm6
  vpxor %xmm2, %xmm4, %xmm4
  pxor %xmm3, %xmm3
  mov $3254779904, %rax
  pinsrd $3, %eax, %xmm3
  vpxor %xmm8, %xmm7, %xmm7
  vpslldq $8, %xmm6, %xmm5
  vpxor %xmm5, %xmm4, %xmm4
  vpalignr $8, %xmm4, %xmm4, %xmm0
  vpclmulqdq $16, %xmm3, %xmm4, %xmm4
  vpsrldq $8, %xmm6, %xmm6
  vpxor %xmm6, %xmm7, %xmm7
  vpxor %xmm4, %xmm0, %xmm4
  vpalignr $8, %xmm4, %xmm4, %xmm8
  vpclmulqdq $16, %xmm3, %xmm4, %xmm4
  vpxor %xmm7, %xmm8, %xmm8
  vpxor %xmm4, %xmm8, %xmm8
  mov $579005069656919567, %r12
  pinsrq $0, %r12, %xmm0
  mov $283686952306183, %r12
  pinsrq $1, %r12, %xmm0
  vpshufb %xmm0, %xmm8, %xmm8
  sub $128, %rcx
L185:
  movdqu 0(%r8), %xmm7
  mov %rcx, %r8
  mov 312(%rsp), %rax
  mov 320(%rsp), %rbx
  mov 328(%rsp), %rcx
  movdqu %xmm8, %xmm1
  mov $579005069656919567, %r12
  pinsrq $0, %r12, %xmm8
  mov $283686952306183, %r12
  pinsrq $1, %r12, %xmm8
  pshufb %xmm8, %xmm7
  movdqu 0(%r9), %xmm11
  mov $0, %rdx
  mov %rax, %r9
  mov %rbx, %r10
  pxor %xmm10, %xmm10
  mov $1, %r12
  pinsrd $0, %r12d, %xmm10
  jmp L193
.balign 16
L192:
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
.balign 16
L193:
  cmp %rcx, %rdx
  jne L192
  add 304(%rsp), %rcx
  imul $16, %rcx
  mov 344(%rsp), %r13
  cmp %rcx, %r13
  jbe L194
  mov 336(%rsp), %rax
  mov %rax, %rbx
  mov %r13, %rcx
  and $15, %rcx
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
  movdqu 0(%rax), %xmm2
  pxor %xmm0, %xmm2
  movdqu %xmm2, 0(%rbx)
  mov %rcx, %rax
  cmp $8, %rax
  jae L196
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
  jmp L197
L196:
  mov %rax, %rcx
  sub $8, %rcx
  shl $3, %rcx
  mov $1, %rdx
  shl %cl, %rdx
  sub $1, %rdx
  pextrq $1, %xmm2, %rcx
  and %rdx, %rcx
  pinsrq $1, %rcx, %xmm2
L197:
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
  jmp L195
L194:
L195:
  mov %r15, %r11
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
  mov 360(%rsp), %r15
  movdqu %xmm1, 0(%r15)
  pop %rax
  pinsrq $1, %rax, %xmm6
  pop %rax
  pinsrq $0, %rax, %xmm6
  pop %rax
  pinsrq $1, %rax, %xmm7
  pop %rax
  pinsrq $0, %rax, %xmm7
  pop %rax
  pinsrq $1, %rax, %xmm8
  pop %rax
  pinsrq $0, %rax, %xmm8
  pop %rax
  pinsrq $1, %rax, %xmm9
  pop %rax
  pinsrq $0, %rax, %xmm9
  pop %rax
  pinsrq $1, %rax, %xmm10
  pop %rax
  pinsrq $0, %rax, %xmm10
  pop %rax
  pinsrq $1, %rax, %xmm11
  pop %rax
  pinsrq $0, %rax, %xmm11
  pop %rax
  pinsrq $1, %rax, %xmm12
  pop %rax
  pinsrq $0, %rax, %xmm12
  pop %rax
  pinsrq $1, %rax, %xmm13
  pop %rax
  pinsrq $0, %rax, %xmm13
  pop %rax
  pinsrq $1, %rax, %xmm14
  pop %rax
  pinsrq $0, %rax, %xmm14
  pop %rax
  pinsrq $1, %rax, %xmm15
  pop %rax
  pinsrq $0, %rax, %xmm15
  pop %rbx
  pop %rbp
  pop %rdi
  pop %rsi
  pop %r12
  pop %r13
  pop %r14
  pop %r15
  ret

.global gcm256_encrypt_opt
gcm256_encrypt_opt:
  push %r15
  push %r14
  push %r13
  push %r12
  push %rsi
  push %rdi
  push %rbp
  push %rbx
  pextrq $0, %xmm15, %rax
  push %rax
  pextrq $1, %xmm15, %rax
  push %rax
  pextrq $0, %xmm14, %rax
  push %rax
  pextrq $1, %xmm14, %rax
  push %rax
  pextrq $0, %xmm13, %rax
  push %rax
  pextrq $1, %xmm13, %rax
  push %rax
  pextrq $0, %xmm12, %rax
  push %rax
  pextrq $1, %xmm12, %rax
  push %rax
  pextrq $0, %xmm11, %rax
  push %rax
  pextrq $1, %xmm11, %rax
  push %rax
  pextrq $0, %xmm10, %rax
  push %rax
  pextrq $1, %xmm10, %rax
  push %rax
  pextrq $0, %xmm9, %rax
  push %rax
  pextrq $1, %xmm9, %rax
  push %rax
  pextrq $0, %xmm8, %rax
  push %rax
  pextrq $1, %xmm8, %rax
  push %rax
  pextrq $0, %xmm7, %rax
  push %rax
  pextrq $1, %xmm7, %rax
  push %rax
  pextrq $0, %xmm6, %rax
  push %rax
  pextrq $1, %xmm6, %rax
  push %rax
  mov %rcx, %rdi
  mov %rdx, %rsi
  mov %r8, %rdx
  mov %r9, %rcx
  mov 264(%rsp), %r8
  mov 272(%rsp), %r9
  mov 352(%rsp), %rbp
  mov %r8, %r13
  mov %r9, %r14
  mov $579005069656919567, %r12
  pinsrq $0, %r12, %xmm8
  mov $283686952306183, %r12
  pinsrq $1, %r12, %xmm8
  mov %rdi, %rax
  mov %rcx, %r8
  mov %rdx, %r11
  movdqu 32(%r9), %xmm11
  pxor %xmm1, %xmm1
  mov %r11, %rcx
  cmp $0, %rcx
  je L198
  mov $0, %rdx
  mov %rax, %r9
  jmp L201
.balign 16
L200:
  movdqu 0(%r9), %xmm2
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
.balign 16
L201:
  cmp %rcx, %rdx
  jne L200
  jmp L199
L198:
L199:
  imul $16, %r11
  cmp %r11, %rsi
  jbe L202
  mov 280(%rsp), %r11
  movdqu 0(%r11), %xmm2
  mov %rsi, %rax
  and $15, %rax
  cmp $8, %rax
  jae L204
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
  jmp L205
L204:
  mov %rax, %rcx
  sub $8, %rcx
  shl $3, %rcx
  mov $1, %rdx
  shl %cl, %rdx
  sub $1, %rdx
  pextrq $1, %xmm2, %rcx
  and %rdx, %rcx
  pinsrq $1, %rcx, %xmm2
L205:
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
  jmp L203
L202:
L203:
  mov %rsi, %r15
  mov 288(%rsp), %rdi
  mov 296(%rsp), %rsi
  mov 304(%rsp), %rdx
  mov %r8, %rcx
  mov %r13, %r8
  mov %r14, %r9
  movdqu %xmm1, %xmm8
  cmp $0, %rdx
  jne L206
  lea 32(%r9), %r9
  movdqu 0(%r8), %xmm1
  mov $579005069656919567, %r12
  pinsrq $0, %r12, %xmm0
  mov $283686952306183, %r12
  pinsrq $1, %r12, %xmm0
  vpshufb %xmm0, %xmm1, %xmm1
  mov $2, %rbx
  pinsrd $0, %ebx, %xmm1
  vpshufb %xmm0, %xmm1, %xmm1
  movdqu %xmm1, 0(%r8)
  jmp L207
L206:
  mov $579005069656919567, %r12
  pinsrq $0, %r12, %xmm0
  mov $283686952306183, %r12
  pinsrq $1, %r12, %xmm0
  movdqu 0(%r8), %xmm1
  vpshufb %xmm0, %xmm8, %xmm8
  movdqu %xmm8, 0(%r8)
  add $128, %rcx
  vpshufb %xmm0, %xmm1, %xmm1
  mov $2, %rbx
  pinsrd $0, %ebx, %xmm1
  vpshufb %xmm0, %xmm1, %xmm1
  lea 96(%rsi), %r14
  movdqu -128(%rcx), %xmm4
  pxor %xmm2, %xmm2
  mov $72057594037927936, %r11
  pinsrq $1, %r11, %xmm2
  movdqu -112(%rcx), %xmm15
  mov %rcx, %r12
  sub $96, %r12
  vpxor %xmm4, %xmm1, %xmm9
  vpaddd %xmm2, %xmm1, %xmm10
  vpaddd %xmm2, %xmm10, %xmm11
  vpxor %xmm4, %xmm10, %xmm10
  vpaddd %xmm2, %xmm11, %xmm12
  vpxor %xmm4, %xmm11, %xmm11
  vpaddd %xmm2, %xmm12, %xmm13
  vpxor %xmm4, %xmm12, %xmm12
  vpaddd %xmm2, %xmm13, %xmm14
  vpxor %xmm4, %xmm13, %xmm13
  vpaddd %xmm2, %xmm14, %xmm1
  vpxor %xmm4, %xmm14, %xmm14
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -96(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -80(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -64(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -48(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -32(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -16(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu 0(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu 16(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu 32(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu 48(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu 64(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu 80(%rcx), %xmm15
  movdqu 96(%rcx), %xmm3
  vaesenc %xmm15, %xmm9, %xmm9
  vpxor 0(%rdi), %xmm3, %xmm4
  vaesenc %xmm15, %xmm10, %xmm10
  vpxor 16(%rdi), %xmm3, %xmm5
  vaesenc %xmm15, %xmm11, %xmm11
  vpxor 32(%rdi), %xmm3, %xmm6
  vaesenc %xmm15, %xmm12, %xmm12
  vpxor 48(%rdi), %xmm3, %xmm8
  vaesenc %xmm15, %xmm13, %xmm13
  vpxor 64(%rdi), %xmm3, %xmm2
  vaesenc %xmm15, %xmm14, %xmm14
  vpxor 80(%rdi), %xmm3, %xmm3
  lea 96(%rdi), %rdi
  vaesenclast %xmm4, %xmm9, %xmm9
  vaesenclast %xmm5, %xmm10, %xmm10
  vaesenclast %xmm6, %xmm11, %xmm11
  vaesenclast %xmm8, %xmm12, %xmm12
  vaesenclast %xmm2, %xmm13, %xmm13
  vaesenclast %xmm3, %xmm14, %xmm14
  movdqu %xmm9, 0(%rsi)
  movdqu %xmm10, 16(%rsi)
  movdqu %xmm11, 32(%rsi)
  movdqu %xmm12, 48(%rsi)
  movdqu %xmm13, 64(%rsi)
  movdqu %xmm14, 80(%rsi)
  lea 96(%rsi), %rsi
  vpshufb %xmm0, %xmm9, %xmm8
  vpshufb %xmm0, %xmm10, %xmm2
  movdqu %xmm8, 112(%rbp)
  vpshufb %xmm0, %xmm11, %xmm4
  movdqu %xmm2, 96(%rbp)
  vpshufb %xmm0, %xmm12, %xmm5
  movdqu %xmm4, 80(%rbp)
  vpshufb %xmm0, %xmm13, %xmm6
  movdqu %xmm5, 64(%rbp)
  vpshufb %xmm0, %xmm14, %xmm7
  movdqu %xmm6, 48(%rbp)
  movdqu -128(%rcx), %xmm4
  pxor %xmm2, %xmm2
  mov $72057594037927936, %r11
  pinsrq $1, %r11, %xmm2
  movdqu -112(%rcx), %xmm15
  mov %rcx, %r12
  sub $96, %r12
  vpxor %xmm4, %xmm1, %xmm9
  vpaddd %xmm2, %xmm1, %xmm10
  vpaddd %xmm2, %xmm10, %xmm11
  vpxor %xmm4, %xmm10, %xmm10
  vpaddd %xmm2, %xmm11, %xmm12
  vpxor %xmm4, %xmm11, %xmm11
  vpaddd %xmm2, %xmm12, %xmm13
  vpxor %xmm4, %xmm12, %xmm12
  vpaddd %xmm2, %xmm13, %xmm14
  vpxor %xmm4, %xmm13, %xmm13
  vpaddd %xmm2, %xmm14, %xmm1
  vpxor %xmm4, %xmm14, %xmm14
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -96(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -80(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -64(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -48(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -32(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -16(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu 0(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu 16(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu 32(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu 48(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu 64(%rcx), %xmm15
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu 80(%rcx), %xmm15
  movdqu 96(%rcx), %xmm3
  vaesenc %xmm15, %xmm9, %xmm9
  vpxor 0(%rdi), %xmm3, %xmm4
  vaesenc %xmm15, %xmm10, %xmm10
  vpxor 16(%rdi), %xmm3, %xmm5
  vaesenc %xmm15, %xmm11, %xmm11
  vpxor 32(%rdi), %xmm3, %xmm6
  vaesenc %xmm15, %xmm12, %xmm12
  vpxor 48(%rdi), %xmm3, %xmm8
  vaesenc %xmm15, %xmm13, %xmm13
  vpxor 64(%rdi), %xmm3, %xmm2
  vaesenc %xmm15, %xmm14, %xmm14
  vpxor 80(%rdi), %xmm3, %xmm3
  lea 96(%rdi), %rdi
  vaesenclast %xmm4, %xmm9, %xmm9
  vaesenclast %xmm5, %xmm10, %xmm10
  vaesenclast %xmm6, %xmm11, %xmm11
  vaesenclast %xmm8, %xmm12, %xmm12
  vaesenclast %xmm2, %xmm13, %xmm13
  vaesenclast %xmm3, %xmm14, %xmm14
  movdqu %xmm9, 0(%rsi)
  movdqu %xmm10, 16(%rsi)
  movdqu %xmm11, 32(%rsi)
  movdqu %xmm12, 48(%rsi)
  movdqu %xmm13, 64(%rsi)
  movdqu %xmm14, 80(%rsi)
  lea 96(%rsi), %rsi
  sub $12, %rdx
  movdqu 0(%r8), %xmm8
  lea 32(%r9), %r9
  pxor %xmm2, %xmm2
  mov $72057594037927936, %r11
  pinsrq $1, %r11, %xmm2
  vpxor %xmm4, %xmm4, %xmm4
  movdqu -128(%rcx), %xmm15
  vpaddd %xmm2, %xmm1, %xmm10
  vpaddd %xmm2, %xmm10, %xmm11
  vpaddd %xmm2, %xmm11, %xmm12
  vpaddd %xmm2, %xmm12, %xmm13
  vpaddd %xmm2, %xmm13, %xmm14
  vpxor %xmm15, %xmm1, %xmm9
  movdqu %xmm4, 16(%rbp)
  mov $14, %rbx
  jmp L209
.balign 16
L208:
  add $6, %rbx
  cmp $256, %rbx
  jb L210
  mov $579005069656919567, %r11
  pinsrq $0, %r11, %xmm0
  mov $283686952306183, %r11
  pinsrq $1, %r11, %xmm0
  vpshufb %xmm0, %xmm1, %xmm6
  pxor %xmm5, %xmm5
  mov $1, %r11
  pinsrq $0, %r11, %xmm5
  vpaddd %xmm5, %xmm6, %xmm10
  pxor %xmm5, %xmm5
  mov $2, %r11
  pinsrq $0, %r11, %xmm5
  vpaddd %xmm5, %xmm6, %xmm11
  movdqu -32(%r9), %xmm3
  vpaddd %xmm5, %xmm10, %xmm12
  vpshufb %xmm0, %xmm10, %xmm10
  vpaddd %xmm5, %xmm11, %xmm13
  vpshufb %xmm0, %xmm11, %xmm11
  vpxor %xmm15, %xmm10, %xmm10
  vpaddd %xmm5, %xmm12, %xmm14
  vpshufb %xmm0, %xmm12, %xmm12
  vpxor %xmm15, %xmm11, %xmm11
  vpaddd %xmm5, %xmm13, %xmm1
  vpshufb %xmm0, %xmm13, %xmm13
  vpshufb %xmm0, %xmm14, %xmm14
  vpshufb %xmm0, %xmm1, %xmm1
  sub $256, %rbx
  jmp L211
L210:
  movdqu -32(%r9), %xmm3
  vpaddd %xmm14, %xmm2, %xmm1
  vpxor %xmm15, %xmm10, %xmm10
  vpxor %xmm15, %xmm11, %xmm11
L211:
  movdqu %xmm1, 0(%r8)
  vpclmulqdq $16, %xmm3, %xmm7, %xmm5
  vpxor %xmm15, %xmm12, %xmm12
  movdqu -112(%rcx), %xmm2
  vpclmulqdq $1, %xmm3, %xmm7, %xmm6
  vaesenc %xmm2, %xmm9, %xmm9
  movdqu 48(%rbp), %xmm0
  vpxor %xmm15, %xmm13, %xmm13
  vpclmulqdq $0, %xmm3, %xmm7, %xmm1
  vaesenc %xmm2, %xmm10, %xmm10
  vpxor %xmm15, %xmm14, %xmm14
  vpclmulqdq $17, %xmm3, %xmm7, %xmm7
  vaesenc %xmm2, %xmm11, %xmm11
  movdqu -16(%r9), %xmm3
  vaesenc %xmm2, %xmm12, %xmm12
  vpxor %xmm5, %xmm6, %xmm6
  vpclmulqdq $0, %xmm3, %xmm0, %xmm5
  vpxor %xmm4, %xmm8, %xmm8
  vaesenc %xmm2, %xmm13, %xmm13
  vpxor %xmm5, %xmm1, %xmm4
  vpclmulqdq $16, %xmm3, %xmm0, %xmm1
  vaesenc %xmm2, %xmm14, %xmm14
  movdqu -96(%rcx), %xmm15
  vpclmulqdq $1, %xmm3, %xmm0, %xmm2
  vaesenc %xmm15, %xmm9, %xmm9
  vpxor 16(%rbp), %xmm8, %xmm8
  vpclmulqdq $17, %xmm3, %xmm0, %xmm3
  movdqu 64(%rbp), %xmm0
  vaesenc %xmm15, %xmm10, %xmm10
  movbeq 88(%r14), %r13
  vaesenc %xmm15, %xmm11, %xmm11
  movbeq 80(%r14), %r12
  vaesenc %xmm15, %xmm12, %xmm12
  movq %r13, 32(%rbp)
  vaesenc %xmm15, %xmm13, %xmm13
  movq %r12, 40(%rbp)
  movdqu 16(%r9), %xmm5
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -80(%rcx), %xmm15
  vpxor %xmm1, %xmm6, %xmm6
  vpclmulqdq $0, %xmm5, %xmm0, %xmm1
  vaesenc %xmm15, %xmm9, %xmm9
  vpxor %xmm2, %xmm6, %xmm6
  vpclmulqdq $16, %xmm5, %xmm0, %xmm2
  vaesenc %xmm15, %xmm10, %xmm10
  vpxor %xmm3, %xmm7, %xmm7
  vpclmulqdq $1, %xmm5, %xmm0, %xmm3
  vaesenc %xmm15, %xmm11, %xmm11
  vpclmulqdq $17, %xmm5, %xmm0, %xmm5
  movdqu 80(%rbp), %xmm0
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vpxor %xmm1, %xmm4, %xmm4
  movdqu 32(%r9), %xmm1
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -64(%rcx), %xmm15
  vpxor %xmm2, %xmm6, %xmm6
  vpclmulqdq $0, %xmm1, %xmm0, %xmm2
  vaesenc %xmm15, %xmm9, %xmm9
  vpxor %xmm3, %xmm6, %xmm6
  vpclmulqdq $16, %xmm1, %xmm0, %xmm3
  vaesenc %xmm15, %xmm10, %xmm10
  movbeq 72(%r14), %r13
  vpxor %xmm5, %xmm7, %xmm7
  vpclmulqdq $1, %xmm1, %xmm0, %xmm5
  vaesenc %xmm15, %xmm11, %xmm11
  movbeq 64(%r14), %r12
  vpclmulqdq $17, %xmm1, %xmm0, %xmm1
  movdqu 96(%rbp), %xmm0
  vaesenc %xmm15, %xmm12, %xmm12
  movq %r13, 48(%rbp)
  vaesenc %xmm15, %xmm13, %xmm13
  movq %r12, 56(%rbp)
  vpxor %xmm2, %xmm4, %xmm4
  movdqu 64(%r9), %xmm2
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -48(%rcx), %xmm15
  vpxor %xmm3, %xmm6, %xmm6
  vpclmulqdq $0, %xmm2, %xmm0, %xmm3
  vaesenc %xmm15, %xmm9, %xmm9
  vpxor %xmm5, %xmm6, %xmm6
  vpclmulqdq $16, %xmm2, %xmm0, %xmm5
  vaesenc %xmm15, %xmm10, %xmm10
  movbeq 56(%r14), %r13
  vpxor %xmm1, %xmm7, %xmm7
  vpclmulqdq $1, %xmm2, %xmm0, %xmm1
  vpxor 112(%rbp), %xmm8, %xmm8
  vaesenc %xmm15, %xmm11, %xmm11
  movbeq 48(%r14), %r12
  vpclmulqdq $17, %xmm2, %xmm0, %xmm2
  vaesenc %xmm15, %xmm12, %xmm12
  movq %r13, 64(%rbp)
  vaesenc %xmm15, %xmm13, %xmm13
  movq %r12, 72(%rbp)
  vpxor %xmm3, %xmm4, %xmm4
  movdqu 80(%r9), %xmm3
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu -32(%rcx), %xmm15
  vpxor %xmm5, %xmm6, %xmm6
  vpclmulqdq $16, %xmm3, %xmm8, %xmm5
  vaesenc %xmm15, %xmm9, %xmm9
  vpxor %xmm1, %xmm6, %xmm6
  vpclmulqdq $1, %xmm3, %xmm8, %xmm1
  vaesenc %xmm15, %xmm10, %xmm10
  movbeq 40(%r14), %r13
  vpxor %xmm2, %xmm7, %xmm7
  vpclmulqdq $0, %xmm3, %xmm8, %xmm2
  vaesenc %xmm15, %xmm11, %xmm11
  movbeq 32(%r14), %r12
  vpclmulqdq $17, %xmm3, %xmm8, %xmm8
  vaesenc %xmm15, %xmm12, %xmm12
  movq %r13, 80(%rbp)
  vaesenc %xmm15, %xmm13, %xmm13
  movq %r12, 88(%rbp)
  vpxor %xmm5, %xmm6, %xmm6
  vaesenc %xmm15, %xmm14, %xmm14
  vpxor %xmm1, %xmm6, %xmm6
  movdqu -16(%rcx), %xmm15
  vpslldq $8, %xmm6, %xmm5
  vpxor %xmm2, %xmm4, %xmm4
  pxor %xmm3, %xmm3
  mov $13979173243358019584, %r11
  pinsrq $1, %r11, %xmm3
  vaesenc %xmm15, %xmm9, %xmm9
  vpxor %xmm8, %xmm7, %xmm7
  vaesenc %xmm15, %xmm10, %xmm10
  vpxor %xmm5, %xmm4, %xmm4
  movbeq 24(%r14), %r13
  vaesenc %xmm15, %xmm11, %xmm11
  movbeq 16(%r14), %r12
  vpalignr $8, %xmm4, %xmm4, %xmm0
  vpclmulqdq $16, %xmm3, %xmm4, %xmm4
  movq %r13, 96(%rbp)
  vaesenc %xmm15, %xmm12, %xmm12
  movq %r12, 104(%rbp)
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  movdqu 0(%rcx), %xmm1
  vaesenc %xmm1, %xmm9, %xmm9
  movdqu 16(%rcx), %xmm15
  vaesenc %xmm1, %xmm10, %xmm10
  vpsrldq $8, %xmm6, %xmm6
  vaesenc %xmm1, %xmm11, %xmm11
  vpxor %xmm6, %xmm7, %xmm7
  vaesenc %xmm1, %xmm12, %xmm12
  vpxor %xmm0, %xmm4, %xmm4
  movbeq 8(%r14), %r13
  vaesenc %xmm1, %xmm13, %xmm13
  movbeq 0(%r14), %r12
  vaesenc %xmm1, %xmm14, %xmm14
  movdqu 32(%rcx), %xmm1
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  vaesenc %xmm1, %xmm9, %xmm9
  vaesenc %xmm1, %xmm10, %xmm10
  vaesenc %xmm1, %xmm11, %xmm11
  vaesenc %xmm1, %xmm12, %xmm12
  vaesenc %xmm1, %xmm13, %xmm13
  movdqu 48(%rcx), %xmm15
  vaesenc %xmm1, %xmm14, %xmm14
  movdqu 64(%rcx), %xmm1
  vaesenc %xmm15, %xmm9, %xmm9
  vaesenc %xmm15, %xmm10, %xmm10
  vaesenc %xmm15, %xmm11, %xmm11
  vaesenc %xmm15, %xmm12, %xmm12
  vaesenc %xmm15, %xmm13, %xmm13
  vaesenc %xmm15, %xmm14, %xmm14
  vaesenc %xmm1, %xmm9, %xmm9
  vaesenc %xmm1, %xmm10, %xmm10
  vaesenc %xmm1, %xmm11, %xmm11
  vaesenc %xmm1, %xmm12, %xmm12
  vaesenc %xmm1, %xmm13, %xmm13
  movdqu 80(%rcx), %xmm15
  vaesenc %xmm1, %xmm14, %xmm14
  movdqu 96(%rcx), %xmm1
  vaesenc %xmm15, %xmm9, %xmm9
  movdqu %xmm7, 16(%rbp)
  vpalignr $8, %xmm4, %xmm4, %xmm8
  vaesenc %xmm15, %xmm10, %xmm10
  vpclmulqdq $16, %xmm3, %xmm4, %xmm4
  vpxor 0(%rdi), %xmm1, %xmm2
  vaesenc %xmm15, %xmm11, %xmm11
  vpxor 16(%rdi), %xmm1, %xmm0
  vaesenc %xmm15, %xmm12, %xmm12
  vpxor 32(%rdi), %xmm1, %xmm5
  vaesenc %xmm15, %xmm13, %xmm13
  vpxor 48(%rdi), %xmm1, %xmm6
  vaesenc %xmm15, %xmm14, %xmm14
  vpxor 64(%rdi), %xmm1, %xmm7
  vpxor 80(%rdi), %xmm1, %xmm3
  movdqu 0(%r8), %xmm1
  vaesenclast %xmm2, %xmm9, %xmm9
  pxor %xmm2, %xmm2
  mov $72057594037927936, %r11
  pinsrq $1, %r11, %xmm2
  vaesenclast %xmm0, %xmm10, %xmm10
  vpaddd %xmm2, %xmm1, %xmm0
  movq %r13, 112(%rbp)
  lea 96(%rdi), %rdi
  vaesenclast %xmm5, %xmm11, %xmm11
  vpaddd %xmm2, %xmm0, %xmm5
  movq %r12, 120(%rbp)
  lea 96(%rsi), %rsi
  movdqu -128(%rcx), %xmm15
  vaesenclast %xmm6, %xmm12, %xmm12
  vpaddd %xmm2, %xmm5, %xmm6
  vaesenclast %xmm7, %xmm13, %xmm13
  vpaddd %xmm2, %xmm6, %xmm7
  vaesenclast %xmm3, %xmm14, %xmm14
  vpaddd %xmm2, %xmm7, %xmm3
  sub $6, %rdx
  add $96, %r14
  cmp $0, %rdx
  jbe L212
  movdqu %xmm9, -96(%rsi)
  vpxor %xmm15, %xmm1, %xmm9
  movdqu %xmm10, -80(%rsi)
  movdqu %xmm0, %xmm10
  movdqu %xmm11, -64(%rsi)
  movdqu %xmm5, %xmm11
  movdqu %xmm12, -48(%rsi)
  movdqu %xmm6, %xmm12
  movdqu %xmm13, -32(%rsi)
  movdqu %xmm7, %xmm13
  movdqu %xmm14, -16(%rsi)
  movdqu %xmm3, %xmm14
  movdqu 32(%rbp), %xmm7
  jmp L213
L212:
  vpxor 16(%rbp), %xmm8, %xmm8
  vpxor %xmm4, %xmm8, %xmm8
L213:
.balign 16
L209:
  cmp $0, %rdx
  ja L208
  movdqu %xmm1, 0(%r8)
  movdqu 32(%rbp), %xmm7
  pxor %xmm4, %xmm4
  movdqu %xmm4, 0(%rbp)
  movdqu -32(%r9), %xmm3
  vpclmulqdq $0, %xmm3, %xmm7, %xmm1
  vpclmulqdq $16, %xmm3, %xmm7, %xmm5
  movdqu 48(%rbp), %xmm0
  vpclmulqdq $1, %xmm3, %xmm7, %xmm6
  vpclmulqdq $17, %xmm3, %xmm7, %xmm7
  movdqu -16(%r9), %xmm3
  vpxor %xmm5, %xmm6, %xmm6
  vpclmulqdq $0, %xmm3, %xmm0, %xmm5
  vpxor %xmm4, %xmm8, %xmm8
  vpxor %xmm5, %xmm1, %xmm4
  vpclmulqdq $16, %xmm3, %xmm0, %xmm1
  vpclmulqdq $1, %xmm3, %xmm0, %xmm2
  vpxor 0(%rbp), %xmm8, %xmm8
  vpclmulqdq $17, %xmm3, %xmm0, %xmm3
  movdqu 64(%rbp), %xmm0
  movdqu 16(%r9), %xmm5
  vpxor %xmm1, %xmm6, %xmm6
  vpclmulqdq $0, %xmm5, %xmm0, %xmm1
  vpxor %xmm2, %xmm6, %xmm6
  vpclmulqdq $16, %xmm5, %xmm0, %xmm2
  vpxor %xmm3, %xmm7, %xmm7
  vpclmulqdq $1, %xmm5, %xmm0, %xmm3
  vpclmulqdq $17, %xmm5, %xmm0, %xmm5
  movdqu 80(%rbp), %xmm0
  vpxor %xmm1, %xmm4, %xmm4
  movdqu 32(%r9), %xmm1
  vpxor %xmm2, %xmm6, %xmm6
  vpclmulqdq $0, %xmm1, %xmm0, %xmm2
  vpxor %xmm3, %xmm6, %xmm6
  vpclmulqdq $16, %xmm1, %xmm0, %xmm3
  vpxor %xmm5, %xmm7, %xmm7
  vpclmulqdq $1, %xmm1, %xmm0, %xmm5
  vpclmulqdq $17, %xmm1, %xmm0, %xmm1
  movdqu 96(%rbp), %xmm0
  vpxor %xmm2, %xmm4, %xmm4
  movdqu 64(%r9), %xmm2
  vpxor %xmm3, %xmm6, %xmm6
  vpclmulqdq $0, %xmm2, %xmm0, %xmm3
  vpxor %xmm5, %xmm6, %xmm6
  vpclmulqdq $16, %xmm2, %xmm0, %xmm5
  vpxor %xmm1, %xmm7, %xmm7
  vpclmulqdq $1, %xmm2, %xmm0, %xmm1
  vpxor 112(%rbp), %xmm8, %xmm8
  vpclmulqdq $17, %xmm2, %xmm0, %xmm2
  vpxor %xmm3, %xmm4, %xmm4
  movdqu 80(%r9), %xmm3
  vpxor %xmm5, %xmm6, %xmm6
  vpclmulqdq $16, %xmm3, %xmm8, %xmm5
  vpxor %xmm1, %xmm6, %xmm6
  vpclmulqdq $1, %xmm3, %xmm8, %xmm1
  vpxor %xmm2, %xmm7, %xmm7
  vpclmulqdq $0, %xmm3, %xmm8, %xmm2
  vpclmulqdq $17, %xmm3, %xmm8, %xmm8
  vpxor %xmm5, %xmm6, %xmm6
  vpxor %xmm1, %xmm6, %xmm6
  vpxor %xmm2, %xmm4, %xmm4
  pxor %xmm3, %xmm3
  mov $3254779904, %rax
  pinsrd $3, %eax, %xmm3
  vpxor %xmm8, %xmm7, %xmm7
  vpslldq $8, %xmm6, %xmm5
  vpxor %xmm5, %xmm4, %xmm4
  vpalignr $8, %xmm4, %xmm4, %xmm0
  vpclmulqdq $16, %xmm3, %xmm4, %xmm4
  vpsrldq $8, %xmm6, %xmm6
  vpxor %xmm6, %xmm7, %xmm7
  vpxor %xmm4, %xmm0, %xmm4
  vpalignr $8, %xmm4, %xmm4, %xmm8
  vpclmulqdq $16, %xmm3, %xmm4, %xmm4
  vpxor %xmm7, %xmm8, %xmm8
  vpxor %xmm4, %xmm8, %xmm8
  mov $579005069656919567, %r12
  pinsrq $0, %r12, %xmm0
  mov $283686952306183, %r12
  pinsrq $1, %r12, %xmm0
  movdqu %xmm9, -96(%rsi)
  vpshufb %xmm0, %xmm9, %xmm9
  vpxor %xmm7, %xmm1, %xmm1
  movdqu %xmm10, -80(%rsi)
  vpshufb %xmm0, %xmm10, %xmm10
  movdqu %xmm11, -64(%rsi)
  vpshufb %xmm0, %xmm11, %xmm11
  movdqu %xmm12, -48(%rsi)
  vpshufb %xmm0, %xmm12, %xmm12
  movdqu %xmm13, -32(%rsi)
  vpshufb %xmm0, %xmm13, %xmm13
  movdqu %xmm14, -16(%rsi)
  vpshufb %xmm0, %xmm14, %xmm14
  pxor %xmm4, %xmm4
  movdqu %xmm14, %xmm7
  movdqu %xmm4, 0(%rbp)
  movdqu %xmm13, 48(%rbp)
  movdqu %xmm12, 64(%rbp)
  movdqu %xmm11, 80(%rbp)
  movdqu %xmm10, 96(%rbp)
  movdqu %xmm9, 112(%rbp)
  movdqu -32(%r9), %xmm3
  vpclmulqdq $0, %xmm3, %xmm7, %xmm1
  vpclmulqdq $16, %xmm3, %xmm7, %xmm5
  movdqu 48(%rbp), %xmm0
  vpclmulqdq $1, %xmm3, %xmm7, %xmm6
  vpclmulqdq $17, %xmm3, %xmm7, %xmm7
  movdqu -16(%r9), %xmm3
  vpxor %xmm5, %xmm6, %xmm6
  vpclmulqdq $0, %xmm3, %xmm0, %xmm5
  vpxor %xmm4, %xmm8, %xmm8
  vpxor %xmm5, %xmm1, %xmm4
  vpclmulqdq $16, %xmm3, %xmm0, %xmm1
  vpclmulqdq $1, %xmm3, %xmm0, %xmm2
  vpxor 0(%rbp), %xmm8, %xmm8
  vpclmulqdq $17, %xmm3, %xmm0, %xmm3
  movdqu 64(%rbp), %xmm0
  movdqu 16(%r9), %xmm5
  vpxor %xmm1, %xmm6, %xmm6
  vpclmulqdq $0, %xmm5, %xmm0, %xmm1
  vpxor %xmm2, %xmm6, %xmm6
  vpclmulqdq $16, %xmm5, %xmm0, %xmm2
  vpxor %xmm3, %xmm7, %xmm7
  vpclmulqdq $1, %xmm5, %xmm0, %xmm3
  vpclmulqdq $17, %xmm5, %xmm0, %xmm5
  movdqu 80(%rbp), %xmm0
  vpxor %xmm1, %xmm4, %xmm4
  movdqu 32(%r9), %xmm1
  vpxor %xmm2, %xmm6, %xmm6
  vpclmulqdq $0, %xmm1, %xmm0, %xmm2
  vpxor %xmm3, %xmm6, %xmm6
  vpclmulqdq $16, %xmm1, %xmm0, %xmm3
  vpxor %xmm5, %xmm7, %xmm7
  vpclmulqdq $1, %xmm1, %xmm0, %xmm5
  vpclmulqdq $17, %xmm1, %xmm0, %xmm1
  movdqu 96(%rbp), %xmm0
  vpxor %xmm2, %xmm4, %xmm4
  movdqu 64(%r9), %xmm2
  vpxor %xmm3, %xmm6, %xmm6
  vpclmulqdq $0, %xmm2, %xmm0, %xmm3
  vpxor %xmm5, %xmm6, %xmm6
  vpclmulqdq $16, %xmm2, %xmm0, %xmm5
  vpxor %xmm1, %xmm7, %xmm7
  vpclmulqdq $1, %xmm2, %xmm0, %xmm1
  vpxor 112(%rbp), %xmm8, %xmm8
  vpclmulqdq $17, %xmm2, %xmm0, %xmm2
  vpxor %xmm3, %xmm4, %xmm4
  movdqu 80(%r9), %xmm3
  vpxor %xmm5, %xmm6, %xmm6
  vpclmulqdq $16, %xmm3, %xmm8, %xmm5
  vpxor %xmm1, %xmm6, %xmm6
  vpclmulqdq $1, %xmm3, %xmm8, %xmm1
  vpxor %xmm2, %xmm7, %xmm7
  vpclmulqdq $0, %xmm3, %xmm8, %xmm2
  vpclmulqdq $17, %xmm3, %xmm8, %xmm8
  vpxor %xmm5, %xmm6, %xmm6
  vpxor %xmm1, %xmm6, %xmm6
  vpxor %xmm2, %xmm4, %xmm4
  pxor %xmm3, %xmm3
  mov $3254779904, %rax
  pinsrd $3, %eax, %xmm3
  vpxor %xmm8, %xmm7, %xmm7
  vpslldq $8, %xmm6, %xmm5
  vpxor %xmm5, %xmm4, %xmm4
  vpalignr $8, %xmm4, %xmm4, %xmm0
  vpclmulqdq $16, %xmm3, %xmm4, %xmm4
  vpsrldq $8, %xmm6, %xmm6
  vpxor %xmm6, %xmm7, %xmm7
  vpxor %xmm4, %xmm0, %xmm4
  vpalignr $8, %xmm4, %xmm4, %xmm8
  vpclmulqdq $16, %xmm3, %xmm4, %xmm4
  vpxor %xmm7, %xmm8, %xmm8
  vpxor %xmm4, %xmm8, %xmm8
  mov $579005069656919567, %r12
  pinsrq $0, %r12, %xmm0
  mov $283686952306183, %r12
  pinsrq $1, %r12, %xmm0
  vpshufb %xmm0, %xmm8, %xmm8
  sub $128, %rcx
L207:
  movdqu 0(%r8), %xmm7
  mov %rcx, %r8
  mov 312(%rsp), %rax
  mov 320(%rsp), %rbx
  mov 328(%rsp), %rcx
  movdqu %xmm8, %xmm1
  mov $579005069656919567, %r12
  pinsrq $0, %r12, %xmm8
  mov $283686952306183, %r12
  pinsrq $1, %r12, %xmm8
  pshufb %xmm8, %xmm7
  movdqu 0(%r9), %xmm11
  mov $0, %rdx
  mov %rax, %r9
  mov %rbx, %r10
  pxor %xmm10, %xmm10
  mov $1, %r12
  pinsrd $0, %r12d, %xmm10
  jmp L215
.balign 16
L214:
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
  aesenc %xmm2, %xmm0
  movdqu 176(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 192(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 208(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 224(%r8), %xmm2
  aesenclast %xmm2, %xmm0
  pxor %xmm2, %xmm2
  movdqu 0(%r9), %xmm2
  pxor %xmm0, %xmm2
  movdqu %xmm2, 0(%r10)
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
.balign 16
L215:
  cmp %rcx, %rdx
  jne L214
  add 304(%rsp), %rcx
  imul $16, %rcx
  mov 344(%rsp), %r13
  cmp %rcx, %r13
  jbe L216
  mov 336(%rsp), %rax
  mov %rax, %rbx
  mov %r13, %rcx
  and $15, %rcx
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
  aesenc %xmm2, %xmm0
  movdqu 176(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 192(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 208(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 224(%r8), %xmm2
  aesenclast %xmm2, %xmm0
  pxor %xmm2, %xmm2
  movdqu 0(%rax), %xmm2
  pxor %xmm0, %xmm2
  movdqu %xmm2, 0(%rbx)
  mov %rcx, %rax
  cmp $8, %rax
  jae L218
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
  jmp L219
L218:
  mov %rax, %rcx
  sub $8, %rcx
  shl $3, %rcx
  mov $1, %rdx
  shl %cl, %rdx
  sub $1, %rdx
  pextrq $1, %xmm2, %rcx
  and %rdx, %rcx
  pinsrq $1, %rcx, %xmm2
L219:
  pxor %xmm2, %xmm1
  movdqu %xmm11, %xmm2
  pshufb %xmm8, %xmm1
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
  jmp L217
L216:
L217:
  mov %r15, %r11
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
  aesenc %xmm2, %xmm0
  movdqu 176(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 192(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 208(%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 224(%r8), %xmm2
  aesenclast %xmm2, %xmm0
  pxor %xmm2, %xmm2
  pxor %xmm0, %xmm1
  mov 360(%rsp), %r15
  movdqu %xmm1, 0(%r15)
  pop %rax
  pinsrq $1, %rax, %xmm6
  pop %rax
  pinsrq $0, %rax, %xmm6
  pop %rax
  pinsrq $1, %rax, %xmm7
  pop %rax
  pinsrq $0, %rax, %xmm7
  pop %rax
  pinsrq $1, %rax, %xmm8
  pop %rax
  pinsrq $0, %rax, %xmm8
  pop %rax
  pinsrq $1, %rax, %xmm9
  pop %rax
  pinsrq $0, %rax, %xmm9
  pop %rax
  pinsrq $1, %rax, %xmm10
  pop %rax
  pinsrq $0, %rax, %xmm10
  pop %rax
  pinsrq $1, %rax, %xmm11
  pop %rax
  pinsrq $0, %rax, %xmm11
  pop %rax
  pinsrq $1, %rax, %xmm12
  pop %rax
  pinsrq $0, %rax, %xmm12
  pop %rax
  pinsrq $1, %rax, %xmm13
  pop %rax
  pinsrq $0, %rax, %xmm13
  pop %rax
  pinsrq $1, %rax, %xmm14
  pop %rax
  pinsrq $0, %rax, %xmm14
  pop %rax
  pinsrq $1, %rax, %xmm15
  pop %rax
  pinsrq $0, %rax, %xmm15
  pop %rbx
  pop %rbp
  pop %rdi
  pop %rsi
  pop %r12
  pop %r13
  pop %r14
  pop %r15
  ret


