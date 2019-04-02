.code
ALIGN 16
old_aes128_key_expansion proc
  movdqu xmm1, xmmword ptr [rcx + 0]
  movdqu xmmword ptr [rdx + 0], xmm1
  aeskeygenassist xmm2, xmm1, 1
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 16], xmm1
  aeskeygenassist xmm2, xmm1, 2
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 32], xmm1
  aeskeygenassist xmm2, xmm1, 4
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 48], xmm1
  aeskeygenassist xmm2, xmm1, 8
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 64], xmm1
  aeskeygenassist xmm2, xmm1, 16
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 80], xmm1
  aeskeygenassist xmm2, xmm1, 32
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 96], xmm1
  aeskeygenassist xmm2, xmm1, 64
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 112], xmm1
  aeskeygenassist xmm2, xmm1, 128
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 128], xmm1
  aeskeygenassist xmm2, xmm1, 27
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 144], xmm1
  aeskeygenassist xmm2, xmm1, 54
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 160], xmm1
  pxor xmm1, xmm1
  pxor xmm2, xmm2
  pxor xmm3, xmm3
  ret
old_aes128_key_expansion endp
ALIGN 16
aes128_key_expansion proc
  movdqu xmm1, xmmword ptr [rcx + 0]
  movdqu xmmword ptr [rdx + 0], xmm1
  aeskeygenassist xmm2, xmm1, 1
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 16], xmm1
  aeskeygenassist xmm2, xmm1, 2
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 32], xmm1
  aeskeygenassist xmm2, xmm1, 4
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 48], xmm1
  aeskeygenassist xmm2, xmm1, 8
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 64], xmm1
  aeskeygenassist xmm2, xmm1, 16
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 80], xmm1
  aeskeygenassist xmm2, xmm1, 32
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 96], xmm1
  aeskeygenassist xmm2, xmm1, 64
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 112], xmm1
  aeskeygenassist xmm2, xmm1, 128
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 128], xmm1
  aeskeygenassist xmm2, xmm1, 27
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 144], xmm1
  aeskeygenassist xmm2, xmm1, 54
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 160], xmm1
  pxor xmm1, xmm1
  pxor xmm2, xmm2
  pxor xmm3, xmm3
  ret
aes128_key_expansion endp
ALIGN 16
aes128_keyhash_init proc
  mov r8, 579005069656919567
  pinsrq xmm4, r8, 0
  mov r8, 283686952306183
  pinsrq xmm4, r8, 1
  pxor xmm0, xmm0
  movdqu xmmword ptr [rdx + 80], xmm0
  mov r8, rcx
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pshufb xmm0, xmm4
  mov rcx, rdx
  movdqu xmmword ptr [rcx + 32], xmm0
  movdqu xmm0, xmm6
  mov rax, r12
  movdqu xmm1, xmmword ptr [rcx + 32]
  movdqu xmm6, xmm1
  movdqu xmm3, xmm1
  pxor xmm4, xmm4
  pxor xmm5, xmm5
  mov r12, 3254779904
  pinsrd xmm4, r12d, 3
  mov r12, 1
  pinsrd xmm4, r12d, 0
  mov r12, 2147483648
  pinsrd xmm5, r12d, 3
  movdqu xmm1, xmm3
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pand xmm3, xmm5
  pcmpeqd xmm3, xmm5
  pshufd xmm3, xmm3, 255
  pand xmm3, xmm4
  vpxor xmm1, xmm1, xmm3
  movdqu xmmword ptr [rcx + 0], xmm1
  movdqu xmm1, xmm6
  movdqu xmm2, xmm6
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  movdqu xmm6, xmm1
  movdqu xmm3, xmm1
  pxor xmm4, xmm4
  pxor xmm5, xmm5
  mov r12, 3254779904
  pinsrd xmm4, r12d, 3
  mov r12, 1
  pinsrd xmm4, r12d, 0
  mov r12, 2147483648
  pinsrd xmm5, r12d, 3
  movdqu xmm1, xmm3
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pand xmm3, xmm5
  pcmpeqd xmm3, xmm5
  pshufd xmm3, xmm3, 255
  pand xmm3, xmm4
  vpxor xmm1, xmm1, xmm3
  movdqu xmmword ptr [rcx + 16], xmm1
  movdqu xmm2, xmm6
  movdqu xmm1, xmmword ptr [rcx + 32]
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  movdqu xmm6, xmm1
  movdqu xmm3, xmm1
  pxor xmm4, xmm4
  pxor xmm5, xmm5
  mov r12, 3254779904
  pinsrd xmm4, r12d, 3
  mov r12, 1
  pinsrd xmm4, r12d, 0
  mov r12, 2147483648
  pinsrd xmm5, r12d, 3
  movdqu xmm1, xmm3
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pand xmm3, xmm5
  pcmpeqd xmm3, xmm5
  pshufd xmm3, xmm3, 255
  pand xmm3, xmm4
  vpxor xmm1, xmm1, xmm3
  movdqu xmmword ptr [rcx + 48], xmm1
  movdqu xmm2, xmm6
  movdqu xmm1, xmmword ptr [rcx + 32]
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  movdqu xmm6, xmm1
  movdqu xmm3, xmm1
  pxor xmm4, xmm4
  pxor xmm5, xmm5
  mov r12, 3254779904
  pinsrd xmm4, r12d, 3
  mov r12, 1
  pinsrd xmm4, r12d, 0
  mov r12, 2147483648
  pinsrd xmm5, r12d, 3
  movdqu xmm1, xmm3
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pand xmm3, xmm5
  pcmpeqd xmm3, xmm5
  pshufd xmm3, xmm3, 255
  pand xmm3, xmm4
  vpxor xmm1, xmm1, xmm3
  movdqu xmmword ptr [rcx + 64], xmm1
  movdqu xmm2, xmm6
  movdqu xmm1, xmmword ptr [rcx + 32]
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  movdqu xmm6, xmm1
  movdqu xmm3, xmm1
  pxor xmm4, xmm4
  pxor xmm5, xmm5
  mov r12, 3254779904
  pinsrd xmm4, r12d, 3
  mov r12, 1
  pinsrd xmm4, r12d, 0
  mov r12, 2147483648
  pinsrd xmm5, r12d, 3
  movdqu xmm1, xmm3
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pand xmm3, xmm5
  pcmpeqd xmm3, xmm5
  pshufd xmm3, xmm3, 255
  pand xmm3, xmm4
  vpxor xmm1, xmm1, xmm3
  movdqu xmmword ptr [rcx + 96], xmm1
  movdqu xmm2, xmm6
  movdqu xmm1, xmmword ptr [rcx + 32]
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  movdqu xmm6, xmm1
  movdqu xmm3, xmm1
  pxor xmm4, xmm4
  pxor xmm5, xmm5
  mov r12, 3254779904
  pinsrd xmm4, r12d, 3
  mov r12, 1
  pinsrd xmm4, r12d, 0
  mov r12, 2147483648
  pinsrd xmm5, r12d, 3
  movdqu xmm1, xmm3
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pand xmm3, xmm5
  pcmpeqd xmm3, xmm5
  pshufd xmm3, xmm3, 255
  pand xmm3, xmm4
  vpxor xmm1, xmm1, xmm3
  movdqu xmmword ptr [rcx + 112], xmm1
  movdqu xmm6, xmm0
  mov r12, rax
  ret
aes128_keyhash_init endp
ALIGN 16
old_aes256_key_expansion proc
  movdqu xmm1, xmmword ptr [rcx + 0]
  movdqu xmm3, xmmword ptr [rcx + 16]
  movdqu xmmword ptr [rdx + 0], xmm1
  movdqu xmmword ptr [rdx + 16], xmm3
  aeskeygenassist xmm2, xmm3, 1
  pshufd xmm2, xmm2, 255
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 32], xmm1
  aeskeygenassist xmm2, xmm1, 0
  pshufd xmm2, xmm2, 170
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  pxor xmm3, xmm2
  movdqu xmmword ptr [rdx + 48], xmm3
  aeskeygenassist xmm2, xmm3, 2
  pshufd xmm2, xmm2, 255
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 64], xmm1
  aeskeygenassist xmm2, xmm1, 0
  pshufd xmm2, xmm2, 170
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  pxor xmm3, xmm2
  movdqu xmmword ptr [rdx + 80], xmm3
  aeskeygenassist xmm2, xmm3, 4
  pshufd xmm2, xmm2, 255
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 96], xmm1
  aeskeygenassist xmm2, xmm1, 0
  pshufd xmm2, xmm2, 170
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  pxor xmm3, xmm2
  movdqu xmmword ptr [rdx + 112], xmm3
  aeskeygenassist xmm2, xmm3, 8
  pshufd xmm2, xmm2, 255
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 128], xmm1
  aeskeygenassist xmm2, xmm1, 0
  pshufd xmm2, xmm2, 170
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  pxor xmm3, xmm2
  movdqu xmmword ptr [rdx + 144], xmm3
  aeskeygenassist xmm2, xmm3, 16
  pshufd xmm2, xmm2, 255
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 160], xmm1
  aeskeygenassist xmm2, xmm1, 0
  pshufd xmm2, xmm2, 170
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  pxor xmm3, xmm2
  movdqu xmmword ptr [rdx + 176], xmm3
  aeskeygenassist xmm2, xmm3, 32
  pshufd xmm2, xmm2, 255
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 192], xmm1
  aeskeygenassist xmm2, xmm1, 0
  pshufd xmm2, xmm2, 170
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  pxor xmm3, xmm2
  movdqu xmmword ptr [rdx + 208], xmm3
  aeskeygenassist xmm2, xmm3, 64
  pshufd xmm2, xmm2, 255
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 224], xmm1
  pxor xmm1, xmm1
  pxor xmm2, xmm2
  pxor xmm3, xmm3
  pxor xmm4, xmm4
  ret
old_aes256_key_expansion endp
ALIGN 16
aes256_key_expansion proc
  movdqu xmm1, xmmword ptr [rcx + 0]
  movdqu xmm3, xmmword ptr [rcx + 16]
  movdqu xmmword ptr [rdx + 0], xmm1
  movdqu xmmword ptr [rdx + 16], xmm3
  aeskeygenassist xmm2, xmm3, 1
  pshufd xmm2, xmm2, 255
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 32], xmm1
  aeskeygenassist xmm2, xmm1, 0
  pshufd xmm2, xmm2, 170
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  pxor xmm3, xmm2
  movdqu xmmword ptr [rdx + 48], xmm3
  aeskeygenassist xmm2, xmm3, 2
  pshufd xmm2, xmm2, 255
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 64], xmm1
  aeskeygenassist xmm2, xmm1, 0
  pshufd xmm2, xmm2, 170
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  pxor xmm3, xmm2
  movdqu xmmword ptr [rdx + 80], xmm3
  aeskeygenassist xmm2, xmm3, 4
  pshufd xmm2, xmm2, 255
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 96], xmm1
  aeskeygenassist xmm2, xmm1, 0
  pshufd xmm2, xmm2, 170
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  pxor xmm3, xmm2
  movdqu xmmword ptr [rdx + 112], xmm3
  aeskeygenassist xmm2, xmm3, 8
  pshufd xmm2, xmm2, 255
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 128], xmm1
  aeskeygenassist xmm2, xmm1, 0
  pshufd xmm2, xmm2, 170
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  pxor xmm3, xmm2
  movdqu xmmword ptr [rdx + 144], xmm3
  aeskeygenassist xmm2, xmm3, 16
  pshufd xmm2, xmm2, 255
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 160], xmm1
  aeskeygenassist xmm2, xmm1, 0
  pshufd xmm2, xmm2, 170
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  pxor xmm3, xmm2
  movdqu xmmword ptr [rdx + 176], xmm3
  aeskeygenassist xmm2, xmm3, 32
  pshufd xmm2, xmm2, 255
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 192], xmm1
  aeskeygenassist xmm2, xmm1, 0
  pshufd xmm2, xmm2, 170
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  vpslldq xmm4, xmm3, 4
  pxor xmm3, xmm4
  pxor xmm3, xmm2
  movdqu xmmword ptr [rdx + 208], xmm3
  aeskeygenassist xmm2, xmm3, 64
  pshufd xmm2, xmm2, 255
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  vpslldq xmm4, xmm1, 4
  pxor xmm1, xmm4
  pxor xmm1, xmm2
  movdqu xmmword ptr [rdx + 224], xmm1
  pxor xmm1, xmm1
  pxor xmm2, xmm2
  pxor xmm3, xmm3
  pxor xmm4, xmm4
  ret
aes256_key_expansion endp
ALIGN 16
aes256_keyhash_init proc
  mov r8, 579005069656919567
  pinsrq xmm4, r8, 0
  mov r8, 283686952306183
  pinsrq xmm4, r8, 1
  pxor xmm0, xmm0
  movdqu xmmword ptr [rdx + 80], xmm0
  mov r8, rcx
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 176]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 192]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 208]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 224]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pshufb xmm0, xmm4
  mov rcx, rdx
  movdqu xmmword ptr [rcx + 32], xmm0
  movdqu xmm0, xmm6
  mov rax, r12
  movdqu xmm1, xmmword ptr [rcx + 32]
  movdqu xmm6, xmm1
  movdqu xmm3, xmm1
  pxor xmm4, xmm4
  pxor xmm5, xmm5
  mov r12, 3254779904
  pinsrd xmm4, r12d, 3
  mov r12, 1
  pinsrd xmm4, r12d, 0
  mov r12, 2147483648
  pinsrd xmm5, r12d, 3
  movdqu xmm1, xmm3
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pand xmm3, xmm5
  pcmpeqd xmm3, xmm5
  pshufd xmm3, xmm3, 255
  pand xmm3, xmm4
  vpxor xmm1, xmm1, xmm3
  movdqu xmmword ptr [rcx + 0], xmm1
  movdqu xmm1, xmm6
  movdqu xmm2, xmm6
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  movdqu xmm6, xmm1
  movdqu xmm3, xmm1
  pxor xmm4, xmm4
  pxor xmm5, xmm5
  mov r12, 3254779904
  pinsrd xmm4, r12d, 3
  mov r12, 1
  pinsrd xmm4, r12d, 0
  mov r12, 2147483648
  pinsrd xmm5, r12d, 3
  movdqu xmm1, xmm3
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pand xmm3, xmm5
  pcmpeqd xmm3, xmm5
  pshufd xmm3, xmm3, 255
  pand xmm3, xmm4
  vpxor xmm1, xmm1, xmm3
  movdqu xmmword ptr [rcx + 16], xmm1
  movdqu xmm2, xmm6
  movdqu xmm1, xmmword ptr [rcx + 32]
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  movdqu xmm6, xmm1
  movdqu xmm3, xmm1
  pxor xmm4, xmm4
  pxor xmm5, xmm5
  mov r12, 3254779904
  pinsrd xmm4, r12d, 3
  mov r12, 1
  pinsrd xmm4, r12d, 0
  mov r12, 2147483648
  pinsrd xmm5, r12d, 3
  movdqu xmm1, xmm3
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pand xmm3, xmm5
  pcmpeqd xmm3, xmm5
  pshufd xmm3, xmm3, 255
  pand xmm3, xmm4
  vpxor xmm1, xmm1, xmm3
  movdqu xmmword ptr [rcx + 48], xmm1
  movdqu xmm2, xmm6
  movdqu xmm1, xmmword ptr [rcx + 32]
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  movdqu xmm6, xmm1
  movdqu xmm3, xmm1
  pxor xmm4, xmm4
  pxor xmm5, xmm5
  mov r12, 3254779904
  pinsrd xmm4, r12d, 3
  mov r12, 1
  pinsrd xmm4, r12d, 0
  mov r12, 2147483648
  pinsrd xmm5, r12d, 3
  movdqu xmm1, xmm3
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pand xmm3, xmm5
  pcmpeqd xmm3, xmm5
  pshufd xmm3, xmm3, 255
  pand xmm3, xmm4
  vpxor xmm1, xmm1, xmm3
  movdqu xmmword ptr [rcx + 64], xmm1
  movdqu xmm2, xmm6
  movdqu xmm1, xmmword ptr [rcx + 32]
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  movdqu xmm6, xmm1
  movdqu xmm3, xmm1
  pxor xmm4, xmm4
  pxor xmm5, xmm5
  mov r12, 3254779904
  pinsrd xmm4, r12d, 3
  mov r12, 1
  pinsrd xmm4, r12d, 0
  mov r12, 2147483648
  pinsrd xmm5, r12d, 3
  movdqu xmm1, xmm3
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pand xmm3, xmm5
  pcmpeqd xmm3, xmm5
  pshufd xmm3, xmm3, 255
  pand xmm3, xmm4
  vpxor xmm1, xmm1, xmm3
  movdqu xmmword ptr [rcx + 96], xmm1
  movdqu xmm2, xmm6
  movdqu xmm1, xmmword ptr [rcx + 32]
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  movdqu xmm6, xmm1
  movdqu xmm3, xmm1
  pxor xmm4, xmm4
  pxor xmm5, xmm5
  mov r12, 3254779904
  pinsrd xmm4, r12d, 3
  mov r12, 1
  pinsrd xmm4, r12d, 0
  mov r12, 2147483648
  pinsrd xmm5, r12d, 3
  movdqu xmm1, xmm3
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pand xmm3, xmm5
  pcmpeqd xmm3, xmm5
  pshufd xmm3, xmm3, 255
  pand xmm3, xmm4
  vpxor xmm1, xmm1, xmm3
  movdqu xmmword ptr [rcx + 112], xmm1
  movdqu xmm6, xmm0
  mov r12, rax
  ret
aes256_keyhash_init endp
ALIGN 16
old_gcm128_encrypt proc
  mov r9, rcx
  push r15
  push r14
  push r13
  push r12
  push rsi
  push rdi
  push rbp
  push rbx
  pextrq rax, xmm15, 0
  push rax
  pextrq rax, xmm15, 1
  push rax
  pextrq rax, xmm14, 0
  push rax
  pextrq rax, xmm14, 1
  push rax
  pextrq rax, xmm13, 0
  push rax
  pextrq rax, xmm13, 1
  push rax
  pextrq rax, xmm12, 0
  push rax
  pextrq rax, xmm12, 1
  push rax
  pextrq rax, xmm11, 0
  push rax
  pextrq rax, xmm11, 1
  push rax
  pextrq rax, xmm10, 0
  push rax
  pextrq rax, xmm10, 1
  push rax
  pextrq rax, xmm9, 0
  push rax
  pextrq rax, xmm9, 1
  push rax
  pextrq rax, xmm8, 0
  push rax
  pextrq rax, xmm8, 1
  push rax
  pextrq rax, xmm7, 0
  push rax
  pextrq rax, xmm7, 1
  push rax
  pextrq rax, xmm6, 0
  push rax
  pextrq rax, xmm6, 1
  push rax
  mov r14, qword ptr [r9 + 0]
  mov r13, qword ptr [r9 + 8]
  mov rax, qword ptr [r9 + 16]
  mov r11, qword ptr [r9 + 24]
  mov r10, qword ptr [r9 + 32]
  mov r8, qword ptr [r9 + 40]
  mov rbx, qword ptr [r9 + 48]
  mov r15, qword ptr [r9 + 56]
  movdqu xmm7, xmmword ptr [r10 + 0]
  mov r12, 579005069656919567
  pinsrq xmm8, r12, 0
  mov r12, 283686952306183
  pinsrq xmm8, r12, 1
  pxor xmm0, xmm0
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pshufb xmm0, xmm8
  movdqu xmm11, xmm0
  pshufb xmm7, xmm8
  mov r12, 2
  pinsrd xmm7, r12d, 0
  pxor xmm1, xmm1
  cmp r11, 0
  jbe L0
  mov rcx, r11
  shr rcx, 4
  mov r9, rax
  cmp rcx, 0
  je L2
  mov rdx, 0
  jmp L5
ALIGN 16
L4:
  movdqu xmm2, xmmword ptr [r9 + 0]
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  add rdx, 1
  add r9, 16
ALIGN 16
L5:
  cmp rdx, rcx
  jne L4
  jmp L3
L2:
L3:
  mov rax, r11
  and rax, 15
  cmp rax, 0
  jne L6
  jmp L7
L6:
  movdqu xmm2, xmmword ptr [r9 + 0]
  cmp rax, 8
  jae L8
  mov rcx, 0
  pinsrq xmm2, rcx, 1
  mov rcx, rax
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 0
  and rcx, rdx
  pinsrq xmm2, rcx, 0
  jmp L9
L8:
  mov rcx, rax
  sub rcx, 8
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 1
  and rcx, rdx
  pinsrq xmm2, rcx, 1
L9:
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
L7:
  jmp L1
L0:
L1:
  mov rax, r14
  mov rcx, r13
  cmp rcx, 0
  jbe L10
  mov rsi, rcx
  and rsi, 15
  shr rcx, 4
  mov rdx, rcx
  shr rdx, 2
  and rcx, 3
  cmp rdx, 0
  jbe L12
  mov r9, rax
  mov r10, rbx
  pshufb xmm7, xmm8
  movdqu xmm9, xmm7
  mov rax, 579005069656919567
  pinsrq xmm0, rax, 0
  mov rax, 579005069656919567
  pinsrq xmm0, rax, 1
  pshufb xmm9, xmm0
  movdqu xmm10, xmm9
  pxor xmm3, xmm3
  mov rax, 1
  pinsrd xmm3, eax, 2
  paddd xmm9, xmm3
  mov rax, 3
  pinsrd xmm3, eax, 2
  mov rax, 2
  pinsrd xmm3, eax, 0
  paddd xmm10, xmm3
  pshufb xmm9, xmm8
  pshufb xmm10, xmm8
  pextrq rdi, xmm7, 0
  mov rax, 283686952306183
  pinsrq xmm0, rax, 0
  mov rax, 579005069656919567
  pinsrq xmm0, rax, 1
  pxor xmm15, xmm15
  mov rax, 4
  pinsrd xmm15, eax, 0
  mov rax, 4
  pinsrd xmm15, eax, 2
  jmp L15
ALIGN 16
L14:
  pinsrq xmm2, rdi, 0
  pinsrq xmm12, rdi, 0
  pinsrq xmm13, rdi, 0
  pinsrq xmm14, rdi, 0
  shufpd xmm2, xmm9, 2
  shufpd xmm12, xmm9, 0
  shufpd xmm13, xmm10, 2
  shufpd xmm14, xmm10, 0
  pshufb xmm9, xmm0
  pshufb xmm10, xmm0
  movdqu xmm3, xmmword ptr [r8 + 0]
  movdqu xmm4, xmmword ptr [r8 + 16]
  movdqu xmm5, xmmword ptr [r8 + 32]
  movdqu xmm6, xmmword ptr [r8 + 48]
  paddd xmm9, xmm15
  paddd xmm10, xmm15
  pxor xmm2, xmm3
  pxor xmm12, xmm3
  pxor xmm13, xmm3
  pxor xmm14, xmm3
  pshufb xmm9, xmm0
  pshufb xmm10, xmm0
  aesenc xmm2, xmm4
  aesenc xmm12, xmm4
  aesenc xmm13, xmm4
  aesenc xmm14, xmm4
  aesenc xmm2, xmm5
  aesenc xmm12, xmm5
  aesenc xmm13, xmm5
  aesenc xmm14, xmm5
  aesenc xmm2, xmm6
  aesenc xmm12, xmm6
  aesenc xmm13, xmm6
  aesenc xmm14, xmm6
  movdqu xmm3, xmmword ptr [r8 + 64]
  movdqu xmm4, xmmword ptr [r8 + 80]
  movdqu xmm5, xmmword ptr [r8 + 96]
  movdqu xmm6, xmmword ptr [r8 + 112]
  aesenc xmm2, xmm3
  aesenc xmm12, xmm3
  aesenc xmm13, xmm3
  aesenc xmm14, xmm3
  aesenc xmm2, xmm4
  aesenc xmm12, xmm4
  aesenc xmm13, xmm4
  aesenc xmm14, xmm4
  aesenc xmm2, xmm5
  aesenc xmm12, xmm5
  aesenc xmm13, xmm5
  aesenc xmm14, xmm5
  aesenc xmm2, xmm6
  aesenc xmm12, xmm6
  aesenc xmm13, xmm6
  aesenc xmm14, xmm6
  movdqu xmm3, xmmword ptr [r8 + 128]
  movdqu xmm4, xmmword ptr [r8 + 144]
  movdqu xmm5, xmmword ptr [r8 + 160]
  aesenc xmm2, xmm3
  aesenc xmm12, xmm3
  aesenc xmm13, xmm3
  aesenc xmm14, xmm3
  aesenc xmm2, xmm4
  aesenc xmm12, xmm4
  aesenc xmm13, xmm4
  aesenc xmm14, xmm4
  aesenclast xmm2, xmm5
  aesenclast xmm12, xmm5
  aesenclast xmm13, xmm5
  aesenclast xmm14, xmm5
  movdqu xmm7, xmmword ptr [r9 + 0]
  pxor xmm2, xmm7
  movdqu xmm7, xmmword ptr [r9 + 16]
  pxor xmm12, xmm7
  movdqu xmm7, xmmword ptr [r9 + 32]
  pxor xmm13, xmm7
  movdqu xmm7, xmmword ptr [r9 + 48]
  pxor xmm14, xmm7
  movdqu xmmword ptr [r10 + 0], xmm2
  movdqu xmmword ptr [r10 + 16], xmm12
  movdqu xmmword ptr [r10 + 32], xmm13
  movdqu xmmword ptr [r10 + 48], xmm14
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  movdqu xmm2, xmm12
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  movdqu xmm2, xmm13
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  movdqu xmm2, xmm14
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  sub rdx, 1
  add r9, 64
  add r10, 64
ALIGN 16
L15:
  cmp rdx, 0
  ja L14
  movdqu xmm7, xmm9
  pinsrq xmm7, rdi, 0
  pshufb xmm7, xmm8
  mov rax, r9
  mov rbx, r10
  jmp L13
L12:
L13:
  mov rdx, 0
  mov r9, rax
  mov r10, rbx
  pxor xmm10, xmm10
  mov r12, 1
  pinsrd xmm10, r12d, 0
  jmp L17
ALIGN 16
L16:
  movdqu xmm0, xmm7
  pshufb xmm0, xmm8
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  movdqu xmm2, xmmword ptr [r9 + 0]
  pxor xmm2, xmm0
  movdqu xmmword ptr [r10 + 0], xmm2
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  add rdx, 1
  add r9, 16
  add r10, 16
  paddd xmm7, xmm10
ALIGN 16
L17:
  cmp rdx, rcx
  jne L16
  cmp rsi, 0
  jne L18
  jmp L19
L18:
  movdqu xmm3, xmm1
  movdqu xmm2, xmmword ptr [r9 + 0]
  movdqu xmm1, xmm2
  movdqu xmm0, xmm7
  mov r12, 579005069656919567
  pinsrq xmm2, r12, 0
  mov r12, 283686952306183
  pinsrq xmm2, r12, 1
  pshufb xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pxor xmm1, xmm0
  movdqu xmmword ptr [r10 + 0], xmm1
  mov rax, rsi
  mov r9, r10
  movdqu xmm1, xmm3
  movdqu xmm2, xmmword ptr [r9 + 0]
  cmp rax, 8
  jae L20
  mov rcx, 0
  pinsrq xmm2, rcx, 1
  mov rcx, rax
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 0
  and rcx, rdx
  pinsrq xmm2, rcx, 0
  jmp L21
L20:
  mov rcx, rax
  sub rcx, 8
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 1
  and rcx, rdx
  pinsrq xmm2, rcx, 1
L21:
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
L19:
  jmp L11
L10:
L11:
  pxor xmm2, xmm2
  mov rax, r13
  imul rax, 8
  pinsrd xmm2, eax, 0
  mov rax, r11
  imul rax, 8
  pinsrd xmm2, eax, 2
  pshufb xmm2, xmm8
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  mov r12, 1
  pinsrd xmm7, r12d, 0
  movdqu xmm0, xmm7
  mov r12, 579005069656919567
  pinsrq xmm2, r12, 0
  mov r12, 283686952306183
  pinsrq xmm2, r12, 1
  pshufb xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pxor xmm1, xmm0
  movdqu xmmword ptr [r15 + 0], xmm1
  pop rax
  pinsrq xmm6, rax, 1
  pop rax
  pinsrq xmm6, rax, 0
  pop rax
  pinsrq xmm7, rax, 1
  pop rax
  pinsrq xmm7, rax, 0
  pop rax
  pinsrq xmm8, rax, 1
  pop rax
  pinsrq xmm8, rax, 0
  pop rax
  pinsrq xmm9, rax, 1
  pop rax
  pinsrq xmm9, rax, 0
  pop rax
  pinsrq xmm10, rax, 1
  pop rax
  pinsrq xmm10, rax, 0
  pop rax
  pinsrq xmm11, rax, 1
  pop rax
  pinsrq xmm11, rax, 0
  pop rax
  pinsrq xmm12, rax, 1
  pop rax
  pinsrq xmm12, rax, 0
  pop rax
  pinsrq xmm13, rax, 1
  pop rax
  pinsrq xmm13, rax, 0
  pop rax
  pinsrq xmm14, rax, 1
  pop rax
  pinsrq xmm14, rax, 0
  pop rax
  pinsrq xmm15, rax, 1
  pop rax
  pinsrq xmm15, rax, 0
  pop rbx
  pop rbp
  pop rdi
  pop rsi
  pop r12
  pop r13
  pop r14
  pop r15
  ret
old_gcm128_encrypt endp
ALIGN 16
gcm128_encrypt proc
  push r15
  push r14
  push r13
  push r12
  push rsi
  push rdi
  push rbp
  push rbx
  pextrq rax, xmm15, 0
  push rax
  pextrq rax, xmm15, 1
  push rax
  pextrq rax, xmm14, 0
  push rax
  pextrq rax, xmm14, 1
  push rax
  pextrq rax, xmm13, 0
  push rax
  pextrq rax, xmm13, 1
  push rax
  pextrq rax, xmm12, 0
  push rax
  pextrq rax, xmm12, 1
  push rax
  pextrq rax, xmm11, 0
  push rax
  pextrq rax, xmm11, 1
  push rax
  pextrq rax, xmm10, 0
  push rax
  pextrq rax, xmm10, 1
  push rax
  pextrq rax, xmm9, 0
  push rax
  pextrq rax, xmm9, 1
  push rax
  pextrq rax, xmm8, 0
  push rax
  pextrq rax, xmm8, 1
  push rax
  pextrq rax, xmm7, 0
  push rax
  pextrq rax, xmm7, 1
  push rax
  pextrq rax, xmm6, 0
  push rax
  pextrq rax, xmm6, 1
  push rax
  mov r14, rcx
  mov r13, rdx
  mov rax, r8
  mov r11, r9
  mov r10, qword ptr [rsp + 264]
  mov r8, qword ptr [rsp + 272]
  mov rbx, qword ptr [rsp + 280]
  mov r15, qword ptr [rsp + 288]
  movdqu xmm7, xmmword ptr [r10 + 0]
  mov r12, 579005069656919567
  pinsrq xmm8, r12, 0
  mov r12, 283686952306183
  pinsrq xmm8, r12, 1
  pxor xmm0, xmm0
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pshufb xmm0, xmm8
  movdqu xmm11, xmm0
  pshufb xmm7, xmm8
  mov r12, 2
  pinsrd xmm7, r12d, 0
  pxor xmm1, xmm1
  cmp r11, 0
  jbe L22
  mov rcx, r11
  shr rcx, 4
  mov r9, rax
  cmp rcx, 0
  je L24
  mov rdx, 0
  jmp L27
ALIGN 16
L26:
  movdqu xmm2, xmmword ptr [r9 + 0]
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  add rdx, 1
  add r9, 16
ALIGN 16
L27:
  cmp rdx, rcx
  jne L26
  jmp L25
L24:
L25:
  mov rax, r11
  and rax, 15
  cmp rax, 0
  jne L28
  jmp L29
L28:
  movdqu xmm2, xmmword ptr [r9 + 0]
  cmp rax, 8
  jae L30
  mov rcx, 0
  pinsrq xmm2, rcx, 1
  mov rcx, rax
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 0
  and rcx, rdx
  pinsrq xmm2, rcx, 0
  jmp L31
L30:
  mov rcx, rax
  sub rcx, 8
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 1
  and rcx, rdx
  pinsrq xmm2, rcx, 1
L31:
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
L29:
  jmp L23
L22:
L23:
  mov rax, r14
  mov rcx, r13
  cmp rcx, 0
  jbe L32
  mov rsi, rcx
  and rsi, 15
  shr rcx, 4
  mov rdx, rcx
  shr rdx, 2
  and rcx, 3
  cmp rdx, 0
  jbe L34
  mov r9, rax
  mov r10, rbx
  pshufb xmm7, xmm8
  movdqu xmm9, xmm7
  mov rax, 579005069656919567
  pinsrq xmm0, rax, 0
  mov rax, 579005069656919567
  pinsrq xmm0, rax, 1
  pshufb xmm9, xmm0
  movdqu xmm10, xmm9
  pxor xmm3, xmm3
  mov rax, 1
  pinsrd xmm3, eax, 2
  paddd xmm9, xmm3
  mov rax, 3
  pinsrd xmm3, eax, 2
  mov rax, 2
  pinsrd xmm3, eax, 0
  paddd xmm10, xmm3
  pshufb xmm9, xmm8
  pshufb xmm10, xmm8
  pextrq rdi, xmm7, 0
  mov rax, 283686952306183
  pinsrq xmm0, rax, 0
  mov rax, 579005069656919567
  pinsrq xmm0, rax, 1
  pxor xmm15, xmm15
  mov rax, 4
  pinsrd xmm15, eax, 0
  mov rax, 4
  pinsrd xmm15, eax, 2
  jmp L37
ALIGN 16
L36:
  pinsrq xmm2, rdi, 0
  pinsrq xmm12, rdi, 0
  pinsrq xmm13, rdi, 0
  pinsrq xmm14, rdi, 0
  shufpd xmm2, xmm9, 2
  shufpd xmm12, xmm9, 0
  shufpd xmm13, xmm10, 2
  shufpd xmm14, xmm10, 0
  pshufb xmm9, xmm0
  pshufb xmm10, xmm0
  movdqu xmm3, xmmword ptr [r8 + 0]
  movdqu xmm4, xmmword ptr [r8 + 16]
  movdqu xmm5, xmmword ptr [r8 + 32]
  movdqu xmm6, xmmword ptr [r8 + 48]
  paddd xmm9, xmm15
  paddd xmm10, xmm15
  pxor xmm2, xmm3
  pxor xmm12, xmm3
  pxor xmm13, xmm3
  pxor xmm14, xmm3
  pshufb xmm9, xmm0
  pshufb xmm10, xmm0
  aesenc xmm2, xmm4
  aesenc xmm12, xmm4
  aesenc xmm13, xmm4
  aesenc xmm14, xmm4
  aesenc xmm2, xmm5
  aesenc xmm12, xmm5
  aesenc xmm13, xmm5
  aesenc xmm14, xmm5
  aesenc xmm2, xmm6
  aesenc xmm12, xmm6
  aesenc xmm13, xmm6
  aesenc xmm14, xmm6
  movdqu xmm3, xmmword ptr [r8 + 64]
  movdqu xmm4, xmmword ptr [r8 + 80]
  movdqu xmm5, xmmword ptr [r8 + 96]
  movdqu xmm6, xmmword ptr [r8 + 112]
  aesenc xmm2, xmm3
  aesenc xmm12, xmm3
  aesenc xmm13, xmm3
  aesenc xmm14, xmm3
  aesenc xmm2, xmm4
  aesenc xmm12, xmm4
  aesenc xmm13, xmm4
  aesenc xmm14, xmm4
  aesenc xmm2, xmm5
  aesenc xmm12, xmm5
  aesenc xmm13, xmm5
  aesenc xmm14, xmm5
  aesenc xmm2, xmm6
  aesenc xmm12, xmm6
  aesenc xmm13, xmm6
  aesenc xmm14, xmm6
  movdqu xmm3, xmmword ptr [r8 + 128]
  movdqu xmm4, xmmword ptr [r8 + 144]
  movdqu xmm5, xmmword ptr [r8 + 160]
  aesenc xmm2, xmm3
  aesenc xmm12, xmm3
  aesenc xmm13, xmm3
  aesenc xmm14, xmm3
  aesenc xmm2, xmm4
  aesenc xmm12, xmm4
  aesenc xmm13, xmm4
  aesenc xmm14, xmm4
  aesenclast xmm2, xmm5
  aesenclast xmm12, xmm5
  aesenclast xmm13, xmm5
  aesenclast xmm14, xmm5
  movdqu xmm7, xmmword ptr [r9 + 0]
  pxor xmm2, xmm7
  movdqu xmm7, xmmword ptr [r9 + 16]
  pxor xmm12, xmm7
  movdqu xmm7, xmmword ptr [r9 + 32]
  pxor xmm13, xmm7
  movdqu xmm7, xmmword ptr [r9 + 48]
  pxor xmm14, xmm7
  movdqu xmmword ptr [r10 + 0], xmm2
  movdqu xmmword ptr [r10 + 16], xmm12
  movdqu xmmword ptr [r10 + 32], xmm13
  movdqu xmmword ptr [r10 + 48], xmm14
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  movdqu xmm2, xmm12
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  movdqu xmm2, xmm13
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  movdqu xmm2, xmm14
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  sub rdx, 1
  add r9, 64
  add r10, 64
ALIGN 16
L37:
  cmp rdx, 0
  ja L36
  movdqu xmm7, xmm9
  pinsrq xmm7, rdi, 0
  pshufb xmm7, xmm8
  mov rax, r9
  mov rbx, r10
  jmp L35
L34:
L35:
  mov rdx, 0
  mov r9, rax
  mov r10, rbx
  pxor xmm10, xmm10
  mov r12, 1
  pinsrd xmm10, r12d, 0
  jmp L39
ALIGN 16
L38:
  movdqu xmm0, xmm7
  pshufb xmm0, xmm8
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  movdqu xmm2, xmmword ptr [r9 + 0]
  pxor xmm2, xmm0
  movdqu xmmword ptr [r10 + 0], xmm2
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  add rdx, 1
  add r9, 16
  add r10, 16
  paddd xmm7, xmm10
ALIGN 16
L39:
  cmp rdx, rcx
  jne L38
  cmp rsi, 0
  jne L40
  jmp L41
L40:
  movdqu xmm3, xmm1
  movdqu xmm2, xmmword ptr [r9 + 0]
  movdqu xmm1, xmm2
  movdqu xmm0, xmm7
  mov r12, 579005069656919567
  pinsrq xmm2, r12, 0
  mov r12, 283686952306183
  pinsrq xmm2, r12, 1
  pshufb xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pxor xmm1, xmm0
  movdqu xmmword ptr [r10 + 0], xmm1
  mov rax, rsi
  mov r9, r10
  movdqu xmm1, xmm3
  movdqu xmm2, xmmword ptr [r9 + 0]
  cmp rax, 8
  jae L42
  mov rcx, 0
  pinsrq xmm2, rcx, 1
  mov rcx, rax
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 0
  and rcx, rdx
  pinsrq xmm2, rcx, 0
  jmp L43
L42:
  mov rcx, rax
  sub rcx, 8
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 1
  and rcx, rdx
  pinsrq xmm2, rcx, 1
L43:
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
L41:
  jmp L33
L32:
L33:
  pxor xmm2, xmm2
  mov rax, r13
  imul rax, 8
  pinsrd xmm2, eax, 0
  mov rax, r11
  imul rax, 8
  pinsrd xmm2, eax, 2
  pshufb xmm2, xmm8
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  mov r12, 1
  pinsrd xmm7, r12d, 0
  movdqu xmm0, xmm7
  mov r12, 579005069656919567
  pinsrq xmm2, r12, 0
  mov r12, 283686952306183
  pinsrq xmm2, r12, 1
  pshufb xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pxor xmm1, xmm0
  movdqu xmmword ptr [r15 + 0], xmm1
  pop rax
  pinsrq xmm6, rax, 1
  pop rax
  pinsrq xmm6, rax, 0
  pop rax
  pinsrq xmm7, rax, 1
  pop rax
  pinsrq xmm7, rax, 0
  pop rax
  pinsrq xmm8, rax, 1
  pop rax
  pinsrq xmm8, rax, 0
  pop rax
  pinsrq xmm9, rax, 1
  pop rax
  pinsrq xmm9, rax, 0
  pop rax
  pinsrq xmm10, rax, 1
  pop rax
  pinsrq xmm10, rax, 0
  pop rax
  pinsrq xmm11, rax, 1
  pop rax
  pinsrq xmm11, rax, 0
  pop rax
  pinsrq xmm12, rax, 1
  pop rax
  pinsrq xmm12, rax, 0
  pop rax
  pinsrq xmm13, rax, 1
  pop rax
  pinsrq xmm13, rax, 0
  pop rax
  pinsrq xmm14, rax, 1
  pop rax
  pinsrq xmm14, rax, 0
  pop rax
  pinsrq xmm15, rax, 1
  pop rax
  pinsrq xmm15, rax, 0
  pop rbx
  pop rbp
  pop rdi
  pop rsi
  pop r12
  pop r13
  pop r14
  pop r15
  ret
gcm128_encrypt endp
ALIGN 16
old_gcm128_decrypt proc
  mov r9, rcx
  push r15
  push r14
  push r13
  push r12
  push rsi
  push rdi
  push rbp
  push rbx
  pextrq rax, xmm15, 0
  push rax
  pextrq rax, xmm15, 1
  push rax
  pextrq rax, xmm14, 0
  push rax
  pextrq rax, xmm14, 1
  push rax
  pextrq rax, xmm13, 0
  push rax
  pextrq rax, xmm13, 1
  push rax
  pextrq rax, xmm12, 0
  push rax
  pextrq rax, xmm12, 1
  push rax
  pextrq rax, xmm11, 0
  push rax
  pextrq rax, xmm11, 1
  push rax
  pextrq rax, xmm10, 0
  push rax
  pextrq rax, xmm10, 1
  push rax
  pextrq rax, xmm9, 0
  push rax
  pextrq rax, xmm9, 1
  push rax
  pextrq rax, xmm8, 0
  push rax
  pextrq rax, xmm8, 1
  push rax
  pextrq rax, xmm7, 0
  push rax
  pextrq rax, xmm7, 1
  push rax
  pextrq rax, xmm6, 0
  push rax
  pextrq rax, xmm6, 1
  push rax
  mov r14, qword ptr [r9 + 0]
  mov r13, qword ptr [r9 + 8]
  mov rax, qword ptr [r9 + 16]
  mov r11, qword ptr [r9 + 24]
  mov r10, qword ptr [r9 + 32]
  mov r8, qword ptr [r9 + 40]
  mov rbx, qword ptr [r9 + 48]
  mov r15, qword ptr [r9 + 56]
  movdqu xmm7, xmmword ptr [r10 + 0]
  mov r12, 579005069656919567
  pinsrq xmm8, r12, 0
  mov r12, 283686952306183
  pinsrq xmm8, r12, 1
  pxor xmm0, xmm0
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pshufb xmm0, xmm8
  movdqu xmm11, xmm0
  pshufb xmm7, xmm8
  mov r12, 2
  pinsrd xmm7, r12d, 0
  pxor xmm1, xmm1
  cmp r11, 0
  jbe L44
  mov rcx, r11
  shr rcx, 4
  mov r9, rax
  cmp rcx, 0
  je L46
  mov rdx, 0
  jmp L49
ALIGN 16
L48:
  movdqu xmm2, xmmword ptr [r9 + 0]
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  add rdx, 1
  add r9, 16
ALIGN 16
L49:
  cmp rdx, rcx
  jne L48
  jmp L47
L46:
L47:
  mov rax, r11
  and rax, 15
  cmp rax, 0
  jne L50
  jmp L51
L50:
  movdqu xmm2, xmmword ptr [r9 + 0]
  cmp rax, 8
  jae L52
  mov rcx, 0
  pinsrq xmm2, rcx, 1
  mov rcx, rax
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 0
  and rcx, rdx
  pinsrq xmm2, rcx, 0
  jmp L53
L52:
  mov rcx, rax
  sub rcx, 8
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 1
  and rcx, rdx
  pinsrq xmm2, rcx, 1
L53:
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
L51:
  jmp L45
L44:
L45:
  mov rax, r14
  mov rcx, r13
  cmp rcx, 0
  jbe L54
  mov rsi, rcx
  and rsi, 15
  shr rcx, 4
  mov rdx, 0
  mov r9, rax
  mov r10, rbx
  pxor xmm10, xmm10
  mov r12, 1
  pinsrd xmm10, r12d, 0
  jmp L57
ALIGN 16
L56:
  movdqu xmm0, xmmword ptr [r9 + 0]
  movdqu xmm2, xmm0
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  movdqu xmm3, xmm0
  movdqu xmm0, xmm7
  pshufb xmm0, xmm8
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pxor xmm3, xmm0
  movdqu xmmword ptr [r10 + 0], xmm3
  add rdx, 1
  add r9, 16
  add r10, 16
  paddd xmm7, xmm10
ALIGN 16
L57:
  cmp rdx, rcx
  jne L56
  cmp rsi, 0
  jne L58
  jmp L59
L58:
  movdqu xmm3, xmm1
  movdqu xmm2, xmmword ptr [r9 + 0]
  movdqu xmm1, xmm2
  movdqu xmm0, xmm7
  mov r12, 579005069656919567
  pinsrq xmm2, r12, 0
  mov r12, 283686952306183
  pinsrq xmm2, r12, 1
  pshufb xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pxor xmm1, xmm0
  movdqu xmmword ptr [r10 + 0], xmm1
  mov rax, rsi
  movdqu xmm1, xmm3
  movdqu xmm2, xmmword ptr [r9 + 0]
  cmp rax, 8
  jae L60
  mov rcx, 0
  pinsrq xmm2, rcx, 1
  mov rcx, rax
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 0
  and rcx, rdx
  pinsrq xmm2, rcx, 0
  jmp L61
L60:
  mov rcx, rax
  sub rcx, 8
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 1
  and rcx, rdx
  pinsrq xmm2, rcx, 1
L61:
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
L59:
  jmp L55
L54:
L55:
  pxor xmm2, xmm2
  mov rax, r13
  imul rax, 8
  pinsrd xmm2, eax, 0
  mov rax, r11
  imul rax, 8
  pinsrd xmm2, eax, 2
  pshufb xmm2, xmm8
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  mov r12, 1
  pinsrd xmm7, r12d, 0
  movdqu xmm0, xmm7
  mov r12, 579005069656919567
  pinsrq xmm2, r12, 0
  mov r12, 283686952306183
  pinsrq xmm2, r12, 1
  pshufb xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pxor xmm1, xmm0
  movdqu xmm0, xmmword ptr [r15 + 0]
  pcmpeqd xmm0, xmm1
  pextrq rdx, xmm0, 0
  cmp rdx, 18446744073709551615
  jne L62
  mov rax, 0
  jmp L63
L62:
  mov rax, 1
L63:
  pextrq rdx, xmm0, 1
  cmp rdx, 18446744073709551615
  jne L64
  mov rdx, 0
  jmp L65
L64:
  mov rdx, 1
L65:
  add rax, rdx
  mov rdx, rax
  pop rax
  pinsrq xmm6, rax, 1
  pop rax
  pinsrq xmm6, rax, 0
  pop rax
  pinsrq xmm7, rax, 1
  pop rax
  pinsrq xmm7, rax, 0
  pop rax
  pinsrq xmm8, rax, 1
  pop rax
  pinsrq xmm8, rax, 0
  pop rax
  pinsrq xmm9, rax, 1
  pop rax
  pinsrq xmm9, rax, 0
  pop rax
  pinsrq xmm10, rax, 1
  pop rax
  pinsrq xmm10, rax, 0
  pop rax
  pinsrq xmm11, rax, 1
  pop rax
  pinsrq xmm11, rax, 0
  pop rax
  pinsrq xmm12, rax, 1
  pop rax
  pinsrq xmm12, rax, 0
  pop rax
  pinsrq xmm13, rax, 1
  pop rax
  pinsrq xmm13, rax, 0
  pop rax
  pinsrq xmm14, rax, 1
  pop rax
  pinsrq xmm14, rax, 0
  pop rax
  pinsrq xmm15, rax, 1
  pop rax
  pinsrq xmm15, rax, 0
  pop rbx
  pop rbp
  pop rdi
  pop rsi
  pop r12
  pop r13
  pop r14
  pop r15
  mov rax, rdx
  ret
old_gcm128_decrypt endp
ALIGN 16
gcm128_decrypt proc
  push r15
  push r14
  push r13
  push r12
  push rsi
  push rdi
  push rbp
  push rbx
  pextrq rax, xmm15, 0
  push rax
  pextrq rax, xmm15, 1
  push rax
  pextrq rax, xmm14, 0
  push rax
  pextrq rax, xmm14, 1
  push rax
  pextrq rax, xmm13, 0
  push rax
  pextrq rax, xmm13, 1
  push rax
  pextrq rax, xmm12, 0
  push rax
  pextrq rax, xmm12, 1
  push rax
  pextrq rax, xmm11, 0
  push rax
  pextrq rax, xmm11, 1
  push rax
  pextrq rax, xmm10, 0
  push rax
  pextrq rax, xmm10, 1
  push rax
  pextrq rax, xmm9, 0
  push rax
  pextrq rax, xmm9, 1
  push rax
  pextrq rax, xmm8, 0
  push rax
  pextrq rax, xmm8, 1
  push rax
  pextrq rax, xmm7, 0
  push rax
  pextrq rax, xmm7, 1
  push rax
  pextrq rax, xmm6, 0
  push rax
  pextrq rax, xmm6, 1
  push rax
  mov r14, rcx
  mov r13, rdx
  mov rax, r8
  mov r11, r9
  mov r10, qword ptr [rsp + 264]
  mov r8, qword ptr [rsp + 272]
  mov rbx, qword ptr [rsp + 280]
  mov r15, qword ptr [rsp + 288]
  movdqu xmm7, xmmword ptr [r10 + 0]
  mov r12, 579005069656919567
  pinsrq xmm8, r12, 0
  mov r12, 283686952306183
  pinsrq xmm8, r12, 1
  pxor xmm0, xmm0
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pshufb xmm0, xmm8
  movdqu xmm11, xmm0
  pshufb xmm7, xmm8
  mov r12, 2
  pinsrd xmm7, r12d, 0
  pxor xmm1, xmm1
  cmp r11, 0
  jbe L66
  mov rcx, r11
  shr rcx, 4
  mov r9, rax
  cmp rcx, 0
  je L68
  mov rdx, 0
  jmp L71
ALIGN 16
L70:
  movdqu xmm2, xmmword ptr [r9 + 0]
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  add rdx, 1
  add r9, 16
ALIGN 16
L71:
  cmp rdx, rcx
  jne L70
  jmp L69
L68:
L69:
  mov rax, r11
  and rax, 15
  cmp rax, 0
  jne L72
  jmp L73
L72:
  movdqu xmm2, xmmword ptr [r9 + 0]
  cmp rax, 8
  jae L74
  mov rcx, 0
  pinsrq xmm2, rcx, 1
  mov rcx, rax
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 0
  and rcx, rdx
  pinsrq xmm2, rcx, 0
  jmp L75
L74:
  mov rcx, rax
  sub rcx, 8
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 1
  and rcx, rdx
  pinsrq xmm2, rcx, 1
L75:
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
L73:
  jmp L67
L66:
L67:
  mov rax, r14
  mov rcx, r13
  cmp rcx, 0
  jbe L76
  mov rsi, rcx
  and rsi, 15
  shr rcx, 4
  mov rdx, 0
  mov r9, rax
  mov r10, rbx
  pxor xmm10, xmm10
  mov r12, 1
  pinsrd xmm10, r12d, 0
  jmp L79
ALIGN 16
L78:
  movdqu xmm0, xmmword ptr [r9 + 0]
  movdqu xmm2, xmm0
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  movdqu xmm3, xmm0
  movdqu xmm0, xmm7
  pshufb xmm0, xmm8
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pxor xmm3, xmm0
  movdqu xmmword ptr [r10 + 0], xmm3
  add rdx, 1
  add r9, 16
  add r10, 16
  paddd xmm7, xmm10
ALIGN 16
L79:
  cmp rdx, rcx
  jne L78
  cmp rsi, 0
  jne L80
  jmp L81
L80:
  movdqu xmm3, xmm1
  movdqu xmm2, xmmword ptr [r9 + 0]
  movdqu xmm1, xmm2
  movdqu xmm0, xmm7
  mov r12, 579005069656919567
  pinsrq xmm2, r12, 0
  mov r12, 283686952306183
  pinsrq xmm2, r12, 1
  pshufb xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pxor xmm1, xmm0
  movdqu xmmword ptr [r10 + 0], xmm1
  mov rax, rsi
  movdqu xmm1, xmm3
  movdqu xmm2, xmmword ptr [r9 + 0]
  cmp rax, 8
  jae L82
  mov rcx, 0
  pinsrq xmm2, rcx, 1
  mov rcx, rax
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 0
  and rcx, rdx
  pinsrq xmm2, rcx, 0
  jmp L83
L82:
  mov rcx, rax
  sub rcx, 8
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 1
  and rcx, rdx
  pinsrq xmm2, rcx, 1
L83:
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
L81:
  jmp L77
L76:
L77:
  pxor xmm2, xmm2
  mov rax, r13
  imul rax, 8
  pinsrd xmm2, eax, 0
  mov rax, r11
  imul rax, 8
  pinsrd xmm2, eax, 2
  pshufb xmm2, xmm8
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  mov r12, 1
  pinsrd xmm7, r12d, 0
  movdqu xmm0, xmm7
  mov r12, 579005069656919567
  pinsrq xmm2, r12, 0
  mov r12, 283686952306183
  pinsrq xmm2, r12, 1
  pshufb xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pxor xmm1, xmm0
  movdqu xmm0, xmmword ptr [r15 + 0]
  pcmpeqd xmm0, xmm1
  pextrq rdx, xmm0, 0
  cmp rdx, 18446744073709551615
  jne L84
  mov rax, 0
  jmp L85
L84:
  mov rax, 1
L85:
  pextrq rdx, xmm0, 1
  cmp rdx, 18446744073709551615
  jne L86
  mov rdx, 0
  jmp L87
L86:
  mov rdx, 1
L87:
  add rax, rdx
  pop rdx
  pinsrq xmm6, rdx, 1
  pop rdx
  pinsrq xmm6, rdx, 0
  pop rdx
  pinsrq xmm7, rdx, 1
  pop rdx
  pinsrq xmm7, rdx, 0
  pop rdx
  pinsrq xmm8, rdx, 1
  pop rdx
  pinsrq xmm8, rdx, 0
  pop rdx
  pinsrq xmm9, rdx, 1
  pop rdx
  pinsrq xmm9, rdx, 0
  pop rdx
  pinsrq xmm10, rdx, 1
  pop rdx
  pinsrq xmm10, rdx, 0
  pop rdx
  pinsrq xmm11, rdx, 1
  pop rdx
  pinsrq xmm11, rdx, 0
  pop rdx
  pinsrq xmm12, rdx, 1
  pop rdx
  pinsrq xmm12, rdx, 0
  pop rdx
  pinsrq xmm13, rdx, 1
  pop rdx
  pinsrq xmm13, rdx, 0
  pop rdx
  pinsrq xmm14, rdx, 1
  pop rdx
  pinsrq xmm14, rdx, 0
  pop rdx
  pinsrq xmm15, rdx, 1
  pop rdx
  pinsrq xmm15, rdx, 0
  pop rbx
  pop rbp
  pop rdi
  pop rsi
  pop r12
  pop r13
  pop r14
  pop r15
  ret
gcm128_decrypt endp
ALIGN 16
old_gcm256_encrypt proc
  mov r9, rcx
  push r15
  push r14
  push r13
  push r12
  push rsi
  push rdi
  push rbp
  push rbx
  pextrq rax, xmm15, 0
  push rax
  pextrq rax, xmm15, 1
  push rax
  pextrq rax, xmm14, 0
  push rax
  pextrq rax, xmm14, 1
  push rax
  pextrq rax, xmm13, 0
  push rax
  pextrq rax, xmm13, 1
  push rax
  pextrq rax, xmm12, 0
  push rax
  pextrq rax, xmm12, 1
  push rax
  pextrq rax, xmm11, 0
  push rax
  pextrq rax, xmm11, 1
  push rax
  pextrq rax, xmm10, 0
  push rax
  pextrq rax, xmm10, 1
  push rax
  pextrq rax, xmm9, 0
  push rax
  pextrq rax, xmm9, 1
  push rax
  pextrq rax, xmm8, 0
  push rax
  pextrq rax, xmm8, 1
  push rax
  pextrq rax, xmm7, 0
  push rax
  pextrq rax, xmm7, 1
  push rax
  pextrq rax, xmm6, 0
  push rax
  pextrq rax, xmm6, 1
  push rax
  mov r14, qword ptr [r9 + 0]
  mov r13, qword ptr [r9 + 8]
  mov rax, qword ptr [r9 + 16]
  mov r11, qword ptr [r9 + 24]
  mov r10, qword ptr [r9 + 32]
  mov r8, qword ptr [r9 + 40]
  mov rbx, qword ptr [r9 + 48]
  mov r15, qword ptr [r9 + 56]
  movdqu xmm7, xmmword ptr [r10 + 0]
  mov r12, 579005069656919567
  pinsrq xmm8, r12, 0
  mov r12, 283686952306183
  pinsrq xmm8, r12, 1
  pxor xmm0, xmm0
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 176]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 192]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 208]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 224]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pshufb xmm0, xmm8
  movdqu xmm11, xmm0
  pshufb xmm7, xmm8
  mov r12, 2
  pinsrd xmm7, r12d, 0
  pxor xmm1, xmm1
  cmp r11, 0
  jbe L88
  mov rcx, r11
  shr rcx, 4
  mov r9, rax
  cmp rcx, 0
  je L90
  mov rdx, 0
  jmp L93
ALIGN 16
L92:
  movdqu xmm2, xmmword ptr [r9 + 0]
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  add rdx, 1
  add r9, 16
ALIGN 16
L93:
  cmp rdx, rcx
  jne L92
  jmp L91
L90:
L91:
  mov rax, r11
  and rax, 15
  cmp rax, 0
  jne L94
  jmp L95
L94:
  movdqu xmm2, xmmword ptr [r9 + 0]
  cmp rax, 8
  jae L96
  mov rcx, 0
  pinsrq xmm2, rcx, 1
  mov rcx, rax
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 0
  and rcx, rdx
  pinsrq xmm2, rcx, 0
  jmp L97
L96:
  mov rcx, rax
  sub rcx, 8
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 1
  and rcx, rdx
  pinsrq xmm2, rcx, 1
L97:
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
L95:
  jmp L89
L88:
L89:
  mov rax, r14
  mov rcx, r13
  cmp rcx, 0
  jbe L98
  mov rsi, rcx
  and rsi, 15
  shr rcx, 4
  mov rdx, rcx
  shr rdx, 2
  and rcx, 3
  cmp rdx, 0
  jbe L100
  mov r9, rax
  mov r10, rbx
  pshufb xmm7, xmm8
  movdqu xmm9, xmm7
  mov rax, 579005069656919567
  pinsrq xmm0, rax, 0
  mov rax, 579005069656919567
  pinsrq xmm0, rax, 1
  pshufb xmm9, xmm0
  movdqu xmm10, xmm9
  pxor xmm3, xmm3
  mov rax, 1
  pinsrd xmm3, eax, 2
  paddd xmm9, xmm3
  mov rax, 3
  pinsrd xmm3, eax, 2
  mov rax, 2
  pinsrd xmm3, eax, 0
  paddd xmm10, xmm3
  pshufb xmm9, xmm8
  pshufb xmm10, xmm8
  pextrq rdi, xmm7, 0
  mov rax, 283686952306183
  pinsrq xmm0, rax, 0
  mov rax, 579005069656919567
  pinsrq xmm0, rax, 1
  pxor xmm15, xmm15
  mov rax, 4
  pinsrd xmm15, eax, 0
  mov rax, 4
  pinsrd xmm15, eax, 2
  jmp L103
ALIGN 16
L102:
  pinsrq xmm2, rdi, 0
  pinsrq xmm12, rdi, 0
  pinsrq xmm13, rdi, 0
  pinsrq xmm14, rdi, 0
  shufpd xmm2, xmm9, 2
  shufpd xmm12, xmm9, 0
  shufpd xmm13, xmm10, 2
  shufpd xmm14, xmm10, 0
  pshufb xmm9, xmm0
  pshufb xmm10, xmm0
  movdqu xmm3, xmmword ptr [r8 + 0]
  movdqu xmm4, xmmword ptr [r8 + 16]
  movdqu xmm5, xmmword ptr [r8 + 32]
  movdqu xmm6, xmmword ptr [r8 + 48]
  paddd xmm9, xmm15
  paddd xmm10, xmm15
  pxor xmm2, xmm3
  pxor xmm12, xmm3
  pxor xmm13, xmm3
  pxor xmm14, xmm3
  pshufb xmm9, xmm0
  pshufb xmm10, xmm0
  aesenc xmm2, xmm4
  aesenc xmm12, xmm4
  aesenc xmm13, xmm4
  aesenc xmm14, xmm4
  aesenc xmm2, xmm5
  aesenc xmm12, xmm5
  aesenc xmm13, xmm5
  aesenc xmm14, xmm5
  aesenc xmm2, xmm6
  aesenc xmm12, xmm6
  aesenc xmm13, xmm6
  aesenc xmm14, xmm6
  movdqu xmm3, xmmword ptr [r8 + 64]
  movdqu xmm4, xmmword ptr [r8 + 80]
  movdqu xmm5, xmmword ptr [r8 + 96]
  movdqu xmm6, xmmword ptr [r8 + 112]
  aesenc xmm2, xmm3
  aesenc xmm12, xmm3
  aesenc xmm13, xmm3
  aesenc xmm14, xmm3
  aesenc xmm2, xmm4
  aesenc xmm12, xmm4
  aesenc xmm13, xmm4
  aesenc xmm14, xmm4
  aesenc xmm2, xmm5
  aesenc xmm12, xmm5
  aesenc xmm13, xmm5
  aesenc xmm14, xmm5
  aesenc xmm2, xmm6
  aesenc xmm12, xmm6
  aesenc xmm13, xmm6
  aesenc xmm14, xmm6
  movdqu xmm3, xmmword ptr [r8 + 128]
  movdqu xmm4, xmmword ptr [r8 + 144]
  movdqu xmm5, xmmword ptr [r8 + 160]
  aesenc xmm2, xmm3
  aesenc xmm12, xmm3
  aesenc xmm13, xmm3
  aesenc xmm14, xmm3
  aesenc xmm2, xmm4
  aesenc xmm12, xmm4
  aesenc xmm13, xmm4
  aesenc xmm14, xmm4
  movdqu xmm3, xmm5
  movdqu xmm4, xmmword ptr [r8 + 176]
  movdqu xmm5, xmmword ptr [r8 + 192]
  movdqu xmm6, xmmword ptr [r8 + 208]
  aesenc xmm2, xmm3
  aesenc xmm12, xmm3
  aesenc xmm13, xmm3
  aesenc xmm14, xmm3
  aesenc xmm2, xmm4
  aesenc xmm12, xmm4
  aesenc xmm13, xmm4
  aesenc xmm14, xmm4
  aesenc xmm2, xmm5
  aesenc xmm12, xmm5
  aesenc xmm13, xmm5
  aesenc xmm14, xmm5
  aesenc xmm2, xmm6
  aesenc xmm12, xmm6
  aesenc xmm13, xmm6
  aesenc xmm14, xmm6
  movdqu xmm5, xmmword ptr [r8 + 224]
  aesenclast xmm2, xmm5
  aesenclast xmm12, xmm5
  aesenclast xmm13, xmm5
  aesenclast xmm14, xmm5
  movdqu xmm7, xmmword ptr [r9 + 0]
  pxor xmm2, xmm7
  movdqu xmm7, xmmword ptr [r9 + 16]
  pxor xmm12, xmm7
  movdqu xmm7, xmmword ptr [r9 + 32]
  pxor xmm13, xmm7
  movdqu xmm7, xmmword ptr [r9 + 48]
  pxor xmm14, xmm7
  movdqu xmmword ptr [r10 + 0], xmm2
  movdqu xmmword ptr [r10 + 16], xmm12
  movdqu xmmword ptr [r10 + 32], xmm13
  movdqu xmmword ptr [r10 + 48], xmm14
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  movdqu xmm2, xmm12
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  movdqu xmm2, xmm13
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  movdqu xmm2, xmm14
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  sub rdx, 1
  add r9, 64
  add r10, 64
ALIGN 16
L103:
  cmp rdx, 0
  ja L102
  movdqu xmm7, xmm9
  pinsrq xmm7, rdi, 0
  pshufb xmm7, xmm8
  mov rax, r9
  mov rbx, r10
  jmp L101
L100:
L101:
  mov rdx, 0
  mov r9, rax
  mov r10, rbx
  pxor xmm10, xmm10
  mov r12, 1
  pinsrd xmm10, r12d, 0
  jmp L105
ALIGN 16
L104:
  movdqu xmm0, xmm7
  pshufb xmm0, xmm8
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 176]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 192]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 208]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 224]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  movdqu xmm2, xmmword ptr [r9 + 0]
  pxor xmm2, xmm0
  movdqu xmmword ptr [r10 + 0], xmm2
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  add rdx, 1
  add r9, 16
  add r10, 16
  paddd xmm7, xmm10
ALIGN 16
L105:
  cmp rdx, rcx
  jne L104
  cmp rsi, 0
  jne L106
  jmp L107
L106:
  movdqu xmm3, xmm1
  movdqu xmm2, xmmword ptr [r9 + 0]
  movdqu xmm1, xmm2
  movdqu xmm0, xmm7
  mov r12, 579005069656919567
  pinsrq xmm2, r12, 0
  mov r12, 283686952306183
  pinsrq xmm2, r12, 1
  pshufb xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 176]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 192]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 208]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 224]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pxor xmm1, xmm0
  movdqu xmmword ptr [r10 + 0], xmm1
  mov rax, rsi
  mov r9, r10
  movdqu xmm1, xmm3
  movdqu xmm2, xmmword ptr [r9 + 0]
  cmp rax, 8
  jae L108
  mov rcx, 0
  pinsrq xmm2, rcx, 1
  mov rcx, rax
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 0
  and rcx, rdx
  pinsrq xmm2, rcx, 0
  jmp L109
L108:
  mov rcx, rax
  sub rcx, 8
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 1
  and rcx, rdx
  pinsrq xmm2, rcx, 1
L109:
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
L107:
  jmp L99
L98:
L99:
  pxor xmm2, xmm2
  mov rax, r13
  imul rax, 8
  pinsrd xmm2, eax, 0
  mov rax, r11
  imul rax, 8
  pinsrd xmm2, eax, 2
  pshufb xmm2, xmm8
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  mov r12, 1
  pinsrd xmm7, r12d, 0
  movdqu xmm0, xmm7
  mov r12, 579005069656919567
  pinsrq xmm2, r12, 0
  mov r12, 283686952306183
  pinsrq xmm2, r12, 1
  pshufb xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 176]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 192]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 208]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 224]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pxor xmm1, xmm0
  movdqu xmmword ptr [r15 + 0], xmm1
  pop rax
  pinsrq xmm6, rax, 1
  pop rax
  pinsrq xmm6, rax, 0
  pop rax
  pinsrq xmm7, rax, 1
  pop rax
  pinsrq xmm7, rax, 0
  pop rax
  pinsrq xmm8, rax, 1
  pop rax
  pinsrq xmm8, rax, 0
  pop rax
  pinsrq xmm9, rax, 1
  pop rax
  pinsrq xmm9, rax, 0
  pop rax
  pinsrq xmm10, rax, 1
  pop rax
  pinsrq xmm10, rax, 0
  pop rax
  pinsrq xmm11, rax, 1
  pop rax
  pinsrq xmm11, rax, 0
  pop rax
  pinsrq xmm12, rax, 1
  pop rax
  pinsrq xmm12, rax, 0
  pop rax
  pinsrq xmm13, rax, 1
  pop rax
  pinsrq xmm13, rax, 0
  pop rax
  pinsrq xmm14, rax, 1
  pop rax
  pinsrq xmm14, rax, 0
  pop rax
  pinsrq xmm15, rax, 1
  pop rax
  pinsrq xmm15, rax, 0
  pop rbx
  pop rbp
  pop rdi
  pop rsi
  pop r12
  pop r13
  pop r14
  pop r15
  ret
old_gcm256_encrypt endp
ALIGN 16
gcm256_encrypt proc
  push r15
  push r14
  push r13
  push r12
  push rsi
  push rdi
  push rbp
  push rbx
  pextrq rax, xmm15, 0
  push rax
  pextrq rax, xmm15, 1
  push rax
  pextrq rax, xmm14, 0
  push rax
  pextrq rax, xmm14, 1
  push rax
  pextrq rax, xmm13, 0
  push rax
  pextrq rax, xmm13, 1
  push rax
  pextrq rax, xmm12, 0
  push rax
  pextrq rax, xmm12, 1
  push rax
  pextrq rax, xmm11, 0
  push rax
  pextrq rax, xmm11, 1
  push rax
  pextrq rax, xmm10, 0
  push rax
  pextrq rax, xmm10, 1
  push rax
  pextrq rax, xmm9, 0
  push rax
  pextrq rax, xmm9, 1
  push rax
  pextrq rax, xmm8, 0
  push rax
  pextrq rax, xmm8, 1
  push rax
  pextrq rax, xmm7, 0
  push rax
  pextrq rax, xmm7, 1
  push rax
  pextrq rax, xmm6, 0
  push rax
  pextrq rax, xmm6, 1
  push rax
  mov r14, rcx
  mov r13, rdx
  mov rax, r8
  mov r11, r9
  mov r10, qword ptr [rsp + 264]
  mov r8, qword ptr [rsp + 272]
  mov rbx, qword ptr [rsp + 280]
  mov r15, qword ptr [rsp + 288]
  movdqu xmm7, xmmword ptr [r10 + 0]
  mov r12, 579005069656919567
  pinsrq xmm8, r12, 0
  mov r12, 283686952306183
  pinsrq xmm8, r12, 1
  pxor xmm0, xmm0
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 176]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 192]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 208]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 224]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pshufb xmm0, xmm8
  movdqu xmm11, xmm0
  pshufb xmm7, xmm8
  mov r12, 2
  pinsrd xmm7, r12d, 0
  pxor xmm1, xmm1
  cmp r11, 0
  jbe L110
  mov rcx, r11
  shr rcx, 4
  mov r9, rax
  cmp rcx, 0
  je L112
  mov rdx, 0
  jmp L115
ALIGN 16
L114:
  movdqu xmm2, xmmword ptr [r9 + 0]
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  add rdx, 1
  add r9, 16
ALIGN 16
L115:
  cmp rdx, rcx
  jne L114
  jmp L113
L112:
L113:
  mov rax, r11
  and rax, 15
  cmp rax, 0
  jne L116
  jmp L117
L116:
  movdqu xmm2, xmmword ptr [r9 + 0]
  cmp rax, 8
  jae L118
  mov rcx, 0
  pinsrq xmm2, rcx, 1
  mov rcx, rax
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 0
  and rcx, rdx
  pinsrq xmm2, rcx, 0
  jmp L119
L118:
  mov rcx, rax
  sub rcx, 8
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 1
  and rcx, rdx
  pinsrq xmm2, rcx, 1
L119:
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
L117:
  jmp L111
L110:
L111:
  mov rax, r14
  mov rcx, r13
  cmp rcx, 0
  jbe L120
  mov rsi, rcx
  and rsi, 15
  shr rcx, 4
  mov rdx, rcx
  shr rdx, 2
  and rcx, 3
  cmp rdx, 0
  jbe L122
  mov r9, rax
  mov r10, rbx
  pshufb xmm7, xmm8
  movdqu xmm9, xmm7
  mov rax, 579005069656919567
  pinsrq xmm0, rax, 0
  mov rax, 579005069656919567
  pinsrq xmm0, rax, 1
  pshufb xmm9, xmm0
  movdqu xmm10, xmm9
  pxor xmm3, xmm3
  mov rax, 1
  pinsrd xmm3, eax, 2
  paddd xmm9, xmm3
  mov rax, 3
  pinsrd xmm3, eax, 2
  mov rax, 2
  pinsrd xmm3, eax, 0
  paddd xmm10, xmm3
  pshufb xmm9, xmm8
  pshufb xmm10, xmm8
  pextrq rdi, xmm7, 0
  mov rax, 283686952306183
  pinsrq xmm0, rax, 0
  mov rax, 579005069656919567
  pinsrq xmm0, rax, 1
  pxor xmm15, xmm15
  mov rax, 4
  pinsrd xmm15, eax, 0
  mov rax, 4
  pinsrd xmm15, eax, 2
  jmp L125
ALIGN 16
L124:
  pinsrq xmm2, rdi, 0
  pinsrq xmm12, rdi, 0
  pinsrq xmm13, rdi, 0
  pinsrq xmm14, rdi, 0
  shufpd xmm2, xmm9, 2
  shufpd xmm12, xmm9, 0
  shufpd xmm13, xmm10, 2
  shufpd xmm14, xmm10, 0
  pshufb xmm9, xmm0
  pshufb xmm10, xmm0
  movdqu xmm3, xmmword ptr [r8 + 0]
  movdqu xmm4, xmmword ptr [r8 + 16]
  movdqu xmm5, xmmword ptr [r8 + 32]
  movdqu xmm6, xmmword ptr [r8 + 48]
  paddd xmm9, xmm15
  paddd xmm10, xmm15
  pxor xmm2, xmm3
  pxor xmm12, xmm3
  pxor xmm13, xmm3
  pxor xmm14, xmm3
  pshufb xmm9, xmm0
  pshufb xmm10, xmm0
  aesenc xmm2, xmm4
  aesenc xmm12, xmm4
  aesenc xmm13, xmm4
  aesenc xmm14, xmm4
  aesenc xmm2, xmm5
  aesenc xmm12, xmm5
  aesenc xmm13, xmm5
  aesenc xmm14, xmm5
  aesenc xmm2, xmm6
  aesenc xmm12, xmm6
  aesenc xmm13, xmm6
  aesenc xmm14, xmm6
  movdqu xmm3, xmmword ptr [r8 + 64]
  movdqu xmm4, xmmword ptr [r8 + 80]
  movdqu xmm5, xmmword ptr [r8 + 96]
  movdqu xmm6, xmmword ptr [r8 + 112]
  aesenc xmm2, xmm3
  aesenc xmm12, xmm3
  aesenc xmm13, xmm3
  aesenc xmm14, xmm3
  aesenc xmm2, xmm4
  aesenc xmm12, xmm4
  aesenc xmm13, xmm4
  aesenc xmm14, xmm4
  aesenc xmm2, xmm5
  aesenc xmm12, xmm5
  aesenc xmm13, xmm5
  aesenc xmm14, xmm5
  aesenc xmm2, xmm6
  aesenc xmm12, xmm6
  aesenc xmm13, xmm6
  aesenc xmm14, xmm6
  movdqu xmm3, xmmword ptr [r8 + 128]
  movdqu xmm4, xmmword ptr [r8 + 144]
  movdqu xmm5, xmmword ptr [r8 + 160]
  aesenc xmm2, xmm3
  aesenc xmm12, xmm3
  aesenc xmm13, xmm3
  aesenc xmm14, xmm3
  aesenc xmm2, xmm4
  aesenc xmm12, xmm4
  aesenc xmm13, xmm4
  aesenc xmm14, xmm4
  movdqu xmm3, xmm5
  movdqu xmm4, xmmword ptr [r8 + 176]
  movdqu xmm5, xmmword ptr [r8 + 192]
  movdqu xmm6, xmmword ptr [r8 + 208]
  aesenc xmm2, xmm3
  aesenc xmm12, xmm3
  aesenc xmm13, xmm3
  aesenc xmm14, xmm3
  aesenc xmm2, xmm4
  aesenc xmm12, xmm4
  aesenc xmm13, xmm4
  aesenc xmm14, xmm4
  aesenc xmm2, xmm5
  aesenc xmm12, xmm5
  aesenc xmm13, xmm5
  aesenc xmm14, xmm5
  aesenc xmm2, xmm6
  aesenc xmm12, xmm6
  aesenc xmm13, xmm6
  aesenc xmm14, xmm6
  movdqu xmm5, xmmword ptr [r8 + 224]
  aesenclast xmm2, xmm5
  aesenclast xmm12, xmm5
  aesenclast xmm13, xmm5
  aesenclast xmm14, xmm5
  movdqu xmm7, xmmword ptr [r9 + 0]
  pxor xmm2, xmm7
  movdqu xmm7, xmmword ptr [r9 + 16]
  pxor xmm12, xmm7
  movdqu xmm7, xmmword ptr [r9 + 32]
  pxor xmm13, xmm7
  movdqu xmm7, xmmword ptr [r9 + 48]
  pxor xmm14, xmm7
  movdqu xmmword ptr [r10 + 0], xmm2
  movdqu xmmword ptr [r10 + 16], xmm12
  movdqu xmmword ptr [r10 + 32], xmm13
  movdqu xmmword ptr [r10 + 48], xmm14
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  movdqu xmm2, xmm12
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  movdqu xmm2, xmm13
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  movdqu xmm2, xmm14
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  sub rdx, 1
  add r9, 64
  add r10, 64
ALIGN 16
L125:
  cmp rdx, 0
  ja L124
  movdqu xmm7, xmm9
  pinsrq xmm7, rdi, 0
  pshufb xmm7, xmm8
  mov rax, r9
  mov rbx, r10
  jmp L123
L122:
L123:
  mov rdx, 0
  mov r9, rax
  mov r10, rbx
  pxor xmm10, xmm10
  mov r12, 1
  pinsrd xmm10, r12d, 0
  jmp L127
ALIGN 16
L126:
  movdqu xmm0, xmm7
  pshufb xmm0, xmm8
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 176]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 192]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 208]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 224]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  movdqu xmm2, xmmword ptr [r9 + 0]
  pxor xmm2, xmm0
  movdqu xmmword ptr [r10 + 0], xmm2
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  add rdx, 1
  add r9, 16
  add r10, 16
  paddd xmm7, xmm10
ALIGN 16
L127:
  cmp rdx, rcx
  jne L126
  cmp rsi, 0
  jne L128
  jmp L129
L128:
  movdqu xmm3, xmm1
  movdqu xmm2, xmmword ptr [r9 + 0]
  movdqu xmm1, xmm2
  movdqu xmm0, xmm7
  mov r12, 579005069656919567
  pinsrq xmm2, r12, 0
  mov r12, 283686952306183
  pinsrq xmm2, r12, 1
  pshufb xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 176]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 192]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 208]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 224]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pxor xmm1, xmm0
  movdqu xmmword ptr [r10 + 0], xmm1
  mov rax, rsi
  mov r9, r10
  movdqu xmm1, xmm3
  movdqu xmm2, xmmword ptr [r9 + 0]
  cmp rax, 8
  jae L130
  mov rcx, 0
  pinsrq xmm2, rcx, 1
  mov rcx, rax
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 0
  and rcx, rdx
  pinsrq xmm2, rcx, 0
  jmp L131
L130:
  mov rcx, rax
  sub rcx, 8
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 1
  and rcx, rdx
  pinsrq xmm2, rcx, 1
L131:
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
L129:
  jmp L121
L120:
L121:
  pxor xmm2, xmm2
  mov rax, r13
  imul rax, 8
  pinsrd xmm2, eax, 0
  mov rax, r11
  imul rax, 8
  pinsrd xmm2, eax, 2
  pshufb xmm2, xmm8
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  mov r12, 1
  pinsrd xmm7, r12d, 0
  movdqu xmm0, xmm7
  mov r12, 579005069656919567
  pinsrq xmm2, r12, 0
  mov r12, 283686952306183
  pinsrq xmm2, r12, 1
  pshufb xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 176]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 192]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 208]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 224]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pxor xmm1, xmm0
  movdqu xmmword ptr [r15 + 0], xmm1
  pop rax
  pinsrq xmm6, rax, 1
  pop rax
  pinsrq xmm6, rax, 0
  pop rax
  pinsrq xmm7, rax, 1
  pop rax
  pinsrq xmm7, rax, 0
  pop rax
  pinsrq xmm8, rax, 1
  pop rax
  pinsrq xmm8, rax, 0
  pop rax
  pinsrq xmm9, rax, 1
  pop rax
  pinsrq xmm9, rax, 0
  pop rax
  pinsrq xmm10, rax, 1
  pop rax
  pinsrq xmm10, rax, 0
  pop rax
  pinsrq xmm11, rax, 1
  pop rax
  pinsrq xmm11, rax, 0
  pop rax
  pinsrq xmm12, rax, 1
  pop rax
  pinsrq xmm12, rax, 0
  pop rax
  pinsrq xmm13, rax, 1
  pop rax
  pinsrq xmm13, rax, 0
  pop rax
  pinsrq xmm14, rax, 1
  pop rax
  pinsrq xmm14, rax, 0
  pop rax
  pinsrq xmm15, rax, 1
  pop rax
  pinsrq xmm15, rax, 0
  pop rbx
  pop rbp
  pop rdi
  pop rsi
  pop r12
  pop r13
  pop r14
  pop r15
  ret
gcm256_encrypt endp
ALIGN 16
old_gcm256_decrypt proc
  mov r9, rcx
  push r15
  push r14
  push r13
  push r12
  push rsi
  push rdi
  push rbp
  push rbx
  pextrq rax, xmm15, 0
  push rax
  pextrq rax, xmm15, 1
  push rax
  pextrq rax, xmm14, 0
  push rax
  pextrq rax, xmm14, 1
  push rax
  pextrq rax, xmm13, 0
  push rax
  pextrq rax, xmm13, 1
  push rax
  pextrq rax, xmm12, 0
  push rax
  pextrq rax, xmm12, 1
  push rax
  pextrq rax, xmm11, 0
  push rax
  pextrq rax, xmm11, 1
  push rax
  pextrq rax, xmm10, 0
  push rax
  pextrq rax, xmm10, 1
  push rax
  pextrq rax, xmm9, 0
  push rax
  pextrq rax, xmm9, 1
  push rax
  pextrq rax, xmm8, 0
  push rax
  pextrq rax, xmm8, 1
  push rax
  pextrq rax, xmm7, 0
  push rax
  pextrq rax, xmm7, 1
  push rax
  pextrq rax, xmm6, 0
  push rax
  pextrq rax, xmm6, 1
  push rax
  mov r14, qword ptr [r9 + 0]
  mov r13, qword ptr [r9 + 8]
  mov rax, qword ptr [r9 + 16]
  mov r11, qword ptr [r9 + 24]
  mov r10, qword ptr [r9 + 32]
  mov r8, qword ptr [r9 + 40]
  mov rbx, qword ptr [r9 + 48]
  mov r15, qword ptr [r9 + 56]
  movdqu xmm7, xmmword ptr [r10 + 0]
  mov r12, 579005069656919567
  pinsrq xmm8, r12, 0
  mov r12, 283686952306183
  pinsrq xmm8, r12, 1
  pxor xmm0, xmm0
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 176]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 192]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 208]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 224]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pshufb xmm0, xmm8
  movdqu xmm11, xmm0
  pshufb xmm7, xmm8
  mov r12, 2
  pinsrd xmm7, r12d, 0
  pxor xmm1, xmm1
  cmp r11, 0
  jbe L132
  mov rcx, r11
  shr rcx, 4
  mov r9, rax
  cmp rcx, 0
  je L134
  mov rdx, 0
  jmp L137
ALIGN 16
L136:
  movdqu xmm2, xmmword ptr [r9 + 0]
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  add rdx, 1
  add r9, 16
ALIGN 16
L137:
  cmp rdx, rcx
  jne L136
  jmp L135
L134:
L135:
  mov rax, r11
  and rax, 15
  cmp rax, 0
  jne L138
  jmp L139
L138:
  movdqu xmm2, xmmword ptr [r9 + 0]
  cmp rax, 8
  jae L140
  mov rcx, 0
  pinsrq xmm2, rcx, 1
  mov rcx, rax
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 0
  and rcx, rdx
  pinsrq xmm2, rcx, 0
  jmp L141
L140:
  mov rcx, rax
  sub rcx, 8
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 1
  and rcx, rdx
  pinsrq xmm2, rcx, 1
L141:
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
L139:
  jmp L133
L132:
L133:
  mov rax, r14
  mov rcx, r13
  cmp rcx, 0
  jbe L142
  mov rsi, rcx
  and rsi, 15
  shr rcx, 4
  mov rdx, 0
  mov r9, rax
  mov r10, rbx
  pxor xmm10, xmm10
  mov r12, 1
  pinsrd xmm10, r12d, 0
  jmp L145
ALIGN 16
L144:
  movdqu xmm0, xmmword ptr [r9 + 0]
  movdqu xmm2, xmm0
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  movdqu xmm3, xmm0
  movdqu xmm0, xmm7
  pshufb xmm0, xmm8
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 176]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 192]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 208]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 224]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pxor xmm3, xmm0
  movdqu xmmword ptr [r10 + 0], xmm3
  add rdx, 1
  add r9, 16
  add r10, 16
  paddd xmm7, xmm10
ALIGN 16
L145:
  cmp rdx, rcx
  jne L144
  cmp rsi, 0
  jne L146
  jmp L147
L146:
  movdqu xmm3, xmm1
  movdqu xmm2, xmmword ptr [r9 + 0]
  movdqu xmm1, xmm2
  movdqu xmm0, xmm7
  mov r12, 579005069656919567
  pinsrq xmm2, r12, 0
  mov r12, 283686952306183
  pinsrq xmm2, r12, 1
  pshufb xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 176]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 192]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 208]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 224]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pxor xmm1, xmm0
  movdqu xmmword ptr [r10 + 0], xmm1
  mov rax, rsi
  movdqu xmm1, xmm3
  movdqu xmm2, xmmword ptr [r9 + 0]
  cmp rax, 8
  jae L148
  mov rcx, 0
  pinsrq xmm2, rcx, 1
  mov rcx, rax
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 0
  and rcx, rdx
  pinsrq xmm2, rcx, 0
  jmp L149
L148:
  mov rcx, rax
  sub rcx, 8
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 1
  and rcx, rdx
  pinsrq xmm2, rcx, 1
L149:
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
L147:
  jmp L143
L142:
L143:
  pxor xmm2, xmm2
  mov rax, r13
  imul rax, 8
  pinsrd xmm2, eax, 0
  mov rax, r11
  imul rax, 8
  pinsrd xmm2, eax, 2
  pshufb xmm2, xmm8
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  mov r12, 1
  pinsrd xmm7, r12d, 0
  movdqu xmm0, xmm7
  mov r12, 579005069656919567
  pinsrq xmm2, r12, 0
  mov r12, 283686952306183
  pinsrq xmm2, r12, 1
  pshufb xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 176]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 192]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 208]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 224]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pxor xmm1, xmm0
  movdqu xmm0, xmmword ptr [r15 + 0]
  pcmpeqd xmm0, xmm1
  pextrq rdx, xmm0, 0
  cmp rdx, 18446744073709551615
  jne L150
  mov rax, 0
  jmp L151
L150:
  mov rax, 1
L151:
  pextrq rdx, xmm0, 1
  cmp rdx, 18446744073709551615
  jne L152
  mov rdx, 0
  jmp L153
L152:
  mov rdx, 1
L153:
  add rax, rdx
  mov rdx, rax
  pop rax
  pinsrq xmm6, rax, 1
  pop rax
  pinsrq xmm6, rax, 0
  pop rax
  pinsrq xmm7, rax, 1
  pop rax
  pinsrq xmm7, rax, 0
  pop rax
  pinsrq xmm8, rax, 1
  pop rax
  pinsrq xmm8, rax, 0
  pop rax
  pinsrq xmm9, rax, 1
  pop rax
  pinsrq xmm9, rax, 0
  pop rax
  pinsrq xmm10, rax, 1
  pop rax
  pinsrq xmm10, rax, 0
  pop rax
  pinsrq xmm11, rax, 1
  pop rax
  pinsrq xmm11, rax, 0
  pop rax
  pinsrq xmm12, rax, 1
  pop rax
  pinsrq xmm12, rax, 0
  pop rax
  pinsrq xmm13, rax, 1
  pop rax
  pinsrq xmm13, rax, 0
  pop rax
  pinsrq xmm14, rax, 1
  pop rax
  pinsrq xmm14, rax, 0
  pop rax
  pinsrq xmm15, rax, 1
  pop rax
  pinsrq xmm15, rax, 0
  pop rbx
  pop rbp
  pop rdi
  pop rsi
  pop r12
  pop r13
  pop r14
  pop r15
  mov rax, rdx
  ret
old_gcm256_decrypt endp
ALIGN 16
gcm256_decrypt proc
  push r15
  push r14
  push r13
  push r12
  push rsi
  push rdi
  push rbp
  push rbx
  pextrq rax, xmm15, 0
  push rax
  pextrq rax, xmm15, 1
  push rax
  pextrq rax, xmm14, 0
  push rax
  pextrq rax, xmm14, 1
  push rax
  pextrq rax, xmm13, 0
  push rax
  pextrq rax, xmm13, 1
  push rax
  pextrq rax, xmm12, 0
  push rax
  pextrq rax, xmm12, 1
  push rax
  pextrq rax, xmm11, 0
  push rax
  pextrq rax, xmm11, 1
  push rax
  pextrq rax, xmm10, 0
  push rax
  pextrq rax, xmm10, 1
  push rax
  pextrq rax, xmm9, 0
  push rax
  pextrq rax, xmm9, 1
  push rax
  pextrq rax, xmm8, 0
  push rax
  pextrq rax, xmm8, 1
  push rax
  pextrq rax, xmm7, 0
  push rax
  pextrq rax, xmm7, 1
  push rax
  pextrq rax, xmm6, 0
  push rax
  pextrq rax, xmm6, 1
  push rax
  mov r14, rcx
  mov r13, rdx
  mov rax, r8
  mov r11, r9
  mov r10, qword ptr [rsp + 264]
  mov r8, qword ptr [rsp + 272]
  mov rbx, qword ptr [rsp + 280]
  mov r15, qword ptr [rsp + 288]
  movdqu xmm7, xmmword ptr [r10 + 0]
  mov r12, 579005069656919567
  pinsrq xmm8, r12, 0
  mov r12, 283686952306183
  pinsrq xmm8, r12, 1
  pxor xmm0, xmm0
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 176]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 192]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 208]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 224]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pshufb xmm0, xmm8
  movdqu xmm11, xmm0
  pshufb xmm7, xmm8
  mov r12, 2
  pinsrd xmm7, r12d, 0
  pxor xmm1, xmm1
  cmp r11, 0
  jbe L154
  mov rcx, r11
  shr rcx, 4
  mov r9, rax
  cmp rcx, 0
  je L156
  mov rdx, 0
  jmp L159
ALIGN 16
L158:
  movdqu xmm2, xmmword ptr [r9 + 0]
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  add rdx, 1
  add r9, 16
ALIGN 16
L159:
  cmp rdx, rcx
  jne L158
  jmp L157
L156:
L157:
  mov rax, r11
  and rax, 15
  cmp rax, 0
  jne L160
  jmp L161
L160:
  movdqu xmm2, xmmword ptr [r9 + 0]
  cmp rax, 8
  jae L162
  mov rcx, 0
  pinsrq xmm2, rcx, 1
  mov rcx, rax
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 0
  and rcx, rdx
  pinsrq xmm2, rcx, 0
  jmp L163
L162:
  mov rcx, rax
  sub rcx, 8
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 1
  and rcx, rdx
  pinsrq xmm2, rcx, 1
L163:
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
L161:
  jmp L155
L154:
L155:
  mov rax, r14
  mov rcx, r13
  cmp rcx, 0
  jbe L164
  mov rsi, rcx
  and rsi, 15
  shr rcx, 4
  mov rdx, 0
  mov r9, rax
  mov r10, rbx
  pxor xmm10, xmm10
  mov r12, 1
  pinsrd xmm10, r12d, 0
  jmp L167
ALIGN 16
L166:
  movdqu xmm0, xmmword ptr [r9 + 0]
  movdqu xmm2, xmm0
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  movdqu xmm3, xmm0
  movdqu xmm0, xmm7
  pshufb xmm0, xmm8
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 176]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 192]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 208]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 224]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pxor xmm3, xmm0
  movdqu xmmword ptr [r10 + 0], xmm3
  add rdx, 1
  add r9, 16
  add r10, 16
  paddd xmm7, xmm10
ALIGN 16
L167:
  cmp rdx, rcx
  jne L166
  cmp rsi, 0
  jne L168
  jmp L169
L168:
  movdqu xmm3, xmm1
  movdqu xmm2, xmmword ptr [r9 + 0]
  movdqu xmm1, xmm2
  movdqu xmm0, xmm7
  mov r12, 579005069656919567
  pinsrq xmm2, r12, 0
  mov r12, 283686952306183
  pinsrq xmm2, r12, 1
  pshufb xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 176]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 192]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 208]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 224]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pxor xmm1, xmm0
  movdqu xmmword ptr [r10 + 0], xmm1
  mov rax, rsi
  movdqu xmm1, xmm3
  movdqu xmm2, xmmword ptr [r9 + 0]
  cmp rax, 8
  jae L170
  mov rcx, 0
  pinsrq xmm2, rcx, 1
  mov rcx, rax
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 0
  and rcx, rdx
  pinsrq xmm2, rcx, 0
  jmp L171
L170:
  mov rcx, rax
  sub rcx, 8
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 1
  and rcx, rdx
  pinsrq xmm2, rcx, 1
L171:
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
L169:
  jmp L165
L164:
L165:
  pxor xmm2, xmm2
  mov rax, r13
  imul rax, 8
  pinsrd xmm2, eax, 0
  mov rax, r11
  imul rax, 8
  pinsrd xmm2, eax, 2
  pshufb xmm2, xmm8
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  mov r12, 1
  pinsrd xmm7, r12d, 0
  movdqu xmm0, xmm7
  mov r12, 579005069656919567
  pinsrq xmm2, r12, 0
  mov r12, 283686952306183
  pinsrq xmm2, r12, 1
  pshufb xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 176]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 192]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 208]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 224]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pxor xmm1, xmm0
  movdqu xmm0, xmmword ptr [r15 + 0]
  pcmpeqd xmm0, xmm1
  pextrq rdx, xmm0, 0
  cmp rdx, 18446744073709551615
  jne L172
  mov rax, 0
  jmp L173
L172:
  mov rax, 1
L173:
  pextrq rdx, xmm0, 1
  cmp rdx, 18446744073709551615
  jne L174
  mov rdx, 0
  jmp L175
L174:
  mov rdx, 1
L175:
  add rax, rdx
  pop rdx
  pinsrq xmm6, rdx, 1
  pop rdx
  pinsrq xmm6, rdx, 0
  pop rdx
  pinsrq xmm7, rdx, 1
  pop rdx
  pinsrq xmm7, rdx, 0
  pop rdx
  pinsrq xmm8, rdx, 1
  pop rdx
  pinsrq xmm8, rdx, 0
  pop rdx
  pinsrq xmm9, rdx, 1
  pop rdx
  pinsrq xmm9, rdx, 0
  pop rdx
  pinsrq xmm10, rdx, 1
  pop rdx
  pinsrq xmm10, rdx, 0
  pop rdx
  pinsrq xmm11, rdx, 1
  pop rdx
  pinsrq xmm11, rdx, 0
  pop rdx
  pinsrq xmm12, rdx, 1
  pop rdx
  pinsrq xmm12, rdx, 0
  pop rdx
  pinsrq xmm13, rdx, 1
  pop rdx
  pinsrq xmm13, rdx, 0
  pop rdx
  pinsrq xmm14, rdx, 1
  pop rdx
  pinsrq xmm14, rdx, 0
  pop rdx
  pinsrq xmm15, rdx, 1
  pop rdx
  pinsrq xmm15, rdx, 0
  pop rbx
  pop rbp
  pop rdi
  pop rsi
  pop r12
  pop r13
  pop r14
  pop r15
  ret
gcm256_decrypt endp
ALIGN 16
gcm128_encrypt_opt proc
  push r15
  push r14
  push r13
  push r12
  push rsi
  push rdi
  push rbp
  push rbx
  pextrq rax, xmm15, 0
  push rax
  pextrq rax, xmm15, 1
  push rax
  pextrq rax, xmm14, 0
  push rax
  pextrq rax, xmm14, 1
  push rax
  pextrq rax, xmm13, 0
  push rax
  pextrq rax, xmm13, 1
  push rax
  pextrq rax, xmm12, 0
  push rax
  pextrq rax, xmm12, 1
  push rax
  pextrq rax, xmm11, 0
  push rax
  pextrq rax, xmm11, 1
  push rax
  pextrq rax, xmm10, 0
  push rax
  pextrq rax, xmm10, 1
  push rax
  pextrq rax, xmm9, 0
  push rax
  pextrq rax, xmm9, 1
  push rax
  pextrq rax, xmm8, 0
  push rax
  pextrq rax, xmm8, 1
  push rax
  pextrq rax, xmm7, 0
  push rax
  pextrq rax, xmm7, 1
  push rax
  pextrq rax, xmm6, 0
  push rax
  pextrq rax, xmm6, 1
  push rax
  mov rdi, rcx
  mov rsi, rdx
  mov rdx, r8
  mov rcx, r9
  mov r8, qword ptr [rsp + 264]
  mov r9, qword ptr [rsp + 272]
  mov rbp, qword ptr [rsp + 352]
  mov r13, r8
  mov r14, r9
  mov r12, 579005069656919567
  pinsrq xmm8, r12, 0
  mov r12, 283686952306183
  pinsrq xmm8, r12, 1
  mov rax, rdi
  mov r8, rcx
  mov r11, rdx
  movdqu xmm11, xmmword ptr [r9 + 32]
  pxor xmm1, xmm1
  mov rcx, r11
  cmp rcx, 0
  je L176
  mov rdx, 0
  mov r9, rax
  jmp L179
ALIGN 16
L178:
  movdqu xmm2, xmmword ptr [r9 + 0]
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  add rdx, 1
  add r9, 16
ALIGN 16
L179:
  cmp rdx, rcx
  jne L178
  jmp L177
L176:
L177:
  imul r11, 16
  cmp rsi, r11
  jbe L180
  mov r11, qword ptr [rsp + 280]
  movdqu xmm2, xmmword ptr [r11 + 0]
  mov rax, rsi
  and rax, 15
  cmp rax, 8
  jae L182
  mov rcx, 0
  pinsrq xmm2, rcx, 1
  mov rcx, rax
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 0
  and rcx, rdx
  pinsrq xmm2, rcx, 0
  jmp L183
L182:
  mov rcx, rax
  sub rcx, 8
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 1
  and rcx, rdx
  pinsrq xmm2, rcx, 1
L183:
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  jmp L181
L180:
L181:
  mov r15, rsi
  mov rdi, qword ptr [rsp + 288]
  mov rsi, qword ptr [rsp + 296]
  mov rdx, qword ptr [rsp + 304]
  mov rcx, r8
  mov r8, r13
  mov r9, r14
  movdqu xmm8, xmm1
  cmp rdx, 0
  jne L184
  lea r9, qword ptr [r9 + 32]
  movdqu xmm1, xmmword ptr [r8 + 0]
  mov r12, 579005069656919567
  pinsrq xmm0, r12, 0
  mov r12, 283686952306183
  pinsrq xmm0, r12, 1
  vpshufb xmm1, xmm1, xmm0
  mov rbx, 2
  pinsrd xmm1, ebx, 0
  vpshufb xmm1, xmm1, xmm0
  movdqu xmmword ptr [r8 + 0], xmm1
  jmp L185
L184:
  mov r12, 579005069656919567
  pinsrq xmm0, r12, 0
  mov r12, 283686952306183
  pinsrq xmm0, r12, 1
  movdqu xmm1, xmmword ptr [r8 + 0]
  vpshufb xmm8, xmm8, xmm0
  movdqu xmmword ptr [r8 + 0], xmm8
  add rcx, 128
  vpshufb xmm1, xmm1, xmm0
  mov rbx, 2
  pinsrd xmm1, ebx, 0
  vpshufb xmm1, xmm1, xmm0
  lea r14, qword ptr [rsi + 96]
  movdqu xmm4, xmmword ptr [rcx + -128]
  pxor xmm2, xmm2
  mov r11, 72057594037927936
  pinsrq xmm2, r11, 1
  movdqu xmm15, xmmword ptr [rcx + -112]
  mov r12, rcx
  sub r12, 96
  vpxor xmm9, xmm1, xmm4
  vpaddd xmm10, xmm1, xmm2
  vpaddd xmm11, xmm10, xmm2
  vpxor xmm10, xmm10, xmm4
  vpaddd xmm12, xmm11, xmm2
  vpxor xmm11, xmm11, xmm4
  vpaddd xmm13, xmm12, xmm2
  vpxor xmm12, xmm12, xmm4
  vpaddd xmm14, xmm13, xmm2
  vpxor xmm13, xmm13, xmm4
  vpaddd xmm1, xmm14, xmm2
  vpxor xmm14, xmm14, xmm4
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -96]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -80]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -64]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -48]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -32]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -16]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + 0]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + 16]
  movdqu xmm3, xmmword ptr [rcx + 32]
  vaesenc xmm9, xmm9, xmm15
  vpxor xmm4, xmm3, xmmword ptr [rdi + 0]
  vaesenc xmm10, xmm10, xmm15
  vpxor xmm5, xmm3, xmmword ptr [rdi + 16]
  vaesenc xmm11, xmm11, xmm15
  vpxor xmm6, xmm3, xmmword ptr [rdi + 32]
  vaesenc xmm12, xmm12, xmm15
  vpxor xmm8, xmm3, xmmword ptr [rdi + 48]
  vaesenc xmm13, xmm13, xmm15
  vpxor xmm2, xmm3, xmmword ptr [rdi + 64]
  vaesenc xmm14, xmm14, xmm15
  vpxor xmm3, xmm3, xmmword ptr [rdi + 80]
  lea rdi, qword ptr [rdi + 96]
  vaesenclast xmm9, xmm9, xmm4
  vaesenclast xmm10, xmm10, xmm5
  vaesenclast xmm11, xmm11, xmm6
  vaesenclast xmm12, xmm12, xmm8
  vaesenclast xmm13, xmm13, xmm2
  vaesenclast xmm14, xmm14, xmm3
  movdqu xmmword ptr [rsi + 0], xmm9
  movdqu xmmword ptr [rsi + 16], xmm10
  movdqu xmmword ptr [rsi + 32], xmm11
  movdqu xmmword ptr [rsi + 48], xmm12
  movdqu xmmword ptr [rsi + 64], xmm13
  movdqu xmmword ptr [rsi + 80], xmm14
  lea rsi, qword ptr [rsi + 96]
  vpshufb xmm8, xmm9, xmm0
  vpshufb xmm2, xmm10, xmm0
  movdqu xmmword ptr [rbp + 112], xmm8
  vpshufb xmm4, xmm11, xmm0
  movdqu xmmword ptr [rbp + 96], xmm2
  vpshufb xmm5, xmm12, xmm0
  movdqu xmmword ptr [rbp + 80], xmm4
  vpshufb xmm6, xmm13, xmm0
  movdqu xmmword ptr [rbp + 64], xmm5
  vpshufb xmm7, xmm14, xmm0
  movdqu xmmword ptr [rbp + 48], xmm6
  movdqu xmm4, xmmword ptr [rcx + -128]
  pxor xmm2, xmm2
  mov r11, 72057594037927936
  pinsrq xmm2, r11, 1
  movdqu xmm15, xmmword ptr [rcx + -112]
  mov r12, rcx
  sub r12, 96
  vpxor xmm9, xmm1, xmm4
  vpaddd xmm10, xmm1, xmm2
  vpaddd xmm11, xmm10, xmm2
  vpxor xmm10, xmm10, xmm4
  vpaddd xmm12, xmm11, xmm2
  vpxor xmm11, xmm11, xmm4
  vpaddd xmm13, xmm12, xmm2
  vpxor xmm12, xmm12, xmm4
  vpaddd xmm14, xmm13, xmm2
  vpxor xmm13, xmm13, xmm4
  vpaddd xmm1, xmm14, xmm2
  vpxor xmm14, xmm14, xmm4
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -96]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -80]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -64]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -48]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -32]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -16]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + 0]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + 16]
  movdqu xmm3, xmmword ptr [rcx + 32]
  vaesenc xmm9, xmm9, xmm15
  vpxor xmm4, xmm3, xmmword ptr [rdi + 0]
  vaesenc xmm10, xmm10, xmm15
  vpxor xmm5, xmm3, xmmword ptr [rdi + 16]
  vaesenc xmm11, xmm11, xmm15
  vpxor xmm6, xmm3, xmmword ptr [rdi + 32]
  vaesenc xmm12, xmm12, xmm15
  vpxor xmm8, xmm3, xmmword ptr [rdi + 48]
  vaesenc xmm13, xmm13, xmm15
  vpxor xmm2, xmm3, xmmword ptr [rdi + 64]
  vaesenc xmm14, xmm14, xmm15
  vpxor xmm3, xmm3, xmmword ptr [rdi + 80]
  lea rdi, qword ptr [rdi + 96]
  vaesenclast xmm9, xmm9, xmm4
  vaesenclast xmm10, xmm10, xmm5
  vaesenclast xmm11, xmm11, xmm6
  vaesenclast xmm12, xmm12, xmm8
  vaesenclast xmm13, xmm13, xmm2
  vaesenclast xmm14, xmm14, xmm3
  movdqu xmmword ptr [rsi + 0], xmm9
  movdqu xmmword ptr [rsi + 16], xmm10
  movdqu xmmword ptr [rsi + 32], xmm11
  movdqu xmmword ptr [rsi + 48], xmm12
  movdqu xmmword ptr [rsi + 64], xmm13
  movdqu xmmword ptr [rsi + 80], xmm14
  lea rsi, qword ptr [rsi + 96]
  sub rdx, 12
  movdqu xmm8, xmmword ptr [r8 + 0]
  lea r9, qword ptr [r9 + 32]
  pxor xmm2, xmm2
  mov r11, 72057594037927936
  pinsrq xmm2, r11, 1
  vpxor xmm4, xmm4, xmm4
  movdqu xmm15, xmmword ptr [rcx + -128]
  vpaddd xmm10, xmm1, xmm2
  vpaddd xmm11, xmm10, xmm2
  vpaddd xmm12, xmm11, xmm2
  vpaddd xmm13, xmm12, xmm2
  vpaddd xmm14, xmm13, xmm2
  vpxor xmm9, xmm1, xmm15
  movdqu xmmword ptr [rbp + 16], xmm4
  mov rbx, 14
  jmp L187
ALIGN 16
L186:
  add rbx, 6
  cmp rbx, 256
  jb L188
  mov r11, 579005069656919567
  pinsrq xmm0, r11, 0
  mov r11, 283686952306183
  pinsrq xmm0, r11, 1
  vpshufb xmm6, xmm1, xmm0
  pxor xmm5, xmm5
  mov r11, 1
  pinsrq xmm5, r11, 0
  vpaddd xmm10, xmm6, xmm5
  pxor xmm5, xmm5
  mov r11, 2
  pinsrq xmm5, r11, 0
  vpaddd xmm11, xmm6, xmm5
  movdqu xmm3, xmmword ptr [r9 + -32]
  vpaddd xmm12, xmm10, xmm5
  vpshufb xmm10, xmm10, xmm0
  vpaddd xmm13, xmm11, xmm5
  vpshufb xmm11, xmm11, xmm0
  vpxor xmm10, xmm10, xmm15
  vpaddd xmm14, xmm12, xmm5
  vpshufb xmm12, xmm12, xmm0
  vpxor xmm11, xmm11, xmm15
  vpaddd xmm1, xmm13, xmm5
  vpshufb xmm13, xmm13, xmm0
  vpshufb xmm14, xmm14, xmm0
  vpshufb xmm1, xmm1, xmm0
  sub rbx, 256
  jmp L189
L188:
  movdqu xmm3, xmmword ptr [r9 + -32]
  vpaddd xmm1, xmm2, xmm14
  vpxor xmm10, xmm10, xmm15
  vpxor xmm11, xmm11, xmm15
L189:
  movdqu xmmword ptr [r8 + 0], xmm1
  vpclmulqdq xmm5, xmm7, xmm3, 16
  vpxor xmm12, xmm12, xmm15
  movdqu xmm2, xmmword ptr [rcx + -112]
  vpclmulqdq xmm6, xmm7, xmm3, 1
  vaesenc xmm9, xmm9, xmm2
  movdqu xmm0, xmmword ptr [rbp + 48]
  vpxor xmm13, xmm13, xmm15
  vpclmulqdq xmm1, xmm7, xmm3, 0
  vaesenc xmm10, xmm10, xmm2
  vpxor xmm14, xmm14, xmm15
  vpclmulqdq xmm7, xmm7, xmm3, 17
  vaesenc xmm11, xmm11, xmm2
  movdqu xmm3, xmmword ptr [r9 + -16]
  vaesenc xmm12, xmm12, xmm2
  vpxor xmm6, xmm6, xmm5
  vpclmulqdq xmm5, xmm0, xmm3, 0
  vpxor xmm8, xmm8, xmm4
  vaesenc xmm13, xmm13, xmm2
  vpxor xmm4, xmm1, xmm5
  vpclmulqdq xmm1, xmm0, xmm3, 16
  vaesenc xmm14, xmm14, xmm2
  movdqu xmm15, xmmword ptr [rcx + -96]
  vpclmulqdq xmm2, xmm0, xmm3, 1
  vaesenc xmm9, xmm9, xmm15
  vpxor xmm8, xmm8, xmmword ptr [rbp + 16]
  vpclmulqdq xmm3, xmm0, xmm3, 17
  movdqu xmm0, xmmword ptr [rbp + 64]
  vaesenc xmm10, xmm10, xmm15
  movbe r13, qword ptr [r14 + 88]
  vaesenc xmm11, xmm11, xmm15
  movbe r12, qword ptr [r14 + 80]
  vaesenc xmm12, xmm12, xmm15
  mov qword ptr [rbp + 32], r13
  vaesenc xmm13, xmm13, xmm15
  mov qword ptr [rbp + 40], r12
  movdqu xmm5, xmmword ptr [r9 + 16]
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -80]
  vpxor xmm6, xmm6, xmm1
  vpclmulqdq xmm1, xmm0, xmm5, 0
  vaesenc xmm9, xmm9, xmm15
  vpxor xmm6, xmm6, xmm2
  vpclmulqdq xmm2, xmm0, xmm5, 16
  vaesenc xmm10, xmm10, xmm15
  vpxor xmm7, xmm7, xmm3
  vpclmulqdq xmm3, xmm0, xmm5, 1
  vaesenc xmm11, xmm11, xmm15
  vpclmulqdq xmm5, xmm0, xmm5, 17
  movdqu xmm0, xmmword ptr [rbp + 80]
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vpxor xmm4, xmm4, xmm1
  movdqu xmm1, xmmword ptr [r9 + 32]
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -64]
  vpxor xmm6, xmm6, xmm2
  vpclmulqdq xmm2, xmm0, xmm1, 0
  vaesenc xmm9, xmm9, xmm15
  vpxor xmm6, xmm6, xmm3
  vpclmulqdq xmm3, xmm0, xmm1, 16
  vaesenc xmm10, xmm10, xmm15
  movbe r13, qword ptr [r14 + 72]
  vpxor xmm7, xmm7, xmm5
  vpclmulqdq xmm5, xmm0, xmm1, 1
  vaesenc xmm11, xmm11, xmm15
  movbe r12, qword ptr [r14 + 64]
  vpclmulqdq xmm1, xmm0, xmm1, 17
  movdqu xmm0, xmmword ptr [rbp + 96]
  vaesenc xmm12, xmm12, xmm15
  mov qword ptr [rbp + 48], r13
  vaesenc xmm13, xmm13, xmm15
  mov qword ptr [rbp + 56], r12
  vpxor xmm4, xmm4, xmm2
  movdqu xmm2, xmmword ptr [r9 + 64]
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -48]
  vpxor xmm6, xmm6, xmm3
  vpclmulqdq xmm3, xmm0, xmm2, 0
  vaesenc xmm9, xmm9, xmm15
  vpxor xmm6, xmm6, xmm5
  vpclmulqdq xmm5, xmm0, xmm2, 16
  vaesenc xmm10, xmm10, xmm15
  movbe r13, qword ptr [r14 + 56]
  vpxor xmm7, xmm7, xmm1
  vpclmulqdq xmm1, xmm0, xmm2, 1
  vpxor xmm8, xmm8, xmmword ptr [rbp + 112]
  vaesenc xmm11, xmm11, xmm15
  movbe r12, qword ptr [r14 + 48]
  vpclmulqdq xmm2, xmm0, xmm2, 17
  vaesenc xmm12, xmm12, xmm15
  mov qword ptr [rbp + 64], r13
  vaesenc xmm13, xmm13, xmm15
  mov qword ptr [rbp + 72], r12
  vpxor xmm4, xmm4, xmm3
  movdqu xmm3, xmmword ptr [r9 + 80]
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -32]
  vpxor xmm6, xmm6, xmm5
  vpclmulqdq xmm5, xmm8, xmm3, 16
  vaesenc xmm9, xmm9, xmm15
  vpxor xmm6, xmm6, xmm1
  vpclmulqdq xmm1, xmm8, xmm3, 1
  vaesenc xmm10, xmm10, xmm15
  movbe r13, qword ptr [r14 + 40]
  vpxor xmm7, xmm7, xmm2
  vpclmulqdq xmm2, xmm8, xmm3, 0
  vaesenc xmm11, xmm11, xmm15
  movbe r12, qword ptr [r14 + 32]
  vpclmulqdq xmm8, xmm8, xmm3, 17
  vaesenc xmm12, xmm12, xmm15
  mov qword ptr [rbp + 80], r13
  vaesenc xmm13, xmm13, xmm15
  mov qword ptr [rbp + 88], r12
  vpxor xmm6, xmm6, xmm5
  vaesenc xmm14, xmm14, xmm15
  vpxor xmm6, xmm6, xmm1
  movdqu xmm15, xmmword ptr [rcx + -16]
  vpslldq xmm5, xmm6, 8
  vpxor xmm4, xmm4, xmm2
  pxor xmm3, xmm3
  mov r11, 13979173243358019584
  pinsrq xmm3, r11, 1
  vaesenc xmm9, xmm9, xmm15
  vpxor xmm7, xmm7, xmm8
  vaesenc xmm10, xmm10, xmm15
  vpxor xmm4, xmm4, xmm5
  movbe r13, qword ptr [r14 + 24]
  vaesenc xmm11, xmm11, xmm15
  movbe r12, qword ptr [r14 + 16]
  vpalignr xmm0, xmm4, xmm4, 8
  vpclmulqdq xmm4, xmm4, xmm3, 16
  mov qword ptr [rbp + 96], r13
  vaesenc xmm12, xmm12, xmm15
  mov qword ptr [rbp + 104], r12
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm1, xmmword ptr [rcx + 0]
  vaesenc xmm9, xmm9, xmm1
  movdqu xmm15, xmmword ptr [rcx + 16]
  vaesenc xmm10, xmm10, xmm1
  vpsrldq xmm6, xmm6, 8
  vaesenc xmm11, xmm11, xmm1
  vpxor xmm7, xmm7, xmm6
  vaesenc xmm12, xmm12, xmm1
  vpxor xmm4, xmm4, xmm0
  movbe r13, qword ptr [r14 + 8]
  vaesenc xmm13, xmm13, xmm1
  movbe r12, qword ptr [r14 + 0]
  vaesenc xmm14, xmm14, xmm1
  movdqu xmm1, xmmword ptr [rcx + 32]
  vaesenc xmm9, xmm9, xmm15
  movdqu xmmword ptr [rbp + 16], xmm7
  vpalignr xmm8, xmm4, xmm4, 8
  vaesenc xmm10, xmm10, xmm15
  vpclmulqdq xmm4, xmm4, xmm3, 16
  vpxor xmm2, xmm1, xmmword ptr [rdi + 0]
  vaesenc xmm11, xmm11, xmm15
  vpxor xmm0, xmm1, xmmword ptr [rdi + 16]
  vaesenc xmm12, xmm12, xmm15
  vpxor xmm5, xmm1, xmmword ptr [rdi + 32]
  vaesenc xmm13, xmm13, xmm15
  vpxor xmm6, xmm1, xmmword ptr [rdi + 48]
  vaesenc xmm14, xmm14, xmm15
  vpxor xmm7, xmm1, xmmword ptr [rdi + 64]
  vpxor xmm3, xmm1, xmmword ptr [rdi + 80]
  movdqu xmm1, xmmword ptr [r8 + 0]
  vaesenclast xmm9, xmm9, xmm2
  pxor xmm2, xmm2
  mov r11, 72057594037927936
  pinsrq xmm2, r11, 1
  vaesenclast xmm10, xmm10, xmm0
  vpaddd xmm0, xmm1, xmm2
  mov qword ptr [rbp + 112], r13
  lea rdi, qword ptr [rdi + 96]
  vaesenclast xmm11, xmm11, xmm5
  vpaddd xmm5, xmm0, xmm2
  mov qword ptr [rbp + 120], r12
  lea rsi, qword ptr [rsi + 96]
  movdqu xmm15, xmmword ptr [rcx + -128]
  vaesenclast xmm12, xmm12, xmm6
  vpaddd xmm6, xmm5, xmm2
  vaesenclast xmm13, xmm13, xmm7
  vpaddd xmm7, xmm6, xmm2
  vaesenclast xmm14, xmm14, xmm3
  vpaddd xmm3, xmm7, xmm2
  sub rdx, 6
  add r14, 96
  cmp rdx, 0
  jbe L190
  movdqu xmmword ptr [rsi + -96], xmm9
  vpxor xmm9, xmm1, xmm15
  movdqu xmmword ptr [rsi + -80], xmm10
  movdqu xmm10, xmm0
  movdqu xmmword ptr [rsi + -64], xmm11
  movdqu xmm11, xmm5
  movdqu xmmword ptr [rsi + -48], xmm12
  movdqu xmm12, xmm6
  movdqu xmmword ptr [rsi + -32], xmm13
  movdqu xmm13, xmm7
  movdqu xmmword ptr [rsi + -16], xmm14
  movdqu xmm14, xmm3
  movdqu xmm7, xmmword ptr [rbp + 32]
  jmp L191
L190:
  vpxor xmm8, xmm8, xmmword ptr [rbp + 16]
  vpxor xmm8, xmm8, xmm4
L191:
ALIGN 16
L187:
  cmp rdx, 0
  ja L186
  movdqu xmmword ptr [r8 + 0], xmm1
  movdqu xmm7, xmmword ptr [rbp + 32]
  pxor xmm4, xmm4
  movdqu xmmword ptr [rbp + 0], xmm4
  movdqu xmm3, xmmword ptr [r9 + -32]
  vpclmulqdq xmm1, xmm7, xmm3, 0
  vpclmulqdq xmm5, xmm7, xmm3, 16
  movdqu xmm0, xmmword ptr [rbp + 48]
  vpclmulqdq xmm6, xmm7, xmm3, 1
  vpclmulqdq xmm7, xmm7, xmm3, 17
  movdqu xmm3, xmmword ptr [r9 + -16]
  vpxor xmm6, xmm6, xmm5
  vpclmulqdq xmm5, xmm0, xmm3, 0
  vpxor xmm8, xmm8, xmm4
  vpxor xmm4, xmm1, xmm5
  vpclmulqdq xmm1, xmm0, xmm3, 16
  vpclmulqdq xmm2, xmm0, xmm3, 1
  vpxor xmm8, xmm8, xmmword ptr [rbp + 0]
  vpclmulqdq xmm3, xmm0, xmm3, 17
  movdqu xmm0, xmmword ptr [rbp + 64]
  movdqu xmm5, xmmword ptr [r9 + 16]
  vpxor xmm6, xmm6, xmm1
  vpclmulqdq xmm1, xmm0, xmm5, 0
  vpxor xmm6, xmm6, xmm2
  vpclmulqdq xmm2, xmm0, xmm5, 16
  vpxor xmm7, xmm7, xmm3
  vpclmulqdq xmm3, xmm0, xmm5, 1
  vpclmulqdq xmm5, xmm0, xmm5, 17
  movdqu xmm0, xmmword ptr [rbp + 80]
  vpxor xmm4, xmm4, xmm1
  movdqu xmm1, xmmword ptr [r9 + 32]
  vpxor xmm6, xmm6, xmm2
  vpclmulqdq xmm2, xmm0, xmm1, 0
  vpxor xmm6, xmm6, xmm3
  vpclmulqdq xmm3, xmm0, xmm1, 16
  vpxor xmm7, xmm7, xmm5
  vpclmulqdq xmm5, xmm0, xmm1, 1
  vpclmulqdq xmm1, xmm0, xmm1, 17
  movdqu xmm0, xmmword ptr [rbp + 96]
  vpxor xmm4, xmm4, xmm2
  movdqu xmm2, xmmword ptr [r9 + 64]
  vpxor xmm6, xmm6, xmm3
  vpclmulqdq xmm3, xmm0, xmm2, 0
  vpxor xmm6, xmm6, xmm5
  vpclmulqdq xmm5, xmm0, xmm2, 16
  vpxor xmm7, xmm7, xmm1
  vpclmulqdq xmm1, xmm0, xmm2, 1
  vpxor xmm8, xmm8, xmmword ptr [rbp + 112]
  vpclmulqdq xmm2, xmm0, xmm2, 17
  vpxor xmm4, xmm4, xmm3
  movdqu xmm3, xmmword ptr [r9 + 80]
  vpxor xmm6, xmm6, xmm5
  vpclmulqdq xmm5, xmm8, xmm3, 16
  vpxor xmm6, xmm6, xmm1
  vpclmulqdq xmm1, xmm8, xmm3, 1
  vpxor xmm7, xmm7, xmm2
  vpclmulqdq xmm2, xmm8, xmm3, 0
  vpclmulqdq xmm8, xmm8, xmm3, 17
  vpxor xmm6, xmm6, xmm5
  vpxor xmm6, xmm6, xmm1
  vpxor xmm4, xmm4, xmm2
  pxor xmm3, xmm3
  mov rax, 3254779904
  pinsrd xmm3, eax, 3
  vpxor xmm7, xmm7, xmm8
  vpslldq xmm5, xmm6, 8
  vpxor xmm4, xmm4, xmm5
  vpalignr xmm0, xmm4, xmm4, 8
  vpclmulqdq xmm4, xmm4, xmm3, 16
  vpsrldq xmm6, xmm6, 8
  vpxor xmm7, xmm7, xmm6
  vpxor xmm4, xmm0, xmm4
  vpalignr xmm8, xmm4, xmm4, 8
  vpclmulqdq xmm4, xmm4, xmm3, 16
  vpxor xmm8, xmm8, xmm7
  vpxor xmm8, xmm8, xmm4
  mov r12, 579005069656919567
  pinsrq xmm0, r12, 0
  mov r12, 283686952306183
  pinsrq xmm0, r12, 1
  movdqu xmmword ptr [rsi + -96], xmm9
  vpshufb xmm9, xmm9, xmm0
  vpxor xmm1, xmm1, xmm7
  movdqu xmmword ptr [rsi + -80], xmm10
  vpshufb xmm10, xmm10, xmm0
  movdqu xmmword ptr [rsi + -64], xmm11
  vpshufb xmm11, xmm11, xmm0
  movdqu xmmword ptr [rsi + -48], xmm12
  vpshufb xmm12, xmm12, xmm0
  movdqu xmmword ptr [rsi + -32], xmm13
  vpshufb xmm13, xmm13, xmm0
  movdqu xmmword ptr [rsi + -16], xmm14
  vpshufb xmm14, xmm14, xmm0
  pxor xmm4, xmm4
  movdqu xmm7, xmm14
  movdqu xmmword ptr [rbp + 0], xmm4
  movdqu xmmword ptr [rbp + 48], xmm13
  movdqu xmmword ptr [rbp + 64], xmm12
  movdqu xmmword ptr [rbp + 80], xmm11
  movdqu xmmword ptr [rbp + 96], xmm10
  movdqu xmmword ptr [rbp + 112], xmm9
  movdqu xmm3, xmmword ptr [r9 + -32]
  vpclmulqdq xmm1, xmm7, xmm3, 0
  vpclmulqdq xmm5, xmm7, xmm3, 16
  movdqu xmm0, xmmword ptr [rbp + 48]
  vpclmulqdq xmm6, xmm7, xmm3, 1
  vpclmulqdq xmm7, xmm7, xmm3, 17
  movdqu xmm3, xmmword ptr [r9 + -16]
  vpxor xmm6, xmm6, xmm5
  vpclmulqdq xmm5, xmm0, xmm3, 0
  vpxor xmm8, xmm8, xmm4
  vpxor xmm4, xmm1, xmm5
  vpclmulqdq xmm1, xmm0, xmm3, 16
  vpclmulqdq xmm2, xmm0, xmm3, 1
  vpxor xmm8, xmm8, xmmword ptr [rbp + 0]
  vpclmulqdq xmm3, xmm0, xmm3, 17
  movdqu xmm0, xmmword ptr [rbp + 64]
  movdqu xmm5, xmmword ptr [r9 + 16]
  vpxor xmm6, xmm6, xmm1
  vpclmulqdq xmm1, xmm0, xmm5, 0
  vpxor xmm6, xmm6, xmm2
  vpclmulqdq xmm2, xmm0, xmm5, 16
  vpxor xmm7, xmm7, xmm3
  vpclmulqdq xmm3, xmm0, xmm5, 1
  vpclmulqdq xmm5, xmm0, xmm5, 17
  movdqu xmm0, xmmword ptr [rbp + 80]
  vpxor xmm4, xmm4, xmm1
  movdqu xmm1, xmmword ptr [r9 + 32]
  vpxor xmm6, xmm6, xmm2
  vpclmulqdq xmm2, xmm0, xmm1, 0
  vpxor xmm6, xmm6, xmm3
  vpclmulqdq xmm3, xmm0, xmm1, 16
  vpxor xmm7, xmm7, xmm5
  vpclmulqdq xmm5, xmm0, xmm1, 1
  vpclmulqdq xmm1, xmm0, xmm1, 17
  movdqu xmm0, xmmword ptr [rbp + 96]
  vpxor xmm4, xmm4, xmm2
  movdqu xmm2, xmmword ptr [r9 + 64]
  vpxor xmm6, xmm6, xmm3
  vpclmulqdq xmm3, xmm0, xmm2, 0
  vpxor xmm6, xmm6, xmm5
  vpclmulqdq xmm5, xmm0, xmm2, 16
  vpxor xmm7, xmm7, xmm1
  vpclmulqdq xmm1, xmm0, xmm2, 1
  vpxor xmm8, xmm8, xmmword ptr [rbp + 112]
  vpclmulqdq xmm2, xmm0, xmm2, 17
  vpxor xmm4, xmm4, xmm3
  movdqu xmm3, xmmword ptr [r9 + 80]
  vpxor xmm6, xmm6, xmm5
  vpclmulqdq xmm5, xmm8, xmm3, 16
  vpxor xmm6, xmm6, xmm1
  vpclmulqdq xmm1, xmm8, xmm3, 1
  vpxor xmm7, xmm7, xmm2
  vpclmulqdq xmm2, xmm8, xmm3, 0
  vpclmulqdq xmm8, xmm8, xmm3, 17
  vpxor xmm6, xmm6, xmm5
  vpxor xmm6, xmm6, xmm1
  vpxor xmm4, xmm4, xmm2
  pxor xmm3, xmm3
  mov rax, 3254779904
  pinsrd xmm3, eax, 3
  vpxor xmm7, xmm7, xmm8
  vpslldq xmm5, xmm6, 8
  vpxor xmm4, xmm4, xmm5
  vpalignr xmm0, xmm4, xmm4, 8
  vpclmulqdq xmm4, xmm4, xmm3, 16
  vpsrldq xmm6, xmm6, 8
  vpxor xmm7, xmm7, xmm6
  vpxor xmm4, xmm0, xmm4
  vpalignr xmm8, xmm4, xmm4, 8
  vpclmulqdq xmm4, xmm4, xmm3, 16
  vpxor xmm8, xmm8, xmm7
  vpxor xmm8, xmm8, xmm4
  mov r12, 579005069656919567
  pinsrq xmm0, r12, 0
  mov r12, 283686952306183
  pinsrq xmm0, r12, 1
  vpshufb xmm8, xmm8, xmm0
  sub rcx, 128
L185:
  movdqu xmm7, xmmword ptr [r8 + 0]
  mov r8, rcx
  mov rax, qword ptr [rsp + 312]
  mov rbx, qword ptr [rsp + 320]
  mov rcx, qword ptr [rsp + 328]
  movdqu xmm1, xmm8
  mov r12, 579005069656919567
  pinsrq xmm8, r12, 0
  mov r12, 283686952306183
  pinsrq xmm8, r12, 1
  pshufb xmm7, xmm8
  movdqu xmm11, xmmword ptr [r9 + 0]
  mov rdx, 0
  mov r9, rax
  mov r10, rbx
  pxor xmm10, xmm10
  mov r12, 1
  pinsrd xmm10, r12d, 0
  jmp L193
ALIGN 16
L192:
  movdqu xmm0, xmm7
  pshufb xmm0, xmm8
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  movdqu xmm2, xmmword ptr [r9 + 0]
  pxor xmm2, xmm0
  movdqu xmmword ptr [r10 + 0], xmm2
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  add rdx, 1
  add r9, 16
  add r10, 16
  paddd xmm7, xmm10
ALIGN 16
L193:
  cmp rdx, rcx
  jne L192
  add rcx, qword ptr [rsp + 304]
  imul rcx, 16
  mov r13, qword ptr [rsp + 344]
  cmp r13, rcx
  jbe L194
  mov rax, qword ptr [rsp + 336]
  mov rbx, rax
  mov rcx, r13
  and rcx, 15
  movdqu xmm0, xmm7
  pshufb xmm0, xmm8
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  movdqu xmm2, xmmword ptr [rax + 0]
  pxor xmm2, xmm0
  movdqu xmmword ptr [rbx + 0], xmm2
  mov rax, rcx
  cmp rax, 8
  jae L196
  mov rcx, 0
  pinsrq xmm2, rcx, 1
  mov rcx, rax
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 0
  and rcx, rdx
  pinsrq xmm2, rcx, 0
  jmp L197
L196:
  mov rcx, rax
  sub rcx, 8
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 1
  and rcx, rdx
  pinsrq xmm2, rcx, 1
L197:
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  jmp L195
L194:
L195:
  mov r11, r15
  pxor xmm2, xmm2
  mov rax, r13
  imul rax, 8
  pinsrd xmm2, eax, 0
  mov rax, r11
  imul rax, 8
  pinsrd xmm2, eax, 2
  pshufb xmm2, xmm8
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  mov r12, 1
  pinsrd xmm7, r12d, 0
  movdqu xmm0, xmm7
  mov r12, 579005069656919567
  pinsrq xmm2, r12, 0
  mov r12, 283686952306183
  pinsrq xmm2, r12, 1
  pshufb xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pxor xmm1, xmm0
  mov r15, qword ptr [rsp + 360]
  movdqu xmmword ptr [r15 + 0], xmm1
  pop rax
  pinsrq xmm6, rax, 1
  pop rax
  pinsrq xmm6, rax, 0
  pop rax
  pinsrq xmm7, rax, 1
  pop rax
  pinsrq xmm7, rax, 0
  pop rax
  pinsrq xmm8, rax, 1
  pop rax
  pinsrq xmm8, rax, 0
  pop rax
  pinsrq xmm9, rax, 1
  pop rax
  pinsrq xmm9, rax, 0
  pop rax
  pinsrq xmm10, rax, 1
  pop rax
  pinsrq xmm10, rax, 0
  pop rax
  pinsrq xmm11, rax, 1
  pop rax
  pinsrq xmm11, rax, 0
  pop rax
  pinsrq xmm12, rax, 1
  pop rax
  pinsrq xmm12, rax, 0
  pop rax
  pinsrq xmm13, rax, 1
  pop rax
  pinsrq xmm13, rax, 0
  pop rax
  pinsrq xmm14, rax, 1
  pop rax
  pinsrq xmm14, rax, 0
  pop rax
  pinsrq xmm15, rax, 1
  pop rax
  pinsrq xmm15, rax, 0
  pop rbx
  pop rbp
  pop rdi
  pop rsi
  pop r12
  pop r13
  pop r14
  pop r15
  ret
gcm128_encrypt_opt endp
ALIGN 16
gcm256_encrypt_opt proc
  push r15
  push r14
  push r13
  push r12
  push rsi
  push rdi
  push rbp
  push rbx
  pextrq rax, xmm15, 0
  push rax
  pextrq rax, xmm15, 1
  push rax
  pextrq rax, xmm14, 0
  push rax
  pextrq rax, xmm14, 1
  push rax
  pextrq rax, xmm13, 0
  push rax
  pextrq rax, xmm13, 1
  push rax
  pextrq rax, xmm12, 0
  push rax
  pextrq rax, xmm12, 1
  push rax
  pextrq rax, xmm11, 0
  push rax
  pextrq rax, xmm11, 1
  push rax
  pextrq rax, xmm10, 0
  push rax
  pextrq rax, xmm10, 1
  push rax
  pextrq rax, xmm9, 0
  push rax
  pextrq rax, xmm9, 1
  push rax
  pextrq rax, xmm8, 0
  push rax
  pextrq rax, xmm8, 1
  push rax
  pextrq rax, xmm7, 0
  push rax
  pextrq rax, xmm7, 1
  push rax
  pextrq rax, xmm6, 0
  push rax
  pextrq rax, xmm6, 1
  push rax
  mov rdi, rcx
  mov rsi, rdx
  mov rdx, r8
  mov rcx, r9
  mov r8, qword ptr [rsp + 264]
  mov r9, qword ptr [rsp + 272]
  mov rbp, qword ptr [rsp + 352]
  mov r13, r8
  mov r14, r9
  mov r12, 579005069656919567
  pinsrq xmm8, r12, 0
  mov r12, 283686952306183
  pinsrq xmm8, r12, 1
  mov rax, rdi
  mov r8, rcx
  mov r11, rdx
  movdqu xmm11, xmmword ptr [r9 + 32]
  pxor xmm1, xmm1
  mov rcx, r11
  cmp rcx, 0
  je L198
  mov rdx, 0
  mov r9, rax
  jmp L201
ALIGN 16
L200:
  movdqu xmm2, xmmword ptr [r9 + 0]
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  add rdx, 1
  add r9, 16
ALIGN 16
L201:
  cmp rdx, rcx
  jne L200
  jmp L199
L198:
L199:
  imul r11, 16
  cmp rsi, r11
  jbe L202
  mov r11, qword ptr [rsp + 280]
  movdqu xmm2, xmmword ptr [r11 + 0]
  mov rax, rsi
  and rax, 15
  cmp rax, 8
  jae L204
  mov rcx, 0
  pinsrq xmm2, rcx, 1
  mov rcx, rax
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 0
  and rcx, rdx
  pinsrq xmm2, rcx, 0
  jmp L205
L204:
  mov rcx, rax
  sub rcx, 8
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 1
  and rcx, rdx
  pinsrq xmm2, rcx, 1
L205:
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  jmp L203
L202:
L203:
  mov r15, rsi
  mov rdi, qword ptr [rsp + 288]
  mov rsi, qword ptr [rsp + 296]
  mov rdx, qword ptr [rsp + 304]
  mov rcx, r8
  mov r8, r13
  mov r9, r14
  movdqu xmm8, xmm1
  cmp rdx, 0
  jne L206
  lea r9, qword ptr [r9 + 32]
  movdqu xmm1, xmmword ptr [r8 + 0]
  mov r12, 579005069656919567
  pinsrq xmm0, r12, 0
  mov r12, 283686952306183
  pinsrq xmm0, r12, 1
  vpshufb xmm1, xmm1, xmm0
  mov rbx, 2
  pinsrd xmm1, ebx, 0
  vpshufb xmm1, xmm1, xmm0
  movdqu xmmword ptr [r8 + 0], xmm1
  jmp L207
L206:
  mov r12, 579005069656919567
  pinsrq xmm0, r12, 0
  mov r12, 283686952306183
  pinsrq xmm0, r12, 1
  movdqu xmm1, xmmword ptr [r8 + 0]
  vpshufb xmm8, xmm8, xmm0
  movdqu xmmword ptr [r8 + 0], xmm8
  add rcx, 128
  vpshufb xmm1, xmm1, xmm0
  mov rbx, 2
  pinsrd xmm1, ebx, 0
  vpshufb xmm1, xmm1, xmm0
  lea r14, qword ptr [rsi + 96]
  movdqu xmm4, xmmword ptr [rcx + -128]
  pxor xmm2, xmm2
  mov r11, 72057594037927936
  pinsrq xmm2, r11, 1
  movdqu xmm15, xmmword ptr [rcx + -112]
  mov r12, rcx
  sub r12, 96
  vpxor xmm9, xmm1, xmm4
  vpaddd xmm10, xmm1, xmm2
  vpaddd xmm11, xmm10, xmm2
  vpxor xmm10, xmm10, xmm4
  vpaddd xmm12, xmm11, xmm2
  vpxor xmm11, xmm11, xmm4
  vpaddd xmm13, xmm12, xmm2
  vpxor xmm12, xmm12, xmm4
  vpaddd xmm14, xmm13, xmm2
  vpxor xmm13, xmm13, xmm4
  vpaddd xmm1, xmm14, xmm2
  vpxor xmm14, xmm14, xmm4
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -96]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -80]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -64]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -48]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -32]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -16]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + 0]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + 16]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + 32]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + 48]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + 64]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + 80]
  movdqu xmm3, xmmword ptr [rcx + 96]
  vaesenc xmm9, xmm9, xmm15
  vpxor xmm4, xmm3, xmmword ptr [rdi + 0]
  vaesenc xmm10, xmm10, xmm15
  vpxor xmm5, xmm3, xmmword ptr [rdi + 16]
  vaesenc xmm11, xmm11, xmm15
  vpxor xmm6, xmm3, xmmword ptr [rdi + 32]
  vaesenc xmm12, xmm12, xmm15
  vpxor xmm8, xmm3, xmmword ptr [rdi + 48]
  vaesenc xmm13, xmm13, xmm15
  vpxor xmm2, xmm3, xmmword ptr [rdi + 64]
  vaesenc xmm14, xmm14, xmm15
  vpxor xmm3, xmm3, xmmword ptr [rdi + 80]
  lea rdi, qword ptr [rdi + 96]
  vaesenclast xmm9, xmm9, xmm4
  vaesenclast xmm10, xmm10, xmm5
  vaesenclast xmm11, xmm11, xmm6
  vaesenclast xmm12, xmm12, xmm8
  vaesenclast xmm13, xmm13, xmm2
  vaesenclast xmm14, xmm14, xmm3
  movdqu xmmword ptr [rsi + 0], xmm9
  movdqu xmmword ptr [rsi + 16], xmm10
  movdqu xmmword ptr [rsi + 32], xmm11
  movdqu xmmword ptr [rsi + 48], xmm12
  movdqu xmmword ptr [rsi + 64], xmm13
  movdqu xmmword ptr [rsi + 80], xmm14
  lea rsi, qword ptr [rsi + 96]
  vpshufb xmm8, xmm9, xmm0
  vpshufb xmm2, xmm10, xmm0
  movdqu xmmword ptr [rbp + 112], xmm8
  vpshufb xmm4, xmm11, xmm0
  movdqu xmmword ptr [rbp + 96], xmm2
  vpshufb xmm5, xmm12, xmm0
  movdqu xmmword ptr [rbp + 80], xmm4
  vpshufb xmm6, xmm13, xmm0
  movdqu xmmword ptr [rbp + 64], xmm5
  vpshufb xmm7, xmm14, xmm0
  movdqu xmmword ptr [rbp + 48], xmm6
  movdqu xmm4, xmmword ptr [rcx + -128]
  pxor xmm2, xmm2
  mov r11, 72057594037927936
  pinsrq xmm2, r11, 1
  movdqu xmm15, xmmword ptr [rcx + -112]
  mov r12, rcx
  sub r12, 96
  vpxor xmm9, xmm1, xmm4
  vpaddd xmm10, xmm1, xmm2
  vpaddd xmm11, xmm10, xmm2
  vpxor xmm10, xmm10, xmm4
  vpaddd xmm12, xmm11, xmm2
  vpxor xmm11, xmm11, xmm4
  vpaddd xmm13, xmm12, xmm2
  vpxor xmm12, xmm12, xmm4
  vpaddd xmm14, xmm13, xmm2
  vpxor xmm13, xmm13, xmm4
  vpaddd xmm1, xmm14, xmm2
  vpxor xmm14, xmm14, xmm4
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -96]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -80]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -64]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -48]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -32]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -16]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + 0]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + 16]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + 32]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + 48]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + 64]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + 80]
  movdqu xmm3, xmmword ptr [rcx + 96]
  vaesenc xmm9, xmm9, xmm15
  vpxor xmm4, xmm3, xmmword ptr [rdi + 0]
  vaesenc xmm10, xmm10, xmm15
  vpxor xmm5, xmm3, xmmword ptr [rdi + 16]
  vaesenc xmm11, xmm11, xmm15
  vpxor xmm6, xmm3, xmmword ptr [rdi + 32]
  vaesenc xmm12, xmm12, xmm15
  vpxor xmm8, xmm3, xmmword ptr [rdi + 48]
  vaesenc xmm13, xmm13, xmm15
  vpxor xmm2, xmm3, xmmword ptr [rdi + 64]
  vaesenc xmm14, xmm14, xmm15
  vpxor xmm3, xmm3, xmmword ptr [rdi + 80]
  lea rdi, qword ptr [rdi + 96]
  vaesenclast xmm9, xmm9, xmm4
  vaesenclast xmm10, xmm10, xmm5
  vaesenclast xmm11, xmm11, xmm6
  vaesenclast xmm12, xmm12, xmm8
  vaesenclast xmm13, xmm13, xmm2
  vaesenclast xmm14, xmm14, xmm3
  movdqu xmmword ptr [rsi + 0], xmm9
  movdqu xmmword ptr [rsi + 16], xmm10
  movdqu xmmword ptr [rsi + 32], xmm11
  movdqu xmmword ptr [rsi + 48], xmm12
  movdqu xmmword ptr [rsi + 64], xmm13
  movdqu xmmword ptr [rsi + 80], xmm14
  lea rsi, qword ptr [rsi + 96]
  sub rdx, 12
  movdqu xmm8, xmmword ptr [r8 + 0]
  lea r9, qword ptr [r9 + 32]
  pxor xmm2, xmm2
  mov r11, 72057594037927936
  pinsrq xmm2, r11, 1
  vpxor xmm4, xmm4, xmm4
  movdqu xmm15, xmmword ptr [rcx + -128]
  vpaddd xmm10, xmm1, xmm2
  vpaddd xmm11, xmm10, xmm2
  vpaddd xmm12, xmm11, xmm2
  vpaddd xmm13, xmm12, xmm2
  vpaddd xmm14, xmm13, xmm2
  vpxor xmm9, xmm1, xmm15
  movdqu xmmword ptr [rbp + 16], xmm4
  mov rbx, 14
  jmp L209
ALIGN 16
L208:
  add rbx, 6
  cmp rbx, 256
  jb L210
  mov r11, 579005069656919567
  pinsrq xmm0, r11, 0
  mov r11, 283686952306183
  pinsrq xmm0, r11, 1
  vpshufb xmm6, xmm1, xmm0
  pxor xmm5, xmm5
  mov r11, 1
  pinsrq xmm5, r11, 0
  vpaddd xmm10, xmm6, xmm5
  pxor xmm5, xmm5
  mov r11, 2
  pinsrq xmm5, r11, 0
  vpaddd xmm11, xmm6, xmm5
  movdqu xmm3, xmmword ptr [r9 + -32]
  vpaddd xmm12, xmm10, xmm5
  vpshufb xmm10, xmm10, xmm0
  vpaddd xmm13, xmm11, xmm5
  vpshufb xmm11, xmm11, xmm0
  vpxor xmm10, xmm10, xmm15
  vpaddd xmm14, xmm12, xmm5
  vpshufb xmm12, xmm12, xmm0
  vpxor xmm11, xmm11, xmm15
  vpaddd xmm1, xmm13, xmm5
  vpshufb xmm13, xmm13, xmm0
  vpshufb xmm14, xmm14, xmm0
  vpshufb xmm1, xmm1, xmm0
  sub rbx, 256
  jmp L211
L210:
  movdqu xmm3, xmmword ptr [r9 + -32]
  vpaddd xmm1, xmm2, xmm14
  vpxor xmm10, xmm10, xmm15
  vpxor xmm11, xmm11, xmm15
L211:
  movdqu xmmword ptr [r8 + 0], xmm1
  vpclmulqdq xmm5, xmm7, xmm3, 16
  vpxor xmm12, xmm12, xmm15
  movdqu xmm2, xmmword ptr [rcx + -112]
  vpclmulqdq xmm6, xmm7, xmm3, 1
  vaesenc xmm9, xmm9, xmm2
  movdqu xmm0, xmmword ptr [rbp + 48]
  vpxor xmm13, xmm13, xmm15
  vpclmulqdq xmm1, xmm7, xmm3, 0
  vaesenc xmm10, xmm10, xmm2
  vpxor xmm14, xmm14, xmm15
  vpclmulqdq xmm7, xmm7, xmm3, 17
  vaesenc xmm11, xmm11, xmm2
  movdqu xmm3, xmmword ptr [r9 + -16]
  vaesenc xmm12, xmm12, xmm2
  vpxor xmm6, xmm6, xmm5
  vpclmulqdq xmm5, xmm0, xmm3, 0
  vpxor xmm8, xmm8, xmm4
  vaesenc xmm13, xmm13, xmm2
  vpxor xmm4, xmm1, xmm5
  vpclmulqdq xmm1, xmm0, xmm3, 16
  vaesenc xmm14, xmm14, xmm2
  movdqu xmm15, xmmword ptr [rcx + -96]
  vpclmulqdq xmm2, xmm0, xmm3, 1
  vaesenc xmm9, xmm9, xmm15
  vpxor xmm8, xmm8, xmmword ptr [rbp + 16]
  vpclmulqdq xmm3, xmm0, xmm3, 17
  movdqu xmm0, xmmword ptr [rbp + 64]
  vaesenc xmm10, xmm10, xmm15
  movbe r13, qword ptr [r14 + 88]
  vaesenc xmm11, xmm11, xmm15
  movbe r12, qword ptr [r14 + 80]
  vaesenc xmm12, xmm12, xmm15
  mov qword ptr [rbp + 32], r13
  vaesenc xmm13, xmm13, xmm15
  mov qword ptr [rbp + 40], r12
  movdqu xmm5, xmmword ptr [r9 + 16]
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -80]
  vpxor xmm6, xmm6, xmm1
  vpclmulqdq xmm1, xmm0, xmm5, 0
  vaesenc xmm9, xmm9, xmm15
  vpxor xmm6, xmm6, xmm2
  vpclmulqdq xmm2, xmm0, xmm5, 16
  vaesenc xmm10, xmm10, xmm15
  vpxor xmm7, xmm7, xmm3
  vpclmulqdq xmm3, xmm0, xmm5, 1
  vaesenc xmm11, xmm11, xmm15
  vpclmulqdq xmm5, xmm0, xmm5, 17
  movdqu xmm0, xmmword ptr [rbp + 80]
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vpxor xmm4, xmm4, xmm1
  movdqu xmm1, xmmword ptr [r9 + 32]
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -64]
  vpxor xmm6, xmm6, xmm2
  vpclmulqdq xmm2, xmm0, xmm1, 0
  vaesenc xmm9, xmm9, xmm15
  vpxor xmm6, xmm6, xmm3
  vpclmulqdq xmm3, xmm0, xmm1, 16
  vaesenc xmm10, xmm10, xmm15
  movbe r13, qword ptr [r14 + 72]
  vpxor xmm7, xmm7, xmm5
  vpclmulqdq xmm5, xmm0, xmm1, 1
  vaesenc xmm11, xmm11, xmm15
  movbe r12, qword ptr [r14 + 64]
  vpclmulqdq xmm1, xmm0, xmm1, 17
  movdqu xmm0, xmmword ptr [rbp + 96]
  vaesenc xmm12, xmm12, xmm15
  mov qword ptr [rbp + 48], r13
  vaesenc xmm13, xmm13, xmm15
  mov qword ptr [rbp + 56], r12
  vpxor xmm4, xmm4, xmm2
  movdqu xmm2, xmmword ptr [r9 + 64]
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -48]
  vpxor xmm6, xmm6, xmm3
  vpclmulqdq xmm3, xmm0, xmm2, 0
  vaesenc xmm9, xmm9, xmm15
  vpxor xmm6, xmm6, xmm5
  vpclmulqdq xmm5, xmm0, xmm2, 16
  vaesenc xmm10, xmm10, xmm15
  movbe r13, qword ptr [r14 + 56]
  vpxor xmm7, xmm7, xmm1
  vpclmulqdq xmm1, xmm0, xmm2, 1
  vpxor xmm8, xmm8, xmmword ptr [rbp + 112]
  vaesenc xmm11, xmm11, xmm15
  movbe r12, qword ptr [r14 + 48]
  vpclmulqdq xmm2, xmm0, xmm2, 17
  vaesenc xmm12, xmm12, xmm15
  mov qword ptr [rbp + 64], r13
  vaesenc xmm13, xmm13, xmm15
  mov qword ptr [rbp + 72], r12
  vpxor xmm4, xmm4, xmm3
  movdqu xmm3, xmmword ptr [r9 + 80]
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm15, xmmword ptr [rcx + -32]
  vpxor xmm6, xmm6, xmm5
  vpclmulqdq xmm5, xmm8, xmm3, 16
  vaesenc xmm9, xmm9, xmm15
  vpxor xmm6, xmm6, xmm1
  vpclmulqdq xmm1, xmm8, xmm3, 1
  vaesenc xmm10, xmm10, xmm15
  movbe r13, qword ptr [r14 + 40]
  vpxor xmm7, xmm7, xmm2
  vpclmulqdq xmm2, xmm8, xmm3, 0
  vaesenc xmm11, xmm11, xmm15
  movbe r12, qword ptr [r14 + 32]
  vpclmulqdq xmm8, xmm8, xmm3, 17
  vaesenc xmm12, xmm12, xmm15
  mov qword ptr [rbp + 80], r13
  vaesenc xmm13, xmm13, xmm15
  mov qword ptr [rbp + 88], r12
  vpxor xmm6, xmm6, xmm5
  vaesenc xmm14, xmm14, xmm15
  vpxor xmm6, xmm6, xmm1
  movdqu xmm15, xmmword ptr [rcx + -16]
  vpslldq xmm5, xmm6, 8
  vpxor xmm4, xmm4, xmm2
  pxor xmm3, xmm3
  mov r11, 13979173243358019584
  pinsrq xmm3, r11, 1
  vaesenc xmm9, xmm9, xmm15
  vpxor xmm7, xmm7, xmm8
  vaesenc xmm10, xmm10, xmm15
  vpxor xmm4, xmm4, xmm5
  movbe r13, qword ptr [r14 + 24]
  vaesenc xmm11, xmm11, xmm15
  movbe r12, qword ptr [r14 + 16]
  vpalignr xmm0, xmm4, xmm4, 8
  vpclmulqdq xmm4, xmm4, xmm3, 16
  mov qword ptr [rbp + 96], r13
  vaesenc xmm12, xmm12, xmm15
  mov qword ptr [rbp + 104], r12
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  movdqu xmm1, xmmword ptr [rcx + 0]
  vaesenc xmm9, xmm9, xmm1
  movdqu xmm15, xmmword ptr [rcx + 16]
  vaesenc xmm10, xmm10, xmm1
  vpsrldq xmm6, xmm6, 8
  vaesenc xmm11, xmm11, xmm1
  vpxor xmm7, xmm7, xmm6
  vaesenc xmm12, xmm12, xmm1
  vpxor xmm4, xmm4, xmm0
  movbe r13, qword ptr [r14 + 8]
  vaesenc xmm13, xmm13, xmm1
  movbe r12, qword ptr [r14 + 0]
  vaesenc xmm14, xmm14, xmm1
  movdqu xmm1, xmmword ptr [rcx + 32]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  vaesenc xmm9, xmm9, xmm1
  vaesenc xmm10, xmm10, xmm1
  vaesenc xmm11, xmm11, xmm1
  vaesenc xmm12, xmm12, xmm1
  vaesenc xmm13, xmm13, xmm1
  movdqu xmm15, xmmword ptr [rcx + 48]
  vaesenc xmm14, xmm14, xmm1
  movdqu xmm1, xmmword ptr [rcx + 64]
  vaesenc xmm9, xmm9, xmm15
  vaesenc xmm10, xmm10, xmm15
  vaesenc xmm11, xmm11, xmm15
  vaesenc xmm12, xmm12, xmm15
  vaesenc xmm13, xmm13, xmm15
  vaesenc xmm14, xmm14, xmm15
  vaesenc xmm9, xmm9, xmm1
  vaesenc xmm10, xmm10, xmm1
  vaesenc xmm11, xmm11, xmm1
  vaesenc xmm12, xmm12, xmm1
  vaesenc xmm13, xmm13, xmm1
  movdqu xmm15, xmmword ptr [rcx + 80]
  vaesenc xmm14, xmm14, xmm1
  movdqu xmm1, xmmword ptr [rcx + 96]
  vaesenc xmm9, xmm9, xmm15
  movdqu xmmword ptr [rbp + 16], xmm7
  vpalignr xmm8, xmm4, xmm4, 8
  vaesenc xmm10, xmm10, xmm15
  vpclmulqdq xmm4, xmm4, xmm3, 16
  vpxor xmm2, xmm1, xmmword ptr [rdi + 0]
  vaesenc xmm11, xmm11, xmm15
  vpxor xmm0, xmm1, xmmword ptr [rdi + 16]
  vaesenc xmm12, xmm12, xmm15
  vpxor xmm5, xmm1, xmmword ptr [rdi + 32]
  vaesenc xmm13, xmm13, xmm15
  vpxor xmm6, xmm1, xmmword ptr [rdi + 48]
  vaesenc xmm14, xmm14, xmm15
  vpxor xmm7, xmm1, xmmword ptr [rdi + 64]
  vpxor xmm3, xmm1, xmmword ptr [rdi + 80]
  movdqu xmm1, xmmword ptr [r8 + 0]
  vaesenclast xmm9, xmm9, xmm2
  pxor xmm2, xmm2
  mov r11, 72057594037927936
  pinsrq xmm2, r11, 1
  vaesenclast xmm10, xmm10, xmm0
  vpaddd xmm0, xmm1, xmm2
  mov qword ptr [rbp + 112], r13
  lea rdi, qword ptr [rdi + 96]
  vaesenclast xmm11, xmm11, xmm5
  vpaddd xmm5, xmm0, xmm2
  mov qword ptr [rbp + 120], r12
  lea rsi, qword ptr [rsi + 96]
  movdqu xmm15, xmmword ptr [rcx + -128]
  vaesenclast xmm12, xmm12, xmm6
  vpaddd xmm6, xmm5, xmm2
  vaesenclast xmm13, xmm13, xmm7
  vpaddd xmm7, xmm6, xmm2
  vaesenclast xmm14, xmm14, xmm3
  vpaddd xmm3, xmm7, xmm2
  sub rdx, 6
  add r14, 96
  cmp rdx, 0
  jbe L212
  movdqu xmmword ptr [rsi + -96], xmm9
  vpxor xmm9, xmm1, xmm15
  movdqu xmmword ptr [rsi + -80], xmm10
  movdqu xmm10, xmm0
  movdqu xmmword ptr [rsi + -64], xmm11
  movdqu xmm11, xmm5
  movdqu xmmword ptr [rsi + -48], xmm12
  movdqu xmm12, xmm6
  movdqu xmmword ptr [rsi + -32], xmm13
  movdqu xmm13, xmm7
  movdqu xmmword ptr [rsi + -16], xmm14
  movdqu xmm14, xmm3
  movdqu xmm7, xmmword ptr [rbp + 32]
  jmp L213
L212:
  vpxor xmm8, xmm8, xmmword ptr [rbp + 16]
  vpxor xmm8, xmm8, xmm4
L213:
ALIGN 16
L209:
  cmp rdx, 0
  ja L208
  movdqu xmmword ptr [r8 + 0], xmm1
  movdqu xmm7, xmmword ptr [rbp + 32]
  pxor xmm4, xmm4
  movdqu xmmword ptr [rbp + 0], xmm4
  movdqu xmm3, xmmword ptr [r9 + -32]
  vpclmulqdq xmm1, xmm7, xmm3, 0
  vpclmulqdq xmm5, xmm7, xmm3, 16
  movdqu xmm0, xmmword ptr [rbp + 48]
  vpclmulqdq xmm6, xmm7, xmm3, 1
  vpclmulqdq xmm7, xmm7, xmm3, 17
  movdqu xmm3, xmmword ptr [r9 + -16]
  vpxor xmm6, xmm6, xmm5
  vpclmulqdq xmm5, xmm0, xmm3, 0
  vpxor xmm8, xmm8, xmm4
  vpxor xmm4, xmm1, xmm5
  vpclmulqdq xmm1, xmm0, xmm3, 16
  vpclmulqdq xmm2, xmm0, xmm3, 1
  vpxor xmm8, xmm8, xmmword ptr [rbp + 0]
  vpclmulqdq xmm3, xmm0, xmm3, 17
  movdqu xmm0, xmmword ptr [rbp + 64]
  movdqu xmm5, xmmword ptr [r9 + 16]
  vpxor xmm6, xmm6, xmm1
  vpclmulqdq xmm1, xmm0, xmm5, 0
  vpxor xmm6, xmm6, xmm2
  vpclmulqdq xmm2, xmm0, xmm5, 16
  vpxor xmm7, xmm7, xmm3
  vpclmulqdq xmm3, xmm0, xmm5, 1
  vpclmulqdq xmm5, xmm0, xmm5, 17
  movdqu xmm0, xmmword ptr [rbp + 80]
  vpxor xmm4, xmm4, xmm1
  movdqu xmm1, xmmword ptr [r9 + 32]
  vpxor xmm6, xmm6, xmm2
  vpclmulqdq xmm2, xmm0, xmm1, 0
  vpxor xmm6, xmm6, xmm3
  vpclmulqdq xmm3, xmm0, xmm1, 16
  vpxor xmm7, xmm7, xmm5
  vpclmulqdq xmm5, xmm0, xmm1, 1
  vpclmulqdq xmm1, xmm0, xmm1, 17
  movdqu xmm0, xmmword ptr [rbp + 96]
  vpxor xmm4, xmm4, xmm2
  movdqu xmm2, xmmword ptr [r9 + 64]
  vpxor xmm6, xmm6, xmm3
  vpclmulqdq xmm3, xmm0, xmm2, 0
  vpxor xmm6, xmm6, xmm5
  vpclmulqdq xmm5, xmm0, xmm2, 16
  vpxor xmm7, xmm7, xmm1
  vpclmulqdq xmm1, xmm0, xmm2, 1
  vpxor xmm8, xmm8, xmmword ptr [rbp + 112]
  vpclmulqdq xmm2, xmm0, xmm2, 17
  vpxor xmm4, xmm4, xmm3
  movdqu xmm3, xmmword ptr [r9 + 80]
  vpxor xmm6, xmm6, xmm5
  vpclmulqdq xmm5, xmm8, xmm3, 16
  vpxor xmm6, xmm6, xmm1
  vpclmulqdq xmm1, xmm8, xmm3, 1
  vpxor xmm7, xmm7, xmm2
  vpclmulqdq xmm2, xmm8, xmm3, 0
  vpclmulqdq xmm8, xmm8, xmm3, 17
  vpxor xmm6, xmm6, xmm5
  vpxor xmm6, xmm6, xmm1
  vpxor xmm4, xmm4, xmm2
  pxor xmm3, xmm3
  mov rax, 3254779904
  pinsrd xmm3, eax, 3
  vpxor xmm7, xmm7, xmm8
  vpslldq xmm5, xmm6, 8
  vpxor xmm4, xmm4, xmm5
  vpalignr xmm0, xmm4, xmm4, 8
  vpclmulqdq xmm4, xmm4, xmm3, 16
  vpsrldq xmm6, xmm6, 8
  vpxor xmm7, xmm7, xmm6
  vpxor xmm4, xmm0, xmm4
  vpalignr xmm8, xmm4, xmm4, 8
  vpclmulqdq xmm4, xmm4, xmm3, 16
  vpxor xmm8, xmm8, xmm7
  vpxor xmm8, xmm8, xmm4
  mov r12, 579005069656919567
  pinsrq xmm0, r12, 0
  mov r12, 283686952306183
  pinsrq xmm0, r12, 1
  movdqu xmmword ptr [rsi + -96], xmm9
  vpshufb xmm9, xmm9, xmm0
  vpxor xmm1, xmm1, xmm7
  movdqu xmmword ptr [rsi + -80], xmm10
  vpshufb xmm10, xmm10, xmm0
  movdqu xmmword ptr [rsi + -64], xmm11
  vpshufb xmm11, xmm11, xmm0
  movdqu xmmword ptr [rsi + -48], xmm12
  vpshufb xmm12, xmm12, xmm0
  movdqu xmmword ptr [rsi + -32], xmm13
  vpshufb xmm13, xmm13, xmm0
  movdqu xmmword ptr [rsi + -16], xmm14
  vpshufb xmm14, xmm14, xmm0
  pxor xmm4, xmm4
  movdqu xmm7, xmm14
  movdqu xmmword ptr [rbp + 0], xmm4
  movdqu xmmword ptr [rbp + 48], xmm13
  movdqu xmmword ptr [rbp + 64], xmm12
  movdqu xmmword ptr [rbp + 80], xmm11
  movdqu xmmword ptr [rbp + 96], xmm10
  movdqu xmmword ptr [rbp + 112], xmm9
  movdqu xmm3, xmmword ptr [r9 + -32]
  vpclmulqdq xmm1, xmm7, xmm3, 0
  vpclmulqdq xmm5, xmm7, xmm3, 16
  movdqu xmm0, xmmword ptr [rbp + 48]
  vpclmulqdq xmm6, xmm7, xmm3, 1
  vpclmulqdq xmm7, xmm7, xmm3, 17
  movdqu xmm3, xmmword ptr [r9 + -16]
  vpxor xmm6, xmm6, xmm5
  vpclmulqdq xmm5, xmm0, xmm3, 0
  vpxor xmm8, xmm8, xmm4
  vpxor xmm4, xmm1, xmm5
  vpclmulqdq xmm1, xmm0, xmm3, 16
  vpclmulqdq xmm2, xmm0, xmm3, 1
  vpxor xmm8, xmm8, xmmword ptr [rbp + 0]
  vpclmulqdq xmm3, xmm0, xmm3, 17
  movdqu xmm0, xmmword ptr [rbp + 64]
  movdqu xmm5, xmmword ptr [r9 + 16]
  vpxor xmm6, xmm6, xmm1
  vpclmulqdq xmm1, xmm0, xmm5, 0
  vpxor xmm6, xmm6, xmm2
  vpclmulqdq xmm2, xmm0, xmm5, 16
  vpxor xmm7, xmm7, xmm3
  vpclmulqdq xmm3, xmm0, xmm5, 1
  vpclmulqdq xmm5, xmm0, xmm5, 17
  movdqu xmm0, xmmword ptr [rbp + 80]
  vpxor xmm4, xmm4, xmm1
  movdqu xmm1, xmmword ptr [r9 + 32]
  vpxor xmm6, xmm6, xmm2
  vpclmulqdq xmm2, xmm0, xmm1, 0
  vpxor xmm6, xmm6, xmm3
  vpclmulqdq xmm3, xmm0, xmm1, 16
  vpxor xmm7, xmm7, xmm5
  vpclmulqdq xmm5, xmm0, xmm1, 1
  vpclmulqdq xmm1, xmm0, xmm1, 17
  movdqu xmm0, xmmword ptr [rbp + 96]
  vpxor xmm4, xmm4, xmm2
  movdqu xmm2, xmmword ptr [r9 + 64]
  vpxor xmm6, xmm6, xmm3
  vpclmulqdq xmm3, xmm0, xmm2, 0
  vpxor xmm6, xmm6, xmm5
  vpclmulqdq xmm5, xmm0, xmm2, 16
  vpxor xmm7, xmm7, xmm1
  vpclmulqdq xmm1, xmm0, xmm2, 1
  vpxor xmm8, xmm8, xmmword ptr [rbp + 112]
  vpclmulqdq xmm2, xmm0, xmm2, 17
  vpxor xmm4, xmm4, xmm3
  movdqu xmm3, xmmword ptr [r9 + 80]
  vpxor xmm6, xmm6, xmm5
  vpclmulqdq xmm5, xmm8, xmm3, 16
  vpxor xmm6, xmm6, xmm1
  vpclmulqdq xmm1, xmm8, xmm3, 1
  vpxor xmm7, xmm7, xmm2
  vpclmulqdq xmm2, xmm8, xmm3, 0
  vpclmulqdq xmm8, xmm8, xmm3, 17
  vpxor xmm6, xmm6, xmm5
  vpxor xmm6, xmm6, xmm1
  vpxor xmm4, xmm4, xmm2
  pxor xmm3, xmm3
  mov rax, 3254779904
  pinsrd xmm3, eax, 3
  vpxor xmm7, xmm7, xmm8
  vpslldq xmm5, xmm6, 8
  vpxor xmm4, xmm4, xmm5
  vpalignr xmm0, xmm4, xmm4, 8
  vpclmulqdq xmm4, xmm4, xmm3, 16
  vpsrldq xmm6, xmm6, 8
  vpxor xmm7, xmm7, xmm6
  vpxor xmm4, xmm0, xmm4
  vpalignr xmm8, xmm4, xmm4, 8
  vpclmulqdq xmm4, xmm4, xmm3, 16
  vpxor xmm8, xmm8, xmm7
  vpxor xmm8, xmm8, xmm4
  mov r12, 579005069656919567
  pinsrq xmm0, r12, 0
  mov r12, 283686952306183
  pinsrq xmm0, r12, 1
  vpshufb xmm8, xmm8, xmm0
  sub rcx, 128
L207:
  movdqu xmm7, xmmword ptr [r8 + 0]
  mov r8, rcx
  mov rax, qword ptr [rsp + 312]
  mov rbx, qword ptr [rsp + 320]
  mov rcx, qword ptr [rsp + 328]
  movdqu xmm1, xmm8
  mov r12, 579005069656919567
  pinsrq xmm8, r12, 0
  mov r12, 283686952306183
  pinsrq xmm8, r12, 1
  pshufb xmm7, xmm8
  movdqu xmm11, xmmword ptr [r9 + 0]
  mov rdx, 0
  mov r9, rax
  mov r10, rbx
  pxor xmm10, xmm10
  mov r12, 1
  pinsrd xmm10, r12d, 0
  jmp L215
ALIGN 16
L214:
  movdqu xmm0, xmm7
  pshufb xmm0, xmm8
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 176]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 192]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 208]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 224]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  movdqu xmm2, xmmword ptr [r9 + 0]
  pxor xmm2, xmm0
  movdqu xmmword ptr [r10 + 0], xmm2
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  add rdx, 1
  add r9, 16
  add r10, 16
  paddd xmm7, xmm10
ALIGN 16
L215:
  cmp rdx, rcx
  jne L214
  add rcx, qword ptr [rsp + 304]
  imul rcx, 16
  mov r13, qword ptr [rsp + 344]
  cmp r13, rcx
  jbe L216
  mov rax, qword ptr [rsp + 336]
  mov rbx, rax
  mov rcx, r13
  and rcx, 15
  movdqu xmm0, xmm7
  pshufb xmm0, xmm8
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 176]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 192]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 208]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 224]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  movdqu xmm2, xmmword ptr [rax + 0]
  pxor xmm2, xmm0
  movdqu xmmword ptr [rbx + 0], xmm2
  mov rax, rcx
  cmp rax, 8
  jae L218
  mov rcx, 0
  pinsrq xmm2, rcx, 1
  mov rcx, rax
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 0
  and rcx, rdx
  pinsrq xmm2, rcx, 0
  jmp L219
L218:
  mov rcx, rax
  sub rcx, 8
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  sub rdx, 1
  pextrq rcx, xmm2, 1
  and rcx, rdx
  pinsrq xmm2, rcx, 1
L219:
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  jmp L217
L216:
L217:
  mov r11, r15
  pxor xmm2, xmm2
  mov rax, r13
  imul rax, 8
  pinsrd xmm2, eax, 0
  mov rax, r11
  imul rax, 8
  pinsrd xmm2, eax, 2
  pshufb xmm2, xmm8
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm6, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  movdqu xmm5, xmm1
  pclmulqdq xmm1, xmm2, 16
  movdqu xmm3, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 1
  movdqu xmm4, xmm1
  movdqu xmm1, xmm5
  pclmulqdq xmm1, xmm2, 0
  pclmulqdq xmm5, xmm2, 17
  movdqu xmm2, xmm5
  movdqu xmm5, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm4
  mov r12, 0
  pinsrd xmm1, r12d, 0
  pshufd xmm1, xmm1, 14
  pxor xmm2, xmm1
  movdqu xmm1, xmm3
  mov r12, 0
  pinsrd xmm1, r12d, 3
  pshufd xmm1, xmm1, 79
  mov r12, 0
  pinsrd xmm4, r12d, 3
  pshufd xmm4, xmm4, 79
  pxor xmm1, xmm4
  pxor xmm1, xmm5
  movdqu xmm3, xmm1
  psrld xmm3, 31
  movdqu xmm4, xmm2
  psrld xmm4, 31
  pslld xmm1, 1
  pslld xmm2, 1
  vpslldq xmm5, xmm3, 4
  vpslldq xmm4, xmm4, 4
  mov r12, 0
  pinsrd xmm3, r12d, 0
  pshufd xmm3, xmm3, 3
  pxor xmm3, xmm4
  pxor xmm1, xmm5
  pxor xmm2, xmm3
  movdqu xmm5, xmm2
  pxor xmm2, xmm2
  mov r12, 3774873600
  pinsrd xmm2, r12d, 3
  pclmulqdq xmm1, xmm2, 17
  movdqu xmm2, xmm1
  psrld xmm2, 31
  pslld xmm1, 1
  vpslldq xmm2, xmm2, 4
  pxor xmm1, xmm2
  pxor xmm1, xmm5
  pxor xmm1, xmm6
  pshufb xmm1, xmm8
  mov r12, 1
  pinsrd xmm7, r12d, 0
  movdqu xmm0, xmm7
  mov r12, 579005069656919567
  pinsrq xmm2, r12, 0
  mov r12, 283686952306183
  pinsrq xmm2, r12, 1
  pshufb xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 160]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 176]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 192]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 208]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [r8 + 224]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  pxor xmm1, xmm0
  mov r15, qword ptr [rsp + 360]
  movdqu xmmword ptr [r15 + 0], xmm1
  pop rax
  pinsrq xmm6, rax, 1
  pop rax
  pinsrq xmm6, rax, 0
  pop rax
  pinsrq xmm7, rax, 1
  pop rax
  pinsrq xmm7, rax, 0
  pop rax
  pinsrq xmm8, rax, 1
  pop rax
  pinsrq xmm8, rax, 0
  pop rax
  pinsrq xmm9, rax, 1
  pop rax
  pinsrq xmm9, rax, 0
  pop rax
  pinsrq xmm10, rax, 1
  pop rax
  pinsrq xmm10, rax, 0
  pop rax
  pinsrq xmm11, rax, 1
  pop rax
  pinsrq xmm11, rax, 0
  pop rax
  pinsrq xmm12, rax, 1
  pop rax
  pinsrq xmm12, rax, 0
  pop rax
  pinsrq xmm13, rax, 1
  pop rax
  pinsrq xmm13, rax, 0
  pop rax
  pinsrq xmm14, rax, 1
  pop rax
  pinsrq xmm14, rax, 0
  pop rax
  pinsrq xmm15, rax, 1
  pop rax
  pinsrq xmm15, rax, 0
  pop rbx
  pop rbp
  pop rdi
  pop rsi
  pop r12
  pop r13
  pop r14
  pop r15
  ret
gcm256_encrypt_opt endp
end
