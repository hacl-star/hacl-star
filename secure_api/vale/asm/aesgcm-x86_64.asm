.code
ALIGN 16
aes_key_expansion proc
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
aes_key_expansion endp
ALIGN 16
gcm_encrypt proc
  mov r9, rcx
  pextrq rax, xmm11, 0
  push rax
  pextrq rax, xmm11, 1
  push rax
  pextrq rax, xmm10, 0
  push rax
  pextrq rax, xmm10, 1
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
  push r15
  push r14
  push r13
  push r12
  push rsi
  push rdi
  push rbp
  push rbx
  mov r14, qword ptr [r9 + 0]
  mov r13, qword ptr [r9 + 8]
  mov rax, qword ptr [r9 + 16]
  mov r11, qword ptr [r9 + 24]
  mov r10, qword ptr [r9 + 32]
  mov r8, qword ptr [r9 + 40]
  mov rbx, qword ptr [r9 + 48]
  mov r15, qword ptr [r9 + 56]
  movdqu xmm7, xmmword ptr [r10 + 0]
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
  movdqu xmm11, xmm0
  mov r12, 579005069656919567
  pinsrq xmm8, r12, 0
  mov r12, 283686952306183
  pinsrq xmm8, r12, 1
  pshufb xmm7, xmm8
  mov r12, 2
  pinsrd xmm7, r12d, 0
  mov rcx, r11
  pxor xmm1, xmm1
  cmp rcx, 0
  je L0
  mov rdx, 0
  mov r9, rax
  jmp L3
ALIGN 16
L2:
  movdqu xmm2, xmmword ptr [r9 + 0]
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  pshufb xmm2, xmm8
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
L3:
  cmp rdx, rcx
  jne L2
  jmp L1
L0:
L1:
  mov rax, r14
  mov rcx, r13
  mov rdx, 0
  mov r9, rax
  mov r10, rbx
  pxor xmm10, xmm10
  mov r12, 1
  pinsrd xmm10, r12d, 0
  jmp L5
ALIGN 16
L4:
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
  pshufb xmm2, xmm8
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
L5:
  cmp rdx, rcx
  jne L4
  pxor xmm2, xmm2
  mov rax, r13
  imul rax, 128
  pinsrd xmm2, eax, 0
  mov rax, r11
  imul rax, 128
  pinsrd xmm2, eax, 2
  pshufb xmm2, xmm8
  pxor xmm1, xmm2
  movdqu xmm2, xmm11
  pshufb xmm1, xmm8
  pshufb xmm2, xmm8
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
  pop rbx
  pop rbp
  pop rdi
  pop rsi
  pop r12
  pop r13
  pop r14
  pop r15
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
  pinsrq xmm10, rax, 1
  pop rax
  pinsrq xmm10, rax, 0
  pop rax
  pinsrq xmm11, rax, 1
  pop rax
  pinsrq xmm11, rax, 0
  ret
gcm_encrypt endp
end
