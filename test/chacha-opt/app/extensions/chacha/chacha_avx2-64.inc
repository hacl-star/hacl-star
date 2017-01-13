SECTION_TEXT

GLOBAL_HIDDEN_FN chacha_blocks_avx2
chacha_blocks_avx2_local:
vzeroupper
pushq %rbx
pushq %rbp
pushq %r12
pushq %r13
pushq %r14
movq %rsp, %rbp
andq $~63, %rsp
subq $512, %rsp
LOAD_VAR_PIC chacha_constants, %rax
vbroadcasti128 0(%rax), %ymm8
vbroadcasti128 16(%rax), %ymm6
vbroadcasti128 32(%rax), %ymm7
vbroadcasti128 0(%rdi), %ymm9
vbroadcasti128 16(%rdi), %ymm10
vbroadcasti128 32(%rdi), %ymm11
movq 32(%rdi), %r14
movq 48(%rdi), %rax
vmovdqa %xmm8, 0(%rsp)
vmovdqa %xmm9, 16(%rsp)
vmovdqa %xmm10, 32(%rsp)
vmovdqa %xmm11, 48(%rsp)
movq %rax, 64(%rsp)
vmovdqa %ymm6, 448(%rsp)
vmovdqa %ymm7, 480(%rsp)
cmp $128, %rcx
jb chacha_blocks_avx2_below128_fixup
cmp $256, %rcx
jb chacha_blocks_avx2_atleast128
cmp $512, %rcx
jb chacha_blocks_avx2_atleast256
.p2align 6,,63
chacha_blocks_avx2_atleast512:
movq %r14, %rax
leaq 1(%r14), %r8
leaq 2(%r14), %r9
leaq 3(%r14), %r10
leaq 4(%r14), %rbx
leaq 5(%r14), %r11
leaq 6(%r14), %r12
leaq 7(%r14), %r13
movl %eax, 128(%rsp)
movl %r8d, 4+128(%rsp)
movl %r9d, 8+128(%rsp)
movl %r10d, 12+128(%rsp)
movl %ebx, 16+128(%rsp)
movl %r11d, 20+128(%rsp)
movl %r12d, 24+128(%rsp)
movl %r13d, 28+128(%rsp)
addq $8, %r14
shrq $32, %rax
shrq $32, %r8
shrq $32, %r9
shrq $32, %r10
shrq $32, %rbx
shrq $32, %r11
shrq $32, %r12
shrq $32, %r13
movl %eax, 160(%rsp)
movl %r8d, 4+160(%rsp)
movl %r9d, 8+160(%rsp)
movl %r10d, 12+160(%rsp)
movl %ebx, 16+160(%rsp)
movl %r11d, 20+160(%rsp)
movl %r12d, 24+160(%rsp)
movl %r13d, 28+160(%rsp)
movq 64(%rsp), %rax
vpbroadcastd 0(%rsp), %ymm0
vpbroadcastd 4+0(%rsp), %ymm1
vpbroadcastd 8+0(%rsp), %ymm2
vpbroadcastd 12+0(%rsp), %ymm3
vpbroadcastd 16(%rsp), %ymm4
vpbroadcastd 4+16(%rsp), %ymm5
vpbroadcastd 8+16(%rsp), %ymm6
vpbroadcastd 12+16(%rsp), %ymm7
vpbroadcastd 32(%rsp), %ymm8
vpbroadcastd 4+32(%rsp), %ymm9
vpbroadcastd 8+32(%rsp), %ymm10
vpbroadcastd 12+32(%rsp), %ymm11
vpbroadcastd 8+48(%rsp), %ymm14
vpbroadcastd 12+48(%rsp), %ymm15
vmovdqa 128(%rsp), %ymm12
vmovdqa 160(%rsp), %ymm13
chacha_blocks_avx2_mainloop1:
vpaddd %ymm0, %ymm4, %ymm0
vpaddd %ymm1, %ymm5, %ymm1
vpxor %ymm12, %ymm0, %ymm12
vpxor %ymm13, %ymm1, %ymm13
vpaddd %ymm2, %ymm6, %ymm2
vpaddd %ymm3, %ymm7, %ymm3
vpxor %ymm14, %ymm2, %ymm14
vpxor %ymm15, %ymm3, %ymm15
vpshufb 448(%rsp), %ymm12, %ymm12
vpshufb 448(%rsp), %ymm13, %ymm13
vpaddd %ymm8, %ymm12, %ymm8
vpaddd %ymm9, %ymm13, %ymm9
vpshufb 448(%rsp), %ymm14, %ymm14
vpshufb 448(%rsp), %ymm15, %ymm15
vpaddd %ymm10, %ymm14, %ymm10
vpaddd %ymm11, %ymm15, %ymm11
vmovdqa %ymm12, 96(%rsp)
vpxor %ymm4, %ymm8, %ymm4
vpxor %ymm5, %ymm9, %ymm5
vpslld $ 12, %ymm4, %ymm12
vpsrld $20, %ymm4, %ymm4
vpxor %ymm4, %ymm12, %ymm4
vpslld $ 12, %ymm5, %ymm12
vpsrld $20, %ymm5, %ymm5
vpxor %ymm5, %ymm12, %ymm5
vpxor %ymm6, %ymm10, %ymm6
vpxor %ymm7, %ymm11, %ymm7
vpslld $ 12, %ymm6, %ymm12
vpsrld $20, %ymm6, %ymm6
vpxor %ymm6, %ymm12, %ymm6
vpslld $ 12, %ymm7, %ymm12
vpsrld $20, %ymm7, %ymm7
vpxor %ymm7, %ymm12, %ymm7
vpaddd %ymm0, %ymm4, %ymm0
vpaddd %ymm1, %ymm5, %ymm1
vpxor 96(%rsp), %ymm0, %ymm12
vpxor %ymm13, %ymm1, %ymm13
vpaddd %ymm2, %ymm6, %ymm2
vpaddd %ymm3, %ymm7, %ymm3
vpxor %ymm14, %ymm2, %ymm14
vpxor %ymm15, %ymm3, %ymm15
vpshufb 480(%rsp), %ymm12, %ymm12
vpshufb 480(%rsp), %ymm13, %ymm13
vpaddd %ymm8, %ymm12, %ymm8
vpaddd %ymm9, %ymm13, %ymm9
vpshufb 480(%rsp), %ymm14, %ymm14
vpshufb 480(%rsp), %ymm15, %ymm15
vpaddd %ymm10, %ymm14, %ymm10
vpaddd %ymm11, %ymm15, %ymm11
vmovdqa %ymm12, 96(%rsp)
vpxor %ymm4, %ymm8, %ymm4
vpxor %ymm5, %ymm9, %ymm5
vpslld $ 7, %ymm4, %ymm12
vpsrld $25, %ymm4, %ymm4
vpxor %ymm4, %ymm12, %ymm4
vpslld $ 7, %ymm5, %ymm12
vpsrld $25, %ymm5, %ymm5
vpxor %ymm5, %ymm12, %ymm5
vpxor %ymm6, %ymm10, %ymm6
vpxor %ymm7, %ymm11, %ymm7
vpslld $ 7, %ymm6, %ymm12
vpsrld $25, %ymm6, %ymm6
vpxor %ymm6, %ymm12, %ymm6
vpslld $ 7, %ymm7, %ymm12
vpsrld $25, %ymm7, %ymm7
vpxor %ymm7, %ymm12, %ymm7
vpaddd %ymm0, %ymm5, %ymm0
vpaddd %ymm1, %ymm6, %ymm1
vpxor %ymm15, %ymm0, %ymm15
vpxor 96(%rsp), %ymm1, %ymm12
vpaddd %ymm2, %ymm7, %ymm2
vpaddd %ymm3, %ymm4, %ymm3
vpxor %ymm13, %ymm2, %ymm13
vpxor %ymm14, %ymm3, %ymm14
vpshufb 448(%rsp), %ymm15, %ymm15
vpshufb 448(%rsp), %ymm12, %ymm12
vpaddd %ymm10, %ymm15, %ymm10
vpaddd %ymm11, %ymm12, %ymm11
vpshufb 448(%rsp), %ymm13, %ymm13
vpshufb 448(%rsp), %ymm14, %ymm14
vpaddd %ymm8, %ymm13, %ymm8
vpaddd %ymm9, %ymm14, %ymm9
vmovdqa %ymm15, 96(%rsp)
vpxor %ymm5, %ymm10, %ymm5
vpxor %ymm6, %ymm11, %ymm6
vpslld $ 12, %ymm5, %ymm15
vpsrld $20, %ymm5, %ymm5
vpxor %ymm5, %ymm15, %ymm5
vpslld $ 12, %ymm6, %ymm15
vpsrld $20, %ymm6, %ymm6
vpxor %ymm6, %ymm15, %ymm6
vpxor %ymm7, %ymm8, %ymm7
vpxor %ymm4, %ymm9, %ymm4
vpslld $ 12, %ymm7, %ymm15
vpsrld $20, %ymm7, %ymm7
vpxor %ymm7, %ymm15, %ymm7
vpslld $ 12, %ymm4, %ymm15
vpsrld $20, %ymm4, %ymm4
vpxor %ymm4, %ymm15, %ymm4
vpaddd %ymm0, %ymm5, %ymm0
vpaddd %ymm1, %ymm6, %ymm1
vpxor 96(%rsp), %ymm0, %ymm15
vpxor %ymm12, %ymm1, %ymm12
vpaddd %ymm2, %ymm7, %ymm2
vpaddd %ymm3, %ymm4, %ymm3
vpxor %ymm13, %ymm2, %ymm13
vpxor %ymm14, %ymm3, %ymm14
vpshufb 480(%rsp), %ymm15, %ymm15
vpshufb 480(%rsp), %ymm12, %ymm12
vpaddd %ymm10, %ymm15, %ymm10
vpaddd %ymm11, %ymm12, %ymm11
vpshufb 480(%rsp), %ymm13, %ymm13
vpshufb 480(%rsp), %ymm14, %ymm14
vpaddd %ymm8, %ymm13, %ymm8
vpaddd %ymm9, %ymm14, %ymm9
vmovdqa %ymm15, 96(%rsp)
vpxor %ymm5, %ymm10, %ymm5
vpxor %ymm6, %ymm11, %ymm6
vpslld $ 7, %ymm5, %ymm15
vpsrld $25, %ymm5, %ymm5
vpxor %ymm5, %ymm15, %ymm5
vpslld $ 7, %ymm6, %ymm15
vpsrld $25, %ymm6, %ymm6
vpxor %ymm6, %ymm15, %ymm6
vpxor %ymm7, %ymm8, %ymm7
vpxor %ymm4, %ymm9, %ymm4
vpslld $ 7, %ymm7, %ymm15
vpsrld $25, %ymm7, %ymm7
vpxor %ymm7, %ymm15, %ymm7
vpslld $ 7, %ymm4, %ymm15
vpsrld $25, %ymm4, %ymm4
vpxor %ymm4, %ymm15, %ymm4
vmovdqa 96(%rsp), %ymm15
subq $2, %rax
jnz chacha_blocks_avx2_mainloop1
vmovdqa %ymm8, 192(%rsp)
vmovdqa %ymm9, 224(%rsp)
vmovdqa %ymm10, 256(%rsp)
vmovdqa %ymm11, 288(%rsp)
vmovdqa %ymm12, 320(%rsp)
vmovdqa %ymm13, 352(%rsp)
vmovdqa %ymm14, 384(%rsp)
vmovdqa %ymm15, 416(%rsp)
vpbroadcastd 0(%rsp), %ymm8
vpbroadcastd 4+0(%rsp), %ymm9
vpbroadcastd 8+0(%rsp), %ymm10
vpbroadcastd 12+0(%rsp), %ymm11
vpbroadcastd 16(%rsp), %ymm12
vpbroadcastd 4+16(%rsp), %ymm13
vpbroadcastd 8+16(%rsp), %ymm14
vpbroadcastd 12+16(%rsp), %ymm15
vpaddd %ymm8, %ymm0, %ymm0
vpaddd %ymm9, %ymm1, %ymm1
vpaddd %ymm10, %ymm2, %ymm2
vpaddd %ymm11, %ymm3, %ymm3
vpaddd %ymm12, %ymm4, %ymm4
vpaddd %ymm13, %ymm5, %ymm5
vpaddd %ymm14, %ymm6, %ymm6
vpaddd %ymm15, %ymm7, %ymm7
vpunpckldq %ymm1, %ymm0, %ymm8
vpunpckldq %ymm3, %ymm2, %ymm9
vpunpckhdq %ymm1, %ymm0, %ymm12
vpunpckhdq %ymm3, %ymm2, %ymm13
vpunpckldq %ymm5, %ymm4, %ymm10
vpunpckldq %ymm7, %ymm6, %ymm11
vpunpckhdq %ymm5, %ymm4, %ymm14
vpunpckhdq %ymm7, %ymm6, %ymm15
vpunpcklqdq %ymm9, %ymm8, %ymm0
vpunpcklqdq %ymm11, %ymm10, %ymm1
vpunpckhqdq %ymm9, %ymm8, %ymm2
vpunpckhqdq %ymm11, %ymm10, %ymm3
vpunpcklqdq %ymm13, %ymm12, %ymm4
vpunpcklqdq %ymm15, %ymm14, %ymm5
vpunpckhqdq %ymm13, %ymm12, %ymm6
vpunpckhqdq %ymm15, %ymm14, %ymm7
vperm2i128 $0x20, %ymm1, %ymm0, %ymm8
vperm2i128 $0x20, %ymm3, %ymm2, %ymm9
vperm2i128 $0x31, %ymm1, %ymm0, %ymm12
vperm2i128 $0x31, %ymm3, %ymm2, %ymm13
vperm2i128 $0x20, %ymm5, %ymm4, %ymm10
vperm2i128 $0x20, %ymm7, %ymm6, %ymm11
vperm2i128 $0x31, %ymm5, %ymm4, %ymm14
vperm2i128 $0x31, %ymm7, %ymm6, %ymm15
andq %rsi, %rsi
jz chacha_blocks_avx2_noinput1
vpxor 0(%rsi), %ymm8, %ymm8
vpxor 64(%rsi), %ymm9, %ymm9
vpxor 128(%rsi), %ymm10, %ymm10
vpxor 192(%rsi), %ymm11, %ymm11
vpxor 256(%rsi), %ymm12, %ymm12
vpxor 320(%rsi), %ymm13, %ymm13
vpxor 384(%rsi), %ymm14, %ymm14
vpxor 448(%rsi), %ymm15, %ymm15
vmovdqu %ymm8, 0(%rdx)
vmovdqu %ymm9, 64(%rdx)
vmovdqu %ymm10, 128(%rdx)
vmovdqu %ymm11, 192(%rdx)
vmovdqu %ymm12, 256(%rdx)
vmovdqu %ymm13, 320(%rdx)
vmovdqu %ymm14, 384(%rdx)
vmovdqu %ymm15, 448(%rdx)
vmovdqa 192(%rsp), %ymm0
vmovdqa 224(%rsp), %ymm1
vmovdqa 256(%rsp), %ymm2
vmovdqa 288(%rsp), %ymm3
vmovdqa 320(%rsp), %ymm4
vmovdqa 352(%rsp), %ymm5
vmovdqa 384(%rsp), %ymm6
vmovdqa 416(%rsp), %ymm7
vpbroadcastd 32(%rsp), %ymm8
vpbroadcastd 4+32(%rsp), %ymm9
vpbroadcastd 8+32(%rsp), %ymm10
vpbroadcastd 12+32(%rsp), %ymm11
vmovdqa 128(%rsp), %ymm12
vmovdqa 160(%rsp), %ymm13
vpbroadcastd 8+48(%rsp), %ymm14
vpbroadcastd 12+48(%rsp), %ymm15
vpaddd %ymm8, %ymm0, %ymm0
vpaddd %ymm9, %ymm1, %ymm1
vpaddd %ymm10, %ymm2, %ymm2
vpaddd %ymm11, %ymm3, %ymm3
vpaddd %ymm12, %ymm4, %ymm4
vpaddd %ymm13, %ymm5, %ymm5
vpaddd %ymm14, %ymm6, %ymm6
vpaddd %ymm15, %ymm7, %ymm7
vpunpckldq %ymm1, %ymm0, %ymm8
vpunpckldq %ymm3, %ymm2, %ymm9
vpunpckhdq %ymm1, %ymm0, %ymm12
vpunpckhdq %ymm3, %ymm2, %ymm13
vpunpckldq %ymm5, %ymm4, %ymm10
vpunpckldq %ymm7, %ymm6, %ymm11
vpunpckhdq %ymm5, %ymm4, %ymm14
vpunpckhdq %ymm7, %ymm6, %ymm15
vpunpcklqdq %ymm9, %ymm8, %ymm0
vpunpcklqdq %ymm11, %ymm10, %ymm1
vpunpckhqdq %ymm9, %ymm8, %ymm2
vpunpckhqdq %ymm11, %ymm10, %ymm3
vpunpcklqdq %ymm13, %ymm12, %ymm4
vpunpcklqdq %ymm15, %ymm14, %ymm5
vpunpckhqdq %ymm13, %ymm12, %ymm6
vpunpckhqdq %ymm15, %ymm14, %ymm7
vperm2i128 $0x20, %ymm1, %ymm0, %ymm8
vperm2i128 $0x20, %ymm3, %ymm2, %ymm9
vperm2i128 $0x31, %ymm1, %ymm0, %ymm12
vperm2i128 $0x31, %ymm3, %ymm2, %ymm13
vperm2i128 $0x20, %ymm5, %ymm4, %ymm10
vperm2i128 $0x20, %ymm7, %ymm6, %ymm11
vperm2i128 $0x31, %ymm5, %ymm4, %ymm14
vperm2i128 $0x31, %ymm7, %ymm6, %ymm15
vpxor 32(%rsi), %ymm8, %ymm8
vpxor 96(%rsi), %ymm9, %ymm9
vpxor 160(%rsi), %ymm10, %ymm10
vpxor 224(%rsi), %ymm11, %ymm11
vpxor 288(%rsi), %ymm12, %ymm12
vpxor 352(%rsi), %ymm13, %ymm13
vpxor 416(%rsi), %ymm14, %ymm14
vpxor 480(%rsi), %ymm15, %ymm15
vmovdqu %ymm8, 32(%rdx)
vmovdqu %ymm9, 96(%rdx)
vmovdqu %ymm10, 160(%rdx)
vmovdqu %ymm11, 224(%rdx)
vmovdqu %ymm12, 288(%rdx)
vmovdqu %ymm13, 352(%rdx)
vmovdqu %ymm14, 416(%rdx)
vmovdqu %ymm15, 480(%rdx)
addq $512, %rsi
jmp chacha_blocks_avx2_mainloop1_cont
chacha_blocks_avx2_noinput1:
vmovdqu %ymm8, 0(%rdx)
vmovdqu %ymm9, 64(%rdx)
vmovdqu %ymm10, 128(%rdx)
vmovdqu %ymm11, 192(%rdx)
vmovdqu %ymm12, 256(%rdx)
vmovdqu %ymm13, 320(%rdx)
vmovdqu %ymm14, 384(%rdx)
vmovdqu %ymm15, 448(%rdx)
vmovdqa 192(%rsp), %ymm0
vmovdqa 224(%rsp), %ymm1
vmovdqa 256(%rsp), %ymm2
vmovdqa 288(%rsp), %ymm3
vmovdqa 320(%rsp), %ymm4
vmovdqa 352(%rsp), %ymm5
vmovdqa 384(%rsp), %ymm6
vmovdqa 416(%rsp), %ymm7
vpbroadcastd 32(%rsp), %ymm8
vpbroadcastd 4+32(%rsp), %ymm9
vpbroadcastd 8+32(%rsp), %ymm10
vpbroadcastd 12+32(%rsp), %ymm11
vmovdqa 128(%rsp), %ymm12
vmovdqa 160(%rsp), %ymm13
vpbroadcastd 8+48(%rsp), %ymm14
vpbroadcastd 12+48(%rsp), %ymm15
vpaddd %ymm8, %ymm0, %ymm0
vpaddd %ymm9, %ymm1, %ymm1
vpaddd %ymm10, %ymm2, %ymm2
vpaddd %ymm11, %ymm3, %ymm3
vpaddd %ymm12, %ymm4, %ymm4
vpaddd %ymm13, %ymm5, %ymm5
vpaddd %ymm14, %ymm6, %ymm6
vpaddd %ymm15, %ymm7, %ymm7
vpunpckldq %ymm1, %ymm0, %ymm8
vpunpckldq %ymm3, %ymm2, %ymm9
vpunpckhdq %ymm1, %ymm0, %ymm12
vpunpckhdq %ymm3, %ymm2, %ymm13
vpunpckldq %ymm5, %ymm4, %ymm10
vpunpckldq %ymm7, %ymm6, %ymm11
vpunpckhdq %ymm5, %ymm4, %ymm14
vpunpckhdq %ymm7, %ymm6, %ymm15
vpunpcklqdq %ymm9, %ymm8, %ymm0
vpunpcklqdq %ymm11, %ymm10, %ymm1
vpunpckhqdq %ymm9, %ymm8, %ymm2
vpunpckhqdq %ymm11, %ymm10, %ymm3
vpunpcklqdq %ymm13, %ymm12, %ymm4
vpunpcklqdq %ymm15, %ymm14, %ymm5
vpunpckhqdq %ymm13, %ymm12, %ymm6
vpunpckhqdq %ymm15, %ymm14, %ymm7
vperm2i128 $0x20, %ymm1, %ymm0, %ymm8
vperm2i128 $0x20, %ymm3, %ymm2, %ymm9
vperm2i128 $0x31, %ymm1, %ymm0, %ymm12
vperm2i128 $0x31, %ymm3, %ymm2, %ymm13
vperm2i128 $0x20, %ymm5, %ymm4, %ymm10
vperm2i128 $0x20, %ymm7, %ymm6, %ymm11
vperm2i128 $0x31, %ymm5, %ymm4, %ymm14
vperm2i128 $0x31, %ymm7, %ymm6, %ymm15
vmovdqu %ymm8, 32(%rdx)
vmovdqu %ymm9, 96(%rdx)
vmovdqu %ymm10, 160(%rdx)
vmovdqu %ymm11, 224(%rdx)
vmovdqu %ymm12, 288(%rdx)
vmovdqu %ymm13, 352(%rdx)
vmovdqu %ymm14, 416(%rdx)
vmovdqu %ymm15, 480(%rdx)
chacha_blocks_avx2_mainloop1_cont:
addq $512, %rdx
subq $512, %rcx
cmp $512, %rcx
jae chacha_blocks_avx2_atleast512
movq %r14, 48(%rsp)
vbroadcasti128 0(%rsp), %ymm8
vbroadcasti128 16(%rsp), %ymm9
vbroadcasti128 32(%rsp), %ymm10
vbroadcasti128 48(%rsp), %ymm11
vbroadcasti128 448(%rsp), %ymm6
vbroadcasti128 480(%rsp), %ymm7
cmp $128, %rcx
jb chacha_blocks_avx2_below128_fixup
cmp $256, %rcx
jb chacha_blocks_avx2_atleast128
chacha_blocks_avx2_atleast256:
movq $1, %r9
movq $2, %r10
vpxor %ymm13, %ymm13, %ymm13
vmovd %r9, %xmm14
vmovd %r10, %xmm15
vinserti128 $1, %xmm14, %ymm13, %ymm4
vinserti128 $1, %xmm15, %ymm15, %ymm5
vmovdqa %ymm8, %ymm0
vmovdqa %ymm9, %ymm1
vmovdqa %ymm10, %ymm2
vpaddq %ymm4, %ymm11, %ymm3
vpaddq %ymm5, %ymm3, %ymm11
vmovdqa %ymm8, 192(%rsp)
vmovdqa %ymm9, 224(%rsp)
vmovdqa %ymm10, 256(%rsp)
vmovdqa %ymm3, 288(%rsp)
vmovdqa %ymm11, 320(%rsp)
movq 64(%rsp), %rax
chacha_blocks_avx2_mainloop2:
vpaddd %ymm0, %ymm1, %ymm0
vpaddd %ymm8, %ymm9, %ymm8
vpxor %ymm3, %ymm0, %ymm3
vpxor %ymm11, %ymm8, %ymm11
vpshufb %ymm6, %ymm3, %ymm3
vpshufb %ymm6, %ymm11, %ymm11
vpaddd %ymm2, %ymm3, %ymm2
vpaddd %ymm10, %ymm11, %ymm10
vpxor %ymm1, %ymm2, %ymm1
vpxor %ymm9, %ymm10, %ymm9
vpslld $ 12, %ymm1, %ymm4
vpsrld $20, %ymm1, %ymm1
vpxor %ymm1, %ymm4, %ymm1
vpslld $ 12, %ymm9, %ymm5
vpsrld $20, %ymm9, %ymm9
vpxor %ymm9, %ymm5, %ymm9
vpaddd %ymm0, %ymm1, %ymm0
vpaddd %ymm8, %ymm9, %ymm8
vpxor %ymm3, %ymm0, %ymm3
vpxor %ymm11, %ymm8, %ymm11
vpshufb %ymm7, %ymm3, %ymm3
vpshufb %ymm7, %ymm11, %ymm11
vpshufd $0x93, %ymm0, %ymm0
vpshufd $0x93, %ymm8, %ymm8
vpaddd %ymm2, %ymm3, %ymm2
vpaddd %ymm10, %ymm11, %ymm10
vpshufd $0x4e, %ymm3, %ymm3
vpshufd $0x4e, %ymm11, %ymm11
vpxor %ymm1, %ymm2, %ymm1
vpxor %ymm9, %ymm10, %ymm9
vpshufd $0x39, %ymm2, %ymm2
vpshufd $0x39, %ymm10, %ymm10
vpslld $ 7, %ymm1, %ymm4
vpsrld $25, %ymm1, %ymm1
vpxor %ymm1, %ymm4, %ymm1
vpslld $ 7, %ymm9, %ymm5
vpsrld $25, %ymm9, %ymm9
vpxor %ymm9, %ymm5, %ymm9
vpaddd %ymm0, %ymm1, %ymm0
vpaddd %ymm8, %ymm9, %ymm8
vpxor %ymm3, %ymm0, %ymm3
vpxor %ymm11, %ymm8, %ymm11
vpshufb %ymm6, %ymm3, %ymm3
vpshufb %ymm6, %ymm11, %ymm11
vpaddd %ymm2, %ymm3, %ymm2
vpaddd %ymm10, %ymm11, %ymm10
vpxor %ymm1, %ymm2, %ymm1
vpxor %ymm9, %ymm10, %ymm9
vpslld $ 12, %ymm1, %ymm4
vpsrld $20, %ymm1, %ymm1
vpxor %ymm1, %ymm4, %ymm1
vpslld $ 12, %ymm9, %ymm5
vpsrld $20, %ymm9, %ymm9
vpxor %ymm9, %ymm5, %ymm9
vpaddd %ymm0, %ymm1, %ymm0
vpaddd %ymm8, %ymm9, %ymm8
vpxor %ymm3, %ymm0, %ymm3
vpxor %ymm11, %ymm8, %ymm11
vpshufb %ymm7, %ymm3, %ymm3
vpshufb %ymm7, %ymm11, %ymm11
vpshufd $0x39, %ymm0, %ymm0
vpshufd $0x39, %ymm8, %ymm8
vpaddd %ymm2, %ymm3, %ymm2
vpaddd %ymm10, %ymm11, %ymm10
vpshufd $0x4e, %ymm3, %ymm3
vpshufd $0x4e, %ymm11, %ymm11
vpxor %ymm1, %ymm2, %ymm1
vpxor %ymm9, %ymm10, %ymm9
vpshufd $0x93, %ymm2, %ymm2
vpshufd $0x93, %ymm10, %ymm10
vpslld $ 7, %ymm1, %ymm4
vpsrld $25, %ymm1, %ymm1
vpxor %ymm1, %ymm4, %ymm1
vpslld $ 7, %ymm9, %ymm5
vpsrld $25, %ymm9, %ymm9
vpxor %ymm9, %ymm5, %ymm9
subq $2, %rax
jnz chacha_blocks_avx2_mainloop2
vmovdqa 192(%rsp), %ymm12
vmovdqa 224(%rsp), %ymm13
vmovdqa 256(%rsp), %ymm14
vmovdqa 288(%rsp), %ymm15
vmovdqa 320(%rsp), %ymm5
vpaddd %ymm12, %ymm0, %ymm0
vpaddd %ymm12, %ymm8, %ymm8
vpaddd %ymm13, %ymm1, %ymm1
vpaddd %ymm13, %ymm9, %ymm9
vpaddd %ymm14, %ymm2, %ymm2
vpaddd %ymm14, %ymm10, %ymm10
vpaddd %ymm15, %ymm3, %ymm3
vpaddd %ymm5, %ymm11, %ymm11
vperm2i128 $2, %ymm0, %ymm1, %ymm12
vperm2i128 $2, %ymm2, %ymm3, %ymm13
vperm2i128 $19, %ymm0, %ymm1, %ymm14
vperm2i128 $19, %ymm2, %ymm3, %ymm15
vperm2i128 $2, %ymm8, %ymm9, %ymm0
vperm2i128 $2, %ymm10, %ymm11, %ymm1
vperm2i128 $19, %ymm8, %ymm9, %ymm2
vperm2i128 $19, %ymm10, %ymm11, %ymm3
andq %rsi, %rsi
jz chacha_blocks_avx2_noinput2
vpxor 0(%rsi), %ymm12, %ymm12
vpxor 32(%rsi), %ymm13, %ymm13
vpxor 64(%rsi), %ymm14, %ymm14
vpxor 96(%rsi), %ymm15, %ymm15
vpxor 128(%rsi), %ymm0, %ymm0
vpxor 160(%rsi), %ymm1, %ymm1
vpxor 192(%rsi), %ymm2, %ymm2
vpxor 224(%rsi), %ymm3, %ymm3
addq $256, %rsi
chacha_blocks_avx2_noinput2:
addq $4, %r14
vmovdqu %ymm12, 0(%rdx)
vmovdqu %ymm13, 32(%rdx)
vmovdqu %ymm14, 64(%rdx)
vmovdqu %ymm15, 96(%rdx)
vmovdqu %ymm0, 128(%rdx)
vmovdqu %ymm1, 160(%rdx)
vmovdqu %ymm2, 192(%rdx)
vmovdqu %ymm3, 224(%rdx)
movq %r14, 48(%rsp)
addq $256, %rdx
subq $256, %rcx
vbroadcasti128 0(%rsp), %ymm8
vbroadcasti128 16(%rsp), %ymm9
vbroadcasti128 32(%rsp), %ymm10
vbroadcasti128 48(%rsp), %ymm11
cmp $128, %rcx
jb chacha_blocks_avx2_below128_fixup
chacha_blocks_avx2_atleast128:
movq $1, %r9
vpxor %ymm13, %ymm13, %ymm13
vmovd %r9, %xmm14
vinserti128 $1, %xmm14, %ymm13, %ymm13
vpaddq %ymm13, %ymm11, %ymm11
vmovdqa %ymm8, %ymm0
vmovdqa %ymm9, %ymm1
vmovdqa %ymm10, %ymm2
vmovdqa %ymm11, %ymm3
movq 64(%rsp), %rax
chacha_blocks_avx2_mainloop3:
vpaddd %ymm0, %ymm1, %ymm0
vpxor %ymm3, %ymm0, %ymm3
vpshufb %ymm6, %ymm3, %ymm3
vpaddd %ymm2, %ymm3, %ymm2
vpxor %ymm1, %ymm2, %ymm1
vpslld $ 12, %ymm1, %ymm4
vpsrld $20, %ymm1, %ymm1
vpxor %ymm1, %ymm4, %ymm1
vpaddd %ymm0, %ymm1, %ymm0
vpxor %ymm3, %ymm0, %ymm3
vpshufb %ymm7, %ymm3, %ymm3
vpshufd $0x93, %ymm0, %ymm0
vpaddd %ymm2, %ymm3, %ymm2
vpshufd $0x4e, %ymm3, %ymm3
vpxor %ymm1, %ymm2, %ymm1
vpshufd $0x39, %ymm2, %ymm2
vpslld $ 7, %ymm1, %ymm4
vpsrld $25, %ymm1, %ymm1
vpxor %ymm1, %ymm4, %ymm1
vpaddd %ymm0, %ymm1, %ymm0
vpxor %ymm3, %ymm0, %ymm3
vpshufb %ymm6, %ymm3, %ymm3
vpaddd %ymm2, %ymm3, %ymm2
vpxor %ymm1, %ymm2, %ymm1
vpslld $ 12, %ymm1, %ymm4
vpsrld $20, %ymm1, %ymm1
vpxor %ymm1, %ymm4, %ymm1
vpaddd %ymm0, %ymm1, %ymm0
vpxor %ymm3, %ymm0, %ymm3
vpshufb %ymm7, %ymm3, %ymm3
vpshufd $0x39, %ymm0, %ymm0
vpaddd %ymm2, %ymm3, %ymm2
vpshufd $0x4e, %ymm3, %ymm3
vpxor %ymm1, %ymm2, %ymm1
vpshufd $0x93, %ymm2, %ymm2
vpslld $ 7, %ymm1, %ymm4
vpsrld $25, %ymm1, %ymm1
vpxor %ymm1, %ymm4, %ymm1
subq $2, %rax
jnz chacha_blocks_avx2_mainloop3
vpaddd %ymm8, %ymm0, %ymm0
vpaddd %ymm9, %ymm1, %ymm1
vpaddd %ymm10, %ymm2, %ymm2
vpaddd %ymm11, %ymm3, %ymm3
vperm2i128 $2, %ymm0, %ymm1, %ymm12
vperm2i128 $2, %ymm2, %ymm3, %ymm13
vperm2i128 $19, %ymm0, %ymm1, %ymm14
vperm2i128 $19, %ymm2, %ymm3, %ymm15
andq %rsi, %rsi
jz chacha_blocks_avx2_noinput3
vpxor 0(%rsi), %ymm12, %ymm12
vpxor 32(%rsi), %ymm13, %ymm13
vpxor 64(%rsi), %ymm14, %ymm14
vpxor 96(%rsi), %ymm15, %ymm15
addq $128, %rsi
chacha_blocks_avx2_noinput3:
addq $2, %r14
vmovdqu %ymm12, 0(%rdx)
vmovdqu %ymm13, 32(%rdx)
vmovdqu %ymm14, 64(%rdx)
vmovdqu %ymm15, 96(%rdx)
movq $2, %r9
vmovd %r9, %xmm4
addq $128, %rdx
vpaddq %xmm4, %xmm11, %xmm11
subq $128, %rcx
movq %r14, 48(%rsp)
chacha_blocks_avx2_below128_fixup:
movq $1, %r9
vmovd %r9, %xmm5
chacha_blocks_avx2_below128:
andq %rcx, %rcx
jz chacha_blocks_avx2_done
cmpq $64, %rcx
jae chacha_blocks_avx2_above63
movq %rdx, %r9
andq %rsi, %rsi
jz chacha_blocks_avx2_noinput4
movq %rcx, %r10
movq %rsp, %rdx
addq %r10, %rsi
addq %r10, %rdx
negq %r10
chacha_blocks_avx2_copyinput:
movb (%rsi, %r10), %al
movb %al, (%rdx, %r10)
incq %r10
jnz chacha_blocks_avx2_copyinput
movq %rsp, %rsi
chacha_blocks_avx2_noinput4:
movq %rsp, %rdx
chacha_blocks_avx2_above63:
vmovdqa %xmm8, %xmm0
vmovdqa %xmm9, %xmm1
vmovdqa %xmm10, %xmm2
vmovdqa %xmm11, %xmm3
movq 64(%rsp), %rax
chacha_blocks_avx2_mainloop4:
vpaddd %xmm0, %xmm1, %xmm0
vpxor %xmm3, %xmm0, %xmm3
vpshufb %xmm6, %xmm3, %xmm3
vpaddd %xmm2, %xmm3, %xmm2
vpxor %xmm1, %xmm2, %xmm1
vpslld $12, %xmm1, %xmm4
vpsrld $20, %xmm1, %xmm1
vpxor %xmm1, %xmm4, %xmm1
vpaddd %xmm0, %xmm1, %xmm0
vpxor %xmm3, %xmm0, %xmm3
vpshufb %xmm7, %xmm3, %xmm3
vpshufd $0x93, %xmm0, %xmm0
vpaddd %xmm2, %xmm3, %xmm2
vpshufd $0x4e, %xmm3, %xmm3
vpxor %xmm1, %xmm2, %xmm1
vpshufd $0x39, %xmm2, %xmm2
vpslld $7, %xmm1, %xmm4
vpsrld $25, %xmm1, %xmm1
vpxor %xmm1, %xmm4, %xmm1
vpaddd %xmm0, %xmm1, %xmm0
vpxor %xmm3, %xmm0, %xmm3
vpshufb %xmm6, %xmm3, %xmm3
vpaddd %xmm2, %xmm3, %xmm2
vpxor %xmm1, %xmm2, %xmm1
vpslld $12, %xmm1, %xmm4
vpsrld $20, %xmm1, %xmm1
vpxor %xmm1, %xmm4, %xmm1
vpaddd %xmm0, %xmm1, %xmm0
vpxor %xmm3, %xmm0, %xmm3
vpshufb %xmm7, %xmm3, %xmm3
vpshufd $0x39, %xmm0, %xmm0
vpaddd %xmm2, %xmm3, %xmm2
vpshufd $0x4e, %xmm3, %xmm3
vpxor %xmm1, %xmm2, %xmm1
vpshufd $0x93, %xmm2, %xmm2
vpslld $7, %xmm1, %xmm4
vpsrld $25, %xmm1, %xmm1
vpxor %xmm1, %xmm4, %xmm1
subq $2, %rax
jnz chacha_blocks_avx2_mainloop4
vpaddd %xmm0, %xmm8, %xmm0
vpaddd %xmm1, %xmm9, %xmm1
vpaddd %xmm2, %xmm10, %xmm2
vpaddd %xmm3, %xmm11, %xmm3
andq %rsi, %rsi
jz chacha_blocks_avx2_noinput5
vpxor 0(%rsi), %xmm0, %xmm0
vpxor 16(%rsi), %xmm1, %xmm1
vpxor 32(%rsi), %xmm2, %xmm2
vpxor 48(%rsi), %xmm3, %xmm3
addq $64, %rsi
chacha_blocks_avx2_noinput5:
vmovdqu %xmm0, 0(%rdx)
vmovdqu %xmm1, 16(%rdx)
vmovdqu %xmm2, 32(%rdx)
vmovdqu %xmm3, 48(%rdx)
vpaddq %xmm11, %xmm5, %xmm11
addq $1, %r14
cmpq $64, %rcx
jbe chacha_blocks_avx2_mainloop4_finishup
addq $64, %rdx
subq $64, %rcx
jmp chacha_blocks_avx2_below128
chacha_blocks_avx2_mainloop4_finishup:
cmpq $64, %rcx
je chacha_blocks_avx2_done
addq %rcx, %r9
addq %rcx, %rdx
negq %rcx
chacha_blocks_avx2_copyoutput:
movb (%rdx, %rcx), %al
movb %al, (%r9, %rcx)
incq %rcx
jnz chacha_blocks_avx2_copyoutput
chacha_blocks_avx2_done:
movq %r14, 32(%rdi)
movq %rbp, %rsp
popq %r14
popq %r13
popq %r12
popq %rbp
popq %rbx
ret
FN_END chacha_blocks_avx2


GLOBAL_HIDDEN_FN hchacha_avx2
hchacha_avx2_local:
LOAD_VAR_PIC chacha_constants, %rax
vmovdqa 0(%rax), %xmm0
vmovdqa 16(%rax), %xmm6
vmovdqa 32(%rax), %xmm5
vmovdqu 0(%rdi), %xmm1
vmovdqu 16(%rdi), %xmm2
vmovdqu 0(%rsi), %xmm3
hhacha_mainloop_avx2:
vpaddd %xmm0, %xmm1, %xmm0
vpxor %xmm3, %xmm0, %xmm3
vpshufb %xmm6, %xmm3, %xmm3
vpaddd %xmm2, %xmm3, %xmm2
vpxor %xmm1, %xmm2, %xmm1
vpslld $12, %xmm1, %xmm4
vpsrld $20, %xmm1, %xmm1
vpxor %xmm1, %xmm4, %xmm1
vpaddd %xmm0, %xmm1, %xmm0
vpxor %xmm3, %xmm0, %xmm3
vpshufb %xmm5, %xmm3, %xmm3
vpaddd %xmm2, %xmm3, %xmm2
vpxor %xmm1, %xmm2, %xmm1
vpslld $7, %xmm1, %xmm4
vpsrld $25, %xmm1, %xmm1
vpshufd $0x93, %xmm0, %xmm0
vpxor %xmm1, %xmm4, %xmm1
vpshufd $0x4e, %xmm3, %xmm3
vpaddd %xmm0, %xmm1, %xmm0
vpxor %xmm3, %xmm0, %xmm3
vpshufb %xmm6, %xmm3, %xmm3
vpshufd $0x39, %xmm2, %xmm2
vpaddd %xmm2, %xmm3, %xmm2
vpxor %xmm1, %xmm2, %xmm1
vpslld $12, %xmm1, %xmm4
vpsrld $20, %xmm1, %xmm1
vpxor %xmm1, %xmm4, %xmm1
vpaddd %xmm0, %xmm1, %xmm0
vpxor %xmm3, %xmm0, %xmm3
vpshufb %xmm5, %xmm3, %xmm3
vpaddd %xmm2, %xmm3, %xmm2
vpxor %xmm1, %xmm2, %xmm1
vpshufd $0x39, %xmm0, %xmm0
vpslld $7, %xmm1, %xmm4
vpshufd $0x4e, %xmm3, %xmm3
vpsrld $25, %xmm1, %xmm1
vpshufd $0x93, %xmm2, %xmm2
vpxor %xmm1, %xmm4, %xmm1
subl $2, %ecx
jne hhacha_mainloop_avx2
vmovdqu %xmm0, (%rdx)
vmovdqu %xmm3, 16(%rdx)
ret
FN_END hchacha_avx2

GLOBAL_HIDDEN_FN_EXT chacha_avx2, 6, 16
pushq %rbp
movq %rsp, %rbp
subq $64, %rsp
andq $~63, %rsp
vmovdqu 0(%rdi), %xmm0
vmovdqu 16(%rdi), %xmm1
vmovdqa %xmm0, 0(%rsp)
vmovdqa %xmm1, 16(%rsp)
xorq %rdi, %rdi
movq %rdi, 32(%rsp)
movq 0(%rsi), %rsi
movq %rsi, 40(%rsp)
movq %r9, 48(%rsp)
movq %rsp, %rdi
movq %rdx, %rsi
movq %rcx, %rdx
movq %r8, %rcx
call chacha_blocks_avx2_local
vpxor %xmm0, %xmm0, %xmm0
vmovdqa %xmm0, 0(%rsp)
vmovdqa %xmm0, 16(%rsp)
vmovdqa %xmm0, 32(%rsp)
movq %rbp, %rsp
popq %rbp
ret
FN_END chacha_avx2

GLOBAL_HIDDEN_FN_EXT xchacha_avx2, 6, 16
pushq %rbp
pushq %rbx
movq %rsp, %rbp
subq $64, %rsp
andq $~63, %rsp
movq %rsp, %rbx
xorq %rax, %rax
movq %rax, 32(%rbx)
movq 16(%rsi), %rax
movq %rax, 40(%rbx)
movq %r9, 48(%rbx)
pushq %rdx
pushq %rcx
pushq %r8
movq %rbx, %rdx
movq %r9, %rcx
call hchacha_avx2_local
movq %rbx, %rdi
popq %rcx
popq %rdx
popq %rsi
call chacha_blocks_avx2_local
vpxor %xmm0, %xmm0, %xmm0
vmovdqa %xmm0, 0(%rbx)
vmovdqa %xmm0, 16(%rbx)
vmovdqa %xmm0, 32(%rbx)
movq %rbp, %rsp
popq %rbx
popq %rbp
ret
FN_END xchacha_avx2

INCLUDE_VAR_FILE "chacha/chacha_constants_x86.inc", chacha_constants

