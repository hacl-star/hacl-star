	.text
	.p2align	5
	.globl	_chacha20_avx2
	.globl	chacha20_avx2
_chacha20_avx2:
chacha20_avx2:
	movq	%rsp, %r11
	subq	$1156, %rsp
	andq	$-32, %rsp
	cmpl	$257, %edx
	jb  	Lchacha20_avx2$1
	vmovdqu	g_r16(%rip), %ymm0
	vmovdqu	g_r8(%rip), %ymm1
	vmovdqu	%ymm0, 800(%rsp)
	vmovdqu	%ymm1, 768(%rsp)
	movl	%r9d, 1152(%rsp)
	vpbroadcastd	g_sigma0(%rip), %ymm0
	vpbroadcastd	g_sigma1(%rip), %ymm1
	vpbroadcastd	g_sigma2(%rip), %ymm2
	vpbroadcastd	g_sigma3(%rip), %ymm3
	vpbroadcastd	(%rcx), %ymm4
	vpbroadcastd	4(%rcx), %ymm5
	vpbroadcastd	8(%rcx), %ymm6
	vpbroadcastd	12(%rcx), %ymm7
	vpbroadcastd	16(%rcx), %ymm8
	vpbroadcastd	20(%rcx), %ymm9
	vpbroadcastd	24(%rcx), %ymm10
	vpbroadcastd	28(%rcx), %ymm11
	vpbroadcastd	1152(%rsp), %ymm12
	vpaddd	g_cnt(%rip), %ymm12, %ymm12
	vpbroadcastd	(%r8), %ymm13
	vpbroadcastd	4(%r8), %ymm14
	vpbroadcastd	8(%r8), %ymm15
	vmovdqu	%ymm0, 256(%rsp)
	vmovdqu	%ymm1, 288(%rsp)
	vmovdqu	%ymm2, 320(%rsp)
	vmovdqu	%ymm3, 352(%rsp)
	vmovdqu	%ymm4, 384(%rsp)
	vmovdqu	%ymm5, 416(%rsp)
	vmovdqu	%ymm6, 448(%rsp)
	vmovdqu	%ymm7, 480(%rsp)
	vmovdqu	%ymm8, 512(%rsp)
	vmovdqu	%ymm9, 544(%rsp)
	vmovdqu	%ymm10, 576(%rsp)
	vmovdqu	%ymm11, 608(%rsp)
	vmovdqu	%ymm12, 640(%rsp)
	vmovdqu	%ymm13, 672(%rsp)
	vmovdqu	%ymm14, 704(%rsp)
	vmovdqu	%ymm15, 736(%rsp)
	jmp 	Lchacha20_avx2$28
Lchacha20_avx2$29:
	vmovdqu	256(%rsp), %ymm0
	vmovdqu	288(%rsp), %ymm1
	vmovdqu	320(%rsp), %ymm2
	vmovdqu	352(%rsp), %ymm3
	vmovdqu	384(%rsp), %ymm4
	vmovdqu	416(%rsp), %ymm5
	vmovdqu	448(%rsp), %ymm6
	vmovdqu	480(%rsp), %ymm7
	vmovdqu	512(%rsp), %ymm8
	vmovdqu	544(%rsp), %ymm9
	vmovdqu	576(%rsp), %ymm10
	vmovdqu	608(%rsp), %ymm11
	vmovdqu	640(%rsp), %ymm12
	vmovdqu	672(%rsp), %ymm13
	vmovdqu	704(%rsp), %ymm14
	vmovdqu	736(%rsp), %ymm15
	vmovdqu	%ymm15, 1088(%rsp)
	movq	$10, %rax
	.p2align	5
Lchacha20_avx2$30:
	vpaddd	%ymm4, %ymm0, %ymm0
	vpxor	%ymm0, %ymm12, %ymm12
	vpshufb	800(%rsp), %ymm12, %ymm12
	vpaddd	%ymm12, %ymm8, %ymm8
	vpaddd	%ymm6, %ymm2, %ymm2
	vpxor	%ymm8, %ymm4, %ymm4
	vpxor	%ymm2, %ymm14, %ymm14
	vpslld	$12, %ymm4, %ymm15
	vpsrld	$20, %ymm4, %ymm4
	vpxor	%ymm15, %ymm4, %ymm4
	vpshufb	800(%rsp), %ymm14, %ymm14
	vpaddd	%ymm4, %ymm0, %ymm0
	vpaddd	%ymm14, %ymm10, %ymm10
	vpxor	%ymm0, %ymm12, %ymm12
	vpxor	%ymm10, %ymm6, %ymm6
	vpshufb	768(%rsp), %ymm12, %ymm12
	vpslld	$12, %ymm6, %ymm15
	vpsrld	$20, %ymm6, %ymm6
	vpxor	%ymm15, %ymm6, %ymm6
	vpaddd	%ymm12, %ymm8, %ymm8
	vpaddd	%ymm6, %ymm2, %ymm2
	vpxor	%ymm8, %ymm4, %ymm4
	vpxor	%ymm2, %ymm14, %ymm14
	vpslld	$7, %ymm4, %ymm15
	vpsrld	$25, %ymm4, %ymm4
	vpxor	%ymm15, %ymm4, %ymm4
	vpshufb	768(%rsp), %ymm14, %ymm14
	vpaddd	%ymm14, %ymm10, %ymm10
	vpxor	%ymm10, %ymm6, %ymm6
	vpslld	$7, %ymm6, %ymm15
	vpsrld	$25, %ymm6, %ymm6
	vpxor	%ymm15, %ymm6, %ymm6
	vmovdqu	1088(%rsp), %ymm15
	vmovdqu	%ymm14, 1088(%rsp)
	vpaddd	%ymm5, %ymm1, %ymm1
	vpxor	%ymm1, %ymm13, %ymm13
	vpshufb	800(%rsp), %ymm13, %ymm13
	vpaddd	%ymm13, %ymm9, %ymm9
	vpaddd	%ymm7, %ymm3, %ymm3
	vpxor	%ymm9, %ymm5, %ymm5
	vpxor	%ymm3, %ymm15, %ymm14
	vpslld	$12, %ymm5, %ymm15
	vpsrld	$20, %ymm5, %ymm5
	vpxor	%ymm15, %ymm5, %ymm5
	vpshufb	800(%rsp), %ymm14, %ymm14
	vpaddd	%ymm5, %ymm1, %ymm1
	vpaddd	%ymm14, %ymm11, %ymm11
	vpxor	%ymm1, %ymm13, %ymm13
	vpxor	%ymm11, %ymm7, %ymm7
	vpshufb	768(%rsp), %ymm13, %ymm13
	vpslld	$12, %ymm7, %ymm15
	vpsrld	$20, %ymm7, %ymm7
	vpxor	%ymm15, %ymm7, %ymm7
	vpaddd	%ymm13, %ymm9, %ymm9
	vpaddd	%ymm7, %ymm3, %ymm3
	vpxor	%ymm9, %ymm5, %ymm5
	vpxor	%ymm3, %ymm14, %ymm14
	vpslld	$7, %ymm5, %ymm15
	vpsrld	$25, %ymm5, %ymm5
	vpxor	%ymm15, %ymm5, %ymm5
	vpshufb	768(%rsp), %ymm14, %ymm14
	vpaddd	%ymm14, %ymm11, %ymm11
	vpxor	%ymm11, %ymm7, %ymm7
	vpslld	$7, %ymm7, %ymm15
	vpsrld	$25, %ymm7, %ymm7
	vpxor	%ymm15, %ymm7, %ymm7
	vpaddd	%ymm6, %ymm1, %ymm1
	vpxor	%ymm1, %ymm12, %ymm12
	vpshufb	800(%rsp), %ymm12, %ymm12
	vpaddd	%ymm12, %ymm11, %ymm11
	vpaddd	%ymm5, %ymm0, %ymm0
	vpxor	%ymm11, %ymm6, %ymm6
	vpxor	%ymm0, %ymm14, %ymm14
	vpslld	$12, %ymm6, %ymm15
	vpsrld	$20, %ymm6, %ymm6
	vpxor	%ymm15, %ymm6, %ymm6
	vpshufb	800(%rsp), %ymm14, %ymm14
	vpaddd	%ymm6, %ymm1, %ymm1
	vpaddd	%ymm14, %ymm10, %ymm10
	vpxor	%ymm1, %ymm12, %ymm12
	vpxor	%ymm10, %ymm5, %ymm5
	vpshufb	768(%rsp), %ymm12, %ymm12
	vpslld	$12, %ymm5, %ymm15
	vpsrld	$20, %ymm5, %ymm5
	vpxor	%ymm15, %ymm5, %ymm5
	vpaddd	%ymm12, %ymm11, %ymm11
	vpaddd	%ymm5, %ymm0, %ymm0
	vpxor	%ymm11, %ymm6, %ymm6
	vpxor	%ymm0, %ymm14, %ymm14
	vpslld	$7, %ymm6, %ymm15
	vpsrld	$25, %ymm6, %ymm6
	vpxor	%ymm15, %ymm6, %ymm6
	vpshufb	768(%rsp), %ymm14, %ymm14
	vpaddd	%ymm14, %ymm10, %ymm10
	vpxor	%ymm10, %ymm5, %ymm5
	vpslld	$7, %ymm5, %ymm15
	vpsrld	$25, %ymm5, %ymm5
	vpxor	%ymm15, %ymm5, %ymm5
	vmovdqu	1088(%rsp), %ymm15
	vmovdqu	%ymm14, 1088(%rsp)
	vpaddd	%ymm7, %ymm2, %ymm2
	vpxor	%ymm2, %ymm13, %ymm13
	vpshufb	800(%rsp), %ymm13, %ymm13
	vpaddd	%ymm13, %ymm8, %ymm8
	vpaddd	%ymm4, %ymm3, %ymm3
	vpxor	%ymm8, %ymm7, %ymm7
	vpxor	%ymm3, %ymm15, %ymm14
	vpslld	$12, %ymm7, %ymm15
	vpsrld	$20, %ymm7, %ymm7
	vpxor	%ymm15, %ymm7, %ymm7
	vpshufb	800(%rsp), %ymm14, %ymm14
	vpaddd	%ymm7, %ymm2, %ymm2
	vpaddd	%ymm14, %ymm9, %ymm9
	vpxor	%ymm2, %ymm13, %ymm13
	vpxor	%ymm9, %ymm4, %ymm4
	vpshufb	768(%rsp), %ymm13, %ymm13
	vpslld	$12, %ymm4, %ymm15
	vpsrld	$20, %ymm4, %ymm4
	vpxor	%ymm15, %ymm4, %ymm4
	vpaddd	%ymm13, %ymm8, %ymm8
	vpaddd	%ymm4, %ymm3, %ymm3
	vpxor	%ymm8, %ymm7, %ymm7
	vpxor	%ymm3, %ymm14, %ymm14
	vpslld	$7, %ymm7, %ymm15
	vpsrld	$25, %ymm7, %ymm7
	vpxor	%ymm15, %ymm7, %ymm7
	vpshufb	768(%rsp), %ymm14, %ymm14
	vpaddd	%ymm14, %ymm9, %ymm9
	vpxor	%ymm9, %ymm4, %ymm4
	vpslld	$7, %ymm4, %ymm15
	vpsrld	$25, %ymm4, %ymm4
	vpxor	%ymm15, %ymm4, %ymm4
	decq	%rax
	jne 	Lchacha20_avx2$30
	vmovdqu	1088(%rsp), %ymm15
	vpaddd	256(%rsp), %ymm0, %ymm0
	vpaddd	288(%rsp), %ymm1, %ymm1
	vpaddd	320(%rsp), %ymm2, %ymm2
	vpaddd	352(%rsp), %ymm3, %ymm3
	vpaddd	384(%rsp), %ymm4, %ymm4
	vpaddd	416(%rsp), %ymm5, %ymm5
	vpaddd	448(%rsp), %ymm6, %ymm6
	vpaddd	480(%rsp), %ymm7, %ymm7
	vpaddd	512(%rsp), %ymm8, %ymm8
	vpaddd	544(%rsp), %ymm9, %ymm9
	vpaddd	576(%rsp), %ymm10, %ymm10
	vpaddd	608(%rsp), %ymm11, %ymm11
	vpaddd	640(%rsp), %ymm12, %ymm12
	vpaddd	672(%rsp), %ymm13, %ymm13
	vpaddd	704(%rsp), %ymm14, %ymm14
	vpaddd	736(%rsp), %ymm15, %ymm15
	vmovdqu	%ymm8, 832(%rsp)
	vmovdqu	%ymm9, 864(%rsp)
	vmovdqu	%ymm10, 896(%rsp)
	vmovdqu	%ymm11, 928(%rsp)
	vmovdqu	%ymm12, 960(%rsp)
	vmovdqu	%ymm13, 992(%rsp)
	vmovdqu	%ymm14, 1024(%rsp)
	vmovdqu	%ymm15, 1056(%rsp)
	vpunpckldq	%ymm1, %ymm0, %ymm8
	vpunpckhdq	%ymm1, %ymm0, %ymm0
	vpunpckldq	%ymm3, %ymm2, %ymm1
	vpunpckhdq	%ymm3, %ymm2, %ymm2
	vpunpckldq	%ymm5, %ymm4, %ymm3
	vpunpckhdq	%ymm5, %ymm4, %ymm4
	vpunpckldq	%ymm7, %ymm6, %ymm5
	vpunpckhdq	%ymm7, %ymm6, %ymm6
	vpunpcklqdq	%ymm1, %ymm8, %ymm7
	vpunpcklqdq	%ymm5, %ymm3, %ymm9
	vpunpckhqdq	%ymm1, %ymm8, %ymm1
	vpunpckhqdq	%ymm5, %ymm3, %ymm3
	vpunpcklqdq	%ymm2, %ymm0, %ymm5
	vpunpcklqdq	%ymm6, %ymm4, %ymm8
	vpunpckhqdq	%ymm2, %ymm0, %ymm0
	vpunpckhqdq	%ymm6, %ymm4, %ymm2
	vperm2i128	$32, %ymm9, %ymm7, %ymm4
	vperm2i128	$49, %ymm9, %ymm7, %ymm6
	vperm2i128	$32, %ymm3, %ymm1, %ymm7
	vperm2i128	$49, %ymm3, %ymm1, %ymm1
	vperm2i128	$32, %ymm8, %ymm5, %ymm3
	vperm2i128	$49, %ymm8, %ymm5, %ymm5
	vperm2i128	$32, %ymm2, %ymm0, %ymm8
	vperm2i128	$49, %ymm2, %ymm0, %ymm0
	vpxor	(%rsi), %ymm4, %ymm2
	vpxor	64(%rsi), %ymm7, %ymm4
	vpxor	128(%rsi), %ymm3, %ymm3
	vpxor	192(%rsi), %ymm8, %ymm7
	vpxor	256(%rsi), %ymm6, %ymm6
	vpxor	320(%rsi), %ymm1, %ymm1
	vpxor	384(%rsi), %ymm5, %ymm5
	vpxor	448(%rsi), %ymm0, %ymm0
	vmovdqu	%ymm2, (%rdi)
	vmovdqu	%ymm4, 64(%rdi)
	vmovdqu	%ymm3, 128(%rdi)
	vmovdqu	%ymm7, 192(%rdi)
	vmovdqu	%ymm6, 256(%rdi)
	vmovdqu	%ymm1, 320(%rdi)
	vmovdqu	%ymm5, 384(%rdi)
	vmovdqu	%ymm0, 448(%rdi)
	vmovdqu	832(%rsp), %ymm0
	vmovdqu	896(%rsp), %ymm1
	vmovdqu	960(%rsp), %ymm2
	vmovdqu	1024(%rsp), %ymm3
	vpunpckldq	864(%rsp), %ymm0, %ymm4
	vpunpckhdq	864(%rsp), %ymm0, %ymm0
	vpunpckldq	928(%rsp), %ymm1, %ymm5
	vpunpckhdq	928(%rsp), %ymm1, %ymm1
	vpunpckldq	992(%rsp), %ymm2, %ymm6
	vpunpckhdq	992(%rsp), %ymm2, %ymm2
	vpunpckldq	1056(%rsp), %ymm3, %ymm7
	vpunpckhdq	1056(%rsp), %ymm3, %ymm3
	vpunpcklqdq	%ymm5, %ymm4, %ymm8
	vpunpcklqdq	%ymm7, %ymm6, %ymm9
	vpunpckhqdq	%ymm5, %ymm4, %ymm4
	vpunpckhqdq	%ymm7, %ymm6, %ymm5
	vpunpcklqdq	%ymm1, %ymm0, %ymm6
	vpunpcklqdq	%ymm3, %ymm2, %ymm7
	vpunpckhqdq	%ymm1, %ymm0, %ymm0
	vpunpckhqdq	%ymm3, %ymm2, %ymm1
	vperm2i128	$32, %ymm9, %ymm8, %ymm2
	vperm2i128	$49, %ymm9, %ymm8, %ymm3
	vperm2i128	$32, %ymm5, %ymm4, %ymm8
	vperm2i128	$49, %ymm5, %ymm4, %ymm4
	vperm2i128	$32, %ymm7, %ymm6, %ymm5
	vperm2i128	$49, %ymm7, %ymm6, %ymm6
	vperm2i128	$32, %ymm1, %ymm0, %ymm7
	vperm2i128	$49, %ymm1, %ymm0, %ymm0
	vpxor	32(%rsi), %ymm2, %ymm1
	vpxor	96(%rsi), %ymm8, %ymm2
	vpxor	160(%rsi), %ymm5, %ymm5
	vpxor	224(%rsi), %ymm7, %ymm7
	vpxor	288(%rsi), %ymm3, %ymm3
	vpxor	352(%rsi), %ymm4, %ymm4
	vpxor	416(%rsi), %ymm6, %ymm6
	vpxor	480(%rsi), %ymm0, %ymm0
	vmovdqu	%ymm1, 32(%rdi)
	vmovdqu	%ymm2, 96(%rdi)
	vmovdqu	%ymm5, 160(%rdi)
	vmovdqu	%ymm7, 224(%rdi)
	vmovdqu	%ymm3, 288(%rdi)
	vmovdqu	%ymm4, 352(%rdi)
	vmovdqu	%ymm6, 416(%rdi)
	vmovdqu	%ymm0, 480(%rdi)
	addq	$512, %rdi
	addq	$512, %rsi
	subl	$512, %edx
	vmovdqu	g_cnt_inc(%rip), %ymm0
	vpaddd	640(%rsp), %ymm0, %ymm0
	vmovdqu	%ymm0, 640(%rsp)
Lchacha20_avx2$28:
	cmpl	$512, %edx
	jnb 	Lchacha20_avx2$29
	cmpl	$0, %edx
	jbe 	Lchacha20_avx2$19
	vmovdqu	256(%rsp), %ymm0
	vmovdqu	288(%rsp), %ymm1
	vmovdqu	320(%rsp), %ymm2
	vmovdqu	352(%rsp), %ymm3
	vmovdqu	384(%rsp), %ymm4
	vmovdqu	416(%rsp), %ymm5
	vmovdqu	448(%rsp), %ymm6
	vmovdqu	480(%rsp), %ymm7
	vmovdqu	512(%rsp), %ymm8
	vmovdqu	544(%rsp), %ymm9
	vmovdqu	576(%rsp), %ymm10
	vmovdqu	608(%rsp), %ymm11
	vmovdqu	640(%rsp), %ymm12
	vmovdqu	672(%rsp), %ymm13
	vmovdqu	704(%rsp), %ymm14
	vmovdqu	736(%rsp), %ymm15
	vmovdqu	%ymm15, 1088(%rsp)
	movq	$10, %rax
	.p2align	5
Lchacha20_avx2$27:
	vpaddd	%ymm4, %ymm0, %ymm0
	vpxor	%ymm0, %ymm12, %ymm12
	vpshufb	800(%rsp), %ymm12, %ymm12
	vpaddd	%ymm12, %ymm8, %ymm8
	vpaddd	%ymm6, %ymm2, %ymm2
	vpxor	%ymm8, %ymm4, %ymm4
	vpxor	%ymm2, %ymm14, %ymm14
	vpslld	$12, %ymm4, %ymm15
	vpsrld	$20, %ymm4, %ymm4
	vpxor	%ymm15, %ymm4, %ymm4
	vpshufb	800(%rsp), %ymm14, %ymm14
	vpaddd	%ymm4, %ymm0, %ymm0
	vpaddd	%ymm14, %ymm10, %ymm10
	vpxor	%ymm0, %ymm12, %ymm12
	vpxor	%ymm10, %ymm6, %ymm6
	vpshufb	768(%rsp), %ymm12, %ymm12
	vpslld	$12, %ymm6, %ymm15
	vpsrld	$20, %ymm6, %ymm6
	vpxor	%ymm15, %ymm6, %ymm6
	vpaddd	%ymm12, %ymm8, %ymm8
	vpaddd	%ymm6, %ymm2, %ymm2
	vpxor	%ymm8, %ymm4, %ymm4
	vpxor	%ymm2, %ymm14, %ymm14
	vpslld	$7, %ymm4, %ymm15
	vpsrld	$25, %ymm4, %ymm4
	vpxor	%ymm15, %ymm4, %ymm4
	vpshufb	768(%rsp), %ymm14, %ymm14
	vpaddd	%ymm14, %ymm10, %ymm10
	vpxor	%ymm10, %ymm6, %ymm6
	vpslld	$7, %ymm6, %ymm15
	vpsrld	$25, %ymm6, %ymm6
	vpxor	%ymm15, %ymm6, %ymm6
	vmovdqu	1088(%rsp), %ymm15
	vmovdqu	%ymm14, 1088(%rsp)
	vpaddd	%ymm5, %ymm1, %ymm1
	vpxor	%ymm1, %ymm13, %ymm13
	vpshufb	800(%rsp), %ymm13, %ymm13
	vpaddd	%ymm13, %ymm9, %ymm9
	vpaddd	%ymm7, %ymm3, %ymm3
	vpxor	%ymm9, %ymm5, %ymm5
	vpxor	%ymm3, %ymm15, %ymm14
	vpslld	$12, %ymm5, %ymm15
	vpsrld	$20, %ymm5, %ymm5
	vpxor	%ymm15, %ymm5, %ymm5
	vpshufb	800(%rsp), %ymm14, %ymm14
	vpaddd	%ymm5, %ymm1, %ymm1
	vpaddd	%ymm14, %ymm11, %ymm11
	vpxor	%ymm1, %ymm13, %ymm13
	vpxor	%ymm11, %ymm7, %ymm7
	vpshufb	768(%rsp), %ymm13, %ymm13
	vpslld	$12, %ymm7, %ymm15
	vpsrld	$20, %ymm7, %ymm7
	vpxor	%ymm15, %ymm7, %ymm7
	vpaddd	%ymm13, %ymm9, %ymm9
	vpaddd	%ymm7, %ymm3, %ymm3
	vpxor	%ymm9, %ymm5, %ymm5
	vpxor	%ymm3, %ymm14, %ymm14
	vpslld	$7, %ymm5, %ymm15
	vpsrld	$25, %ymm5, %ymm5
	vpxor	%ymm15, %ymm5, %ymm5
	vpshufb	768(%rsp), %ymm14, %ymm14
	vpaddd	%ymm14, %ymm11, %ymm11
	vpxor	%ymm11, %ymm7, %ymm7
	vpslld	$7, %ymm7, %ymm15
	vpsrld	$25, %ymm7, %ymm7
	vpxor	%ymm15, %ymm7, %ymm7
	vpaddd	%ymm6, %ymm1, %ymm1
	vpxor	%ymm1, %ymm12, %ymm12
	vpshufb	800(%rsp), %ymm12, %ymm12
	vpaddd	%ymm12, %ymm11, %ymm11
	vpaddd	%ymm5, %ymm0, %ymm0
	vpxor	%ymm11, %ymm6, %ymm6
	vpxor	%ymm0, %ymm14, %ymm14
	vpslld	$12, %ymm6, %ymm15
	vpsrld	$20, %ymm6, %ymm6
	vpxor	%ymm15, %ymm6, %ymm6
	vpshufb	800(%rsp), %ymm14, %ymm14
	vpaddd	%ymm6, %ymm1, %ymm1
	vpaddd	%ymm14, %ymm10, %ymm10
	vpxor	%ymm1, %ymm12, %ymm12
	vpxor	%ymm10, %ymm5, %ymm5
	vpshufb	768(%rsp), %ymm12, %ymm12
	vpslld	$12, %ymm5, %ymm15
	vpsrld	$20, %ymm5, %ymm5
	vpxor	%ymm15, %ymm5, %ymm5
	vpaddd	%ymm12, %ymm11, %ymm11
	vpaddd	%ymm5, %ymm0, %ymm0
	vpxor	%ymm11, %ymm6, %ymm6
	vpxor	%ymm0, %ymm14, %ymm14
	vpslld	$7, %ymm6, %ymm15
	vpsrld	$25, %ymm6, %ymm6
	vpxor	%ymm15, %ymm6, %ymm6
	vpshufb	768(%rsp), %ymm14, %ymm14
	vpaddd	%ymm14, %ymm10, %ymm10
	vpxor	%ymm10, %ymm5, %ymm5
	vpslld	$7, %ymm5, %ymm15
	vpsrld	$25, %ymm5, %ymm5
	vpxor	%ymm15, %ymm5, %ymm5
	vmovdqu	1088(%rsp), %ymm15
	vmovdqu	%ymm14, 1088(%rsp)
	vpaddd	%ymm7, %ymm2, %ymm2
	vpxor	%ymm2, %ymm13, %ymm13
	vpshufb	800(%rsp), %ymm13, %ymm13
	vpaddd	%ymm13, %ymm8, %ymm8
	vpaddd	%ymm4, %ymm3, %ymm3
	vpxor	%ymm8, %ymm7, %ymm7
	vpxor	%ymm3, %ymm15, %ymm14
	vpslld	$12, %ymm7, %ymm15
	vpsrld	$20, %ymm7, %ymm7
	vpxor	%ymm15, %ymm7, %ymm7
	vpshufb	800(%rsp), %ymm14, %ymm14
	vpaddd	%ymm7, %ymm2, %ymm2
	vpaddd	%ymm14, %ymm9, %ymm9
	vpxor	%ymm2, %ymm13, %ymm13
	vpxor	%ymm9, %ymm4, %ymm4
	vpshufb	768(%rsp), %ymm13, %ymm13
	vpslld	$12, %ymm4, %ymm15
	vpsrld	$20, %ymm4, %ymm4
	vpxor	%ymm15, %ymm4, %ymm4
	vpaddd	%ymm13, %ymm8, %ymm8
	vpaddd	%ymm4, %ymm3, %ymm3
	vpxor	%ymm8, %ymm7, %ymm7
	vpxor	%ymm3, %ymm14, %ymm14
	vpslld	$7, %ymm7, %ymm15
	vpsrld	$25, %ymm7, %ymm7
	vpxor	%ymm15, %ymm7, %ymm7
	vpshufb	768(%rsp), %ymm14, %ymm14
	vpaddd	%ymm14, %ymm9, %ymm9
	vpxor	%ymm9, %ymm4, %ymm4
	vpslld	$7, %ymm4, %ymm15
	vpsrld	$25, %ymm4, %ymm4
	vpxor	%ymm15, %ymm4, %ymm4
	decq	%rax
	jne 	Lchacha20_avx2$27
	vmovdqu	1088(%rsp), %ymm15
	vpaddd	256(%rsp), %ymm0, %ymm0
	vpaddd	288(%rsp), %ymm1, %ymm1
	vpaddd	320(%rsp), %ymm2, %ymm2
	vpaddd	352(%rsp), %ymm3, %ymm3
	vpaddd	384(%rsp), %ymm4, %ymm4
	vpaddd	416(%rsp), %ymm5, %ymm5
	vpaddd	448(%rsp), %ymm6, %ymm6
	vpaddd	480(%rsp), %ymm7, %ymm7
	vpaddd	512(%rsp), %ymm8, %ymm8
	vpaddd	544(%rsp), %ymm9, %ymm9
	vpaddd	576(%rsp), %ymm10, %ymm10
	vpaddd	608(%rsp), %ymm11, %ymm11
	vpaddd	640(%rsp), %ymm12, %ymm12
	vpaddd	672(%rsp), %ymm13, %ymm13
	vpaddd	704(%rsp), %ymm14, %ymm14
	vpaddd	736(%rsp), %ymm15, %ymm15
	vmovdqu	%ymm8, 832(%rsp)
	vmovdqu	%ymm9, 864(%rsp)
	vmovdqu	%ymm10, 896(%rsp)
	vmovdqu	%ymm11, 928(%rsp)
	vmovdqu	%ymm12, 960(%rsp)
	vmovdqu	%ymm13, 992(%rsp)
	vmovdqu	%ymm14, 1024(%rsp)
	vmovdqu	%ymm15, 1056(%rsp)
	vpunpckldq	%ymm1, %ymm0, %ymm8
	vpunpckhdq	%ymm1, %ymm0, %ymm0
	vpunpckldq	%ymm3, %ymm2, %ymm1
	vpunpckhdq	%ymm3, %ymm2, %ymm2
	vpunpckldq	%ymm5, %ymm4, %ymm3
	vpunpckhdq	%ymm5, %ymm4, %ymm4
	vpunpckldq	%ymm7, %ymm6, %ymm5
	vpunpckhdq	%ymm7, %ymm6, %ymm6
	vpunpcklqdq	%ymm1, %ymm8, %ymm7
	vpunpcklqdq	%ymm5, %ymm3, %ymm9
	vpunpckhqdq	%ymm1, %ymm8, %ymm1
	vpunpckhqdq	%ymm5, %ymm3, %ymm3
	vpunpcklqdq	%ymm2, %ymm0, %ymm5
	vpunpcklqdq	%ymm6, %ymm4, %ymm8
	vpunpckhqdq	%ymm2, %ymm0, %ymm0
	vpunpckhqdq	%ymm6, %ymm4, %ymm2
	vperm2i128	$32, %ymm9, %ymm7, %ymm4
	vperm2i128	$49, %ymm9, %ymm7, %ymm6
	vperm2i128	$32, %ymm3, %ymm1, %ymm7
	vperm2i128	$49, %ymm3, %ymm1, %ymm1
	vperm2i128	$32, %ymm8, %ymm5, %ymm3
	vperm2i128	$49, %ymm8, %ymm5, %ymm5
	vperm2i128	$32, %ymm2, %ymm0, %ymm8
	vperm2i128	$49, %ymm2, %ymm0, %ymm0
	vmovdqu	%ymm4, (%rsp)
	vmovdqu	%ymm7, 32(%rsp)
	vmovdqu	%ymm3, 64(%rsp)
	vmovdqu	%ymm8, 96(%rsp)
	vmovdqu	%ymm6, 128(%rsp)
	vmovdqu	%ymm1, 160(%rsp)
	vmovdqu	%ymm5, 192(%rsp)
	vmovdqu	%ymm0, 224(%rsp)
	vmovdqu	832(%rsp), %ymm0
	vmovdqu	896(%rsp), %ymm1
	vmovdqu	960(%rsp), %ymm2
	vmovdqu	1024(%rsp), %ymm3
	vpunpckldq	864(%rsp), %ymm0, %ymm4
	vpunpckhdq	864(%rsp), %ymm0, %ymm0
	vpunpckldq	928(%rsp), %ymm1, %ymm5
	vpunpckhdq	928(%rsp), %ymm1, %ymm1
	vpunpckldq	992(%rsp), %ymm2, %ymm6
	vpunpckhdq	992(%rsp), %ymm2, %ymm2
	vpunpckldq	1056(%rsp), %ymm3, %ymm7
	vpunpckhdq	1056(%rsp), %ymm3, %ymm3
	vpunpcklqdq	%ymm5, %ymm4, %ymm8
	vpunpcklqdq	%ymm7, %ymm6, %ymm9
	vpunpckhqdq	%ymm5, %ymm4, %ymm4
	vpunpckhqdq	%ymm7, %ymm6, %ymm5
	vpunpcklqdq	%ymm1, %ymm0, %ymm6
	vpunpcklqdq	%ymm3, %ymm2, %ymm7
	vpunpckhqdq	%ymm1, %ymm0, %ymm0
	vpunpckhqdq	%ymm3, %ymm2, %ymm1
	vperm2i128	$32, %ymm9, %ymm8, %ymm2
	vperm2i128	$49, %ymm9, %ymm8, %ymm3
	vperm2i128	$32, %ymm5, %ymm4, %ymm8
	vperm2i128	$49, %ymm5, %ymm4, %ymm4
	vperm2i128	$32, %ymm7, %ymm6, %ymm5
	vperm2i128	$49, %ymm7, %ymm6, %ymm6
	vperm2i128	$32, %ymm1, %ymm0, %ymm7
	vperm2i128	$49, %ymm1, %ymm0, %ymm0
	vmovdqu	(%rsp), %ymm1
	vmovdqu	32(%rsp), %ymm13
	vmovdqu	%ymm8, %ymm12
	vmovdqu	64(%rsp), %ymm8
	vmovdqu	%ymm5, %ymm9
	vmovdqu	96(%rsp), %ymm10
	vmovdqu	%ymm7, %ymm11
	cmpl	$256, %edx
	jb  	Lchacha20_avx2$26
	vpxor	(%rsi), %ymm1, %ymm1
	vpxor	32(%rsi), %ymm2, %ymm2
	vpxor	64(%rsi), %ymm13, %ymm5
	vpxor	96(%rsi), %ymm12, %ymm7
	vpxor	128(%rsi), %ymm8, %ymm8
	vpxor	160(%rsi), %ymm9, %ymm9
	vpxor	192(%rsi), %ymm10, %ymm10
	vpxor	224(%rsi), %ymm11, %ymm11
	vmovdqu	%ymm1, (%rdi)
	vmovdqu	%ymm2, 32(%rdi)
	vmovdqu	%ymm5, 64(%rdi)
	vmovdqu	%ymm7, 96(%rdi)
	vmovdqu	%ymm8, 128(%rdi)
	vmovdqu	%ymm9, 160(%rdi)
	vmovdqu	%ymm10, 192(%rdi)
	vmovdqu	%ymm11, 224(%rdi)
	addq	$256, %rdi
	addq	$256, %rsi
	subl	$256, %edx
	vmovdqu	128(%rsp), %ymm1
	vmovdqu	%ymm3, %ymm2
	vmovdqu	160(%rsp), %ymm13
	vmovdqu	%ymm4, %ymm12
	vmovdqu	192(%rsp), %ymm8
	vmovdqu	%ymm6, %ymm9
	vmovdqu	224(%rsp), %ymm10
	vmovdqu	%ymm0, %ymm11
Lchacha20_avx2$26:
	vmovdqu	%ymm1, %ymm0
	vmovdqu	%ymm2, %ymm1
	vmovdqu	%ymm13, %ymm2
	vmovdqu	%ymm12, %ymm3
	cmpl	$128, %edx
	jb  	Lchacha20_avx2$25
	vpxor	(%rsi), %ymm0, %ymm0
	vpxor	32(%rsi), %ymm1, %ymm1
	vpxor	64(%rsi), %ymm2, %ymm2
	vpxor	96(%rsi), %ymm3, %ymm3
	vmovdqu	%ymm0, (%rdi)
	vmovdqu	%ymm1, 32(%rdi)
	vmovdqu	%ymm2, 64(%rdi)
	vmovdqu	%ymm3, 96(%rdi)
	addq	$128, %rdi
	addq	$128, %rsi
	subl	$128, %edx
	vmovdqu	%ymm8, %ymm0
	vmovdqu	%ymm9, %ymm1
	vmovdqu	%ymm10, %ymm2
	vmovdqu	%ymm11, %ymm3
Lchacha20_avx2$25:
	cmpl	$64, %edx
	jb  	Lchacha20_avx2$24
	vpxor	(%rsi), %ymm0, %ymm0
	vpxor	32(%rsi), %ymm1, %ymm1
	vmovdqu	%ymm0, (%rdi)
	vmovdqu	%ymm1, 32(%rdi)
	addq	$64, %rdi
	addq	$64, %rsi
	subl	$64, %edx
	vmovdqu	%ymm2, %ymm0
	vmovdqu	%ymm3, %ymm1
Lchacha20_avx2$24:
	cmpl	$32, %edx
	jb  	Lchacha20_avx2$23
	vpxor	(%rsi), %ymm0, %ymm0
	vmovdqu	%ymm0, (%rdi)
	addq	$32, %rdi
	addq	$32, %rsi
	subl	$32, %edx
	vmovdqu	%ymm1, %ymm0
Lchacha20_avx2$23:
	vextracti128	$0, %ymm0, %xmm1
	cmpl	$16, %edx
	jb  	Lchacha20_avx2$22
	vpxor	(%rsi), %xmm1, %xmm1
	vmovdqu	%xmm1, (%rdi)
	addq	$16, %rdi
	addq	$16, %rsi
	subl	$16, %edx
	vextracti128	$1, %ymm0, %xmm1
Lchacha20_avx2$22:
	vmovdqu	%xmm1, 1120(%rsp)
	movq	$0, %rax
	jmp 	Lchacha20_avx2$20
Lchacha20_avx2$21:
	movb	(%rsi,%rax), %cl
	xorb	1120(%rsp,%rax), %cl
	movb	%cl, (%rdi,%rax)
	incq	%rax
Lchacha20_avx2$20:
	cmpl	%edx, %eax
	jb  	Lchacha20_avx2$21
Lchacha20_avx2$19:
	jmp 	Lchacha20_avx2$2
Lchacha20_avx2$1:
	vmovdqu	g_p0(%rip), %xmm0
	vpinsrd	$0, %r9d, %xmm0, %xmm0
	vpinsrd	$1, (%r8), %xmm0, %xmm0
	vpinsrq	$1, 4(%r8), %xmm0, %xmm0
	vmovdqu	%xmm0, 1136(%rsp)
	vbroadcasti128	g_sigma(%rip), %ymm0
	vbroadcasti128	(%rcx), %ymm1
	vbroadcasti128	16(%rcx), %ymm2
	vbroadcasti128	1136(%rsp), %ymm3
	vpaddd	g_p1(%rip), %ymm3, %ymm3
	cmpl	$128, %edx
	jnbe	Lchacha20_avx2$3
	vmovdqu	%ymm0, %ymm4
	vmovdqu	%ymm1, %ymm5
	vmovdqu	%ymm2, %ymm6
	vmovdqu	%ymm3, %ymm7
	vmovdqu	g_r16(%rip), %ymm8
	vmovdqu	g_r8(%rip), %ymm9
	movq	$0, %rax
	jmp 	Lchacha20_avx2$17
Lchacha20_avx2$18:
	vpaddd	%ymm5, %ymm4, %ymm4
	vpxor	%ymm4, %ymm7, %ymm7
	vpshufb	%ymm8, %ymm7, %ymm7
	vpaddd	%ymm7, %ymm6, %ymm6
	vpxor	%ymm6, %ymm5, %ymm5
	vpslld	$12, %ymm5, %ymm10
	vpsrld	$20, %ymm5, %ymm5
	vpxor	%ymm10, %ymm5, %ymm5
	vpaddd	%ymm5, %ymm4, %ymm4
	vpxor	%ymm4, %ymm7, %ymm7
	vpshufb	%ymm9, %ymm7, %ymm7
	vpaddd	%ymm7, %ymm6, %ymm6
	vpxor	%ymm6, %ymm5, %ymm5
	vpslld	$7, %ymm5, %ymm10
	vpsrld	$25, %ymm5, %ymm5
	vpxor	%ymm10, %ymm5, %ymm5
	vpshufd	$57, %ymm5, %ymm5
	vpshufd	$78, %ymm6, %ymm6
	vpshufd	$-109, %ymm7, %ymm7
	vpaddd	%ymm5, %ymm4, %ymm4
	vpxor	%ymm4, %ymm7, %ymm7
	vpshufb	%ymm8, %ymm7, %ymm7
	vpaddd	%ymm7, %ymm6, %ymm6
	vpxor	%ymm6, %ymm5, %ymm5
	vpslld	$12, %ymm5, %ymm10
	vpsrld	$20, %ymm5, %ymm5
	vpxor	%ymm10, %ymm5, %ymm5
	vpaddd	%ymm5, %ymm4, %ymm4
	vpxor	%ymm4, %ymm7, %ymm7
	vpshufb	%ymm9, %ymm7, %ymm7
	vpaddd	%ymm7, %ymm6, %ymm6
	vpxor	%ymm6, %ymm5, %ymm5
	vpslld	$7, %ymm5, %ymm10
	vpsrld	$25, %ymm5, %ymm5
	vpxor	%ymm10, %ymm5, %ymm5
	vpshufd	$-109, %ymm5, %ymm5
	vpshufd	$78, %ymm6, %ymm6
	vpshufd	$57, %ymm7, %ymm7
	incq	%rax
Lchacha20_avx2$17:
	cmpq	$10, %rax
	jb  	Lchacha20_avx2$18
	vpaddd	%ymm0, %ymm4, %ymm0
	vpaddd	%ymm1, %ymm5, %ymm1
	vpaddd	%ymm2, %ymm6, %ymm2
	vpaddd	%ymm3, %ymm7, %ymm3
	vperm2i128	$32, %ymm1, %ymm0, %ymm4
	vperm2i128	$32, %ymm3, %ymm2, %ymm5
	vperm2i128	$49, %ymm1, %ymm0, %ymm0
	vperm2i128	$49, %ymm3, %ymm2, %ymm1
	vmovdqu	%ymm4, %ymm2
	vmovdqu	%ymm5, %ymm3
	cmpl	$64, %edx
	jb  	Lchacha20_avx2$16
	vpxor	(%rsi), %ymm2, %ymm2
	vpxor	32(%rsi), %ymm3, %ymm3
	vmovdqu	%ymm2, (%rdi)
	vmovdqu	%ymm3, 32(%rdi)
	addq	$64, %rdi
	addq	$64, %rsi
	subl	$64, %edx
	vmovdqu	%ymm0, %ymm2
	vmovdqu	%ymm1, %ymm3
Lchacha20_avx2$16:
	vmovdqu	%ymm2, %ymm0
	cmpl	$32, %edx
	jb  	Lchacha20_avx2$15
	vpxor	(%rsi), %ymm0, %ymm0
	vmovdqu	%ymm0, (%rdi)
	addq	$32, %rdi
	addq	$32, %rsi
	subl	$32, %edx
	vmovdqu	%ymm3, %ymm0
Lchacha20_avx2$15:
	vextracti128	$0, %ymm0, %xmm1
	cmpl	$16, %edx
	jb  	Lchacha20_avx2$14
	vpxor	(%rsi), %xmm1, %xmm1
	vmovdqu	%xmm1, (%rdi)
	addq	$16, %rdi
	addq	$16, %rsi
	subl	$16, %edx
	vextracti128	$1, %ymm0, %xmm1
Lchacha20_avx2$14:
	vmovdqu	%xmm1, 1120(%rsp)
	movq	$0, %rax
	jmp 	Lchacha20_avx2$12
Lchacha20_avx2$13:
	movb	(%rsi,%rax), %cl
	xorb	1120(%rsp,%rax), %cl
	movb	%cl, (%rdi,%rax)
	incq	%rax
Lchacha20_avx2$12:
	cmpl	%edx, %eax
	jb  	Lchacha20_avx2$13
	jmp 	Lchacha20_avx2$4
Lchacha20_avx2$3:
	vmovdqu	%ymm0, %ymm4
	vmovdqu	%ymm1, %ymm5
	vmovdqu	%ymm2, %ymm6
	vmovdqu	%ymm3, %ymm7
	vmovdqu	%ymm0, %ymm8
	vmovdqu	%ymm1, %ymm9
	vmovdqu	%ymm2, %ymm10
	vmovdqu	%ymm3, %ymm11
	vpaddd	g_p2(%rip), %ymm11, %ymm11
	vmovdqu	g_r16(%rip), %ymm12
	vmovdqu	g_r8(%rip), %ymm13
	movq	$0, %rax
	jmp 	Lchacha20_avx2$10
Lchacha20_avx2$11:
	vpaddd	%ymm5, %ymm4, %ymm4
	vpxor	%ymm4, %ymm7, %ymm7
	vpshufb	%ymm12, %ymm7, %ymm7
	vpaddd	%ymm7, %ymm6, %ymm6
	vpxor	%ymm6, %ymm5, %ymm5
	vpslld	$12, %ymm5, %ymm14
	vpsrld	$20, %ymm5, %ymm5
	vpxor	%ymm14, %ymm5, %ymm5
	vpaddd	%ymm5, %ymm4, %ymm4
	vpxor	%ymm4, %ymm7, %ymm7
	vpshufb	%ymm13, %ymm7, %ymm7
	vpaddd	%ymm7, %ymm6, %ymm6
	vpxor	%ymm6, %ymm5, %ymm5
	vpslld	$7, %ymm5, %ymm14
	vpsrld	$25, %ymm5, %ymm5
	vpxor	%ymm14, %ymm5, %ymm5
	vpaddd	%ymm9, %ymm8, %ymm8
	vpxor	%ymm8, %ymm11, %ymm11
	vpshufb	%ymm12, %ymm11, %ymm11
	vpaddd	%ymm11, %ymm10, %ymm10
	vpxor	%ymm10, %ymm9, %ymm9
	vpslld	$12, %ymm9, %ymm14
	vpsrld	$20, %ymm9, %ymm9
	vpxor	%ymm14, %ymm9, %ymm9
	vpaddd	%ymm9, %ymm8, %ymm8
	vpxor	%ymm8, %ymm11, %ymm11
	vpshufb	%ymm13, %ymm11, %ymm11
	vpaddd	%ymm11, %ymm10, %ymm10
	vpxor	%ymm10, %ymm9, %ymm9
	vpslld	$7, %ymm9, %ymm14
	vpsrld	$25, %ymm9, %ymm9
	vpxor	%ymm14, %ymm9, %ymm9
	vpshufd	$57, %ymm5, %ymm5
	vpshufd	$78, %ymm6, %ymm6
	vpshufd	$-109, %ymm7, %ymm7
	vpshufd	$57, %ymm9, %ymm9
	vpshufd	$78, %ymm10, %ymm10
	vpshufd	$-109, %ymm11, %ymm11
	vpaddd	%ymm5, %ymm4, %ymm4
	vpxor	%ymm4, %ymm7, %ymm7
	vpshufb	%ymm12, %ymm7, %ymm7
	vpaddd	%ymm7, %ymm6, %ymm6
	vpxor	%ymm6, %ymm5, %ymm5
	vpslld	$12, %ymm5, %ymm14
	vpsrld	$20, %ymm5, %ymm5
	vpxor	%ymm14, %ymm5, %ymm5
	vpaddd	%ymm5, %ymm4, %ymm4
	vpxor	%ymm4, %ymm7, %ymm7
	vpshufb	%ymm13, %ymm7, %ymm7
	vpaddd	%ymm7, %ymm6, %ymm6
	vpxor	%ymm6, %ymm5, %ymm5
	vpslld	$7, %ymm5, %ymm14
	vpsrld	$25, %ymm5, %ymm5
	vpxor	%ymm14, %ymm5, %ymm5
	vpaddd	%ymm9, %ymm8, %ymm8
	vpxor	%ymm8, %ymm11, %ymm11
	vpshufb	%ymm12, %ymm11, %ymm11
	vpaddd	%ymm11, %ymm10, %ymm10
	vpxor	%ymm10, %ymm9, %ymm9
	vpslld	$12, %ymm9, %ymm14
	vpsrld	$20, %ymm9, %ymm9
	vpxor	%ymm14, %ymm9, %ymm9
	vpaddd	%ymm9, %ymm8, %ymm8
	vpxor	%ymm8, %ymm11, %ymm11
	vpshufb	%ymm13, %ymm11, %ymm11
	vpaddd	%ymm11, %ymm10, %ymm10
	vpxor	%ymm10, %ymm9, %ymm9
	vpslld	$7, %ymm9, %ymm14
	vpsrld	$25, %ymm9, %ymm9
	vpxor	%ymm14, %ymm9, %ymm9
	vpshufd	$-109, %ymm5, %ymm5
	vpshufd	$78, %ymm6, %ymm6
	vpshufd	$57, %ymm7, %ymm7
	vpshufd	$-109, %ymm9, %ymm9
	vpshufd	$78, %ymm10, %ymm10
	vpshufd	$57, %ymm11, %ymm11
	incq	%rax
Lchacha20_avx2$10:
	cmpq	$10, %rax
	jb  	Lchacha20_avx2$11
	vpaddd	%ymm0, %ymm4, %ymm4
	vpaddd	%ymm1, %ymm5, %ymm5
	vpaddd	%ymm2, %ymm6, %ymm6
	vpaddd	%ymm3, %ymm7, %ymm7
	vpaddd	%ymm0, %ymm8, %ymm0
	vpaddd	%ymm1, %ymm9, %ymm1
	vpaddd	%ymm2, %ymm10, %ymm2
	vpaddd	%ymm3, %ymm11, %ymm3
	vpaddd	g_p2(%rip), %ymm3, %ymm3
	vperm2i128	$32, %ymm5, %ymm4, %ymm8
	vperm2i128	$32, %ymm7, %ymm6, %ymm9
	vperm2i128	$49, %ymm5, %ymm4, %ymm4
	vperm2i128	$49, %ymm7, %ymm6, %ymm5
	vperm2i128	$32, %ymm1, %ymm0, %ymm6
	vperm2i128	$32, %ymm3, %ymm2, %ymm7
	vperm2i128	$49, %ymm1, %ymm0, %ymm0
	vperm2i128	$49, %ymm3, %ymm2, %ymm1
	vpxor	(%rsi), %ymm8, %ymm2
	vpxor	32(%rsi), %ymm9, %ymm3
	vpxor	64(%rsi), %ymm4, %ymm4
	vpxor	96(%rsi), %ymm5, %ymm5
	vmovdqu	%ymm2, (%rdi)
	vmovdqu	%ymm3, 32(%rdi)
	vmovdqu	%ymm4, 64(%rdi)
	vmovdqu	%ymm5, 96(%rdi)
	addq	$128, %rdi
	addq	$128, %rsi
	subl	$128, %edx
	vmovdqu	%ymm6, %ymm2
	vmovdqu	%ymm7, %ymm3
	cmpl	$64, %edx
	jb  	Lchacha20_avx2$9
	vpxor	(%rsi), %ymm2, %ymm2
	vpxor	32(%rsi), %ymm3, %ymm3
	vmovdqu	%ymm2, (%rdi)
	vmovdqu	%ymm3, 32(%rdi)
	addq	$64, %rdi
	addq	$64, %rsi
	subl	$64, %edx
	vmovdqu	%ymm0, %ymm2
	vmovdqu	%ymm1, %ymm3
Lchacha20_avx2$9:
	vmovdqu	%ymm2, %ymm0
	cmpl	$32, %edx
	jb  	Lchacha20_avx2$8
	vpxor	(%rsi), %ymm0, %ymm0
	vmovdqu	%ymm0, (%rdi)
	addq	$32, %rdi
	addq	$32, %rsi
	subl	$32, %edx
	vmovdqu	%ymm3, %ymm0
Lchacha20_avx2$8:
	vextracti128	$0, %ymm0, %xmm1
	cmpl	$16, %edx
	jb  	Lchacha20_avx2$7
	vpxor	(%rsi), %xmm1, %xmm1
	vmovdqu	%xmm1, (%rdi)
	addq	$16, %rdi
	addq	$16, %rsi
	subl	$16, %edx
	vextracti128	$1, %ymm0, %xmm1
Lchacha20_avx2$7:
	vmovdqu	%xmm1, 1120(%rsp)
	movq	$0, %rax
	jmp 	Lchacha20_avx2$5
Lchacha20_avx2$6:
	movb	(%rsi,%rax), %cl
	xorb	1120(%rsp,%rax), %cl
	movb	%cl, (%rdi,%rax)
	incq	%rax
Lchacha20_avx2$5:
	cmpl	%edx, %eax
	jb  	Lchacha20_avx2$6
Lchacha20_avx2$4:
Lchacha20_avx2$2:
	movq	%r11, %rsp
	ret 
	.data
	.globl	_g_p0
	.globl	g_p0
	.p2align	4
_g_p0:
g_p0:
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.globl	_g_sigma3
	.globl	g_sigma3
	.p2align	2
_g_sigma3:
g_sigma3:
	.long	1797285236
	.globl	_g_sigma2
	.globl	g_sigma2
	.p2align	2
_g_sigma2:
g_sigma2:
	.long	2036477234
	.globl	_g_sigma1
	.globl	g_sigma1
	.p2align	2
_g_sigma1:
g_sigma1:
	.long	857760878
	.globl	_g_sigma0
	.globl	g_sigma0
	.p2align	2
_g_sigma0:
g_sigma0:
	.long	1634760805
	.globl	_g_sigma
	.globl	g_sigma
	.p2align	4
_g_sigma:
g_sigma:
	.byte	101
	.byte	120
	.byte	112
	.byte	97
	.byte	110
	.byte	100
	.byte	32
	.byte	51
	.byte	50
	.byte	45
	.byte	98
	.byte	121
	.byte	116
	.byte	101
	.byte	32
	.byte	107
	.globl	_g_p2
	.globl	g_p2
	.p2align	5
_g_p2:
g_p2:
	.byte	2
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	2
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.globl	_g_p1
	.globl	g_p1
	.p2align	5
_g_p1:
g_p1:
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	1
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.globl	_g_cnt_inc
	.globl	g_cnt_inc
	.p2align	5
_g_cnt_inc:
g_cnt_inc:
	.byte	8
	.byte	0
	.byte	0
	.byte	0
	.byte	8
	.byte	0
	.byte	0
	.byte	0
	.byte	8
	.byte	0
	.byte	0
	.byte	0
	.byte	8
	.byte	0
	.byte	0
	.byte	0
	.byte	8
	.byte	0
	.byte	0
	.byte	0
	.byte	8
	.byte	0
	.byte	0
	.byte	0
	.byte	8
	.byte	0
	.byte	0
	.byte	0
	.byte	8
	.byte	0
	.byte	0
	.byte	0
	.globl	_g_cnt
	.globl	g_cnt
	.p2align	5
_g_cnt:
g_cnt:
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	1
	.byte	0
	.byte	0
	.byte	0
	.byte	2
	.byte	0
	.byte	0
	.byte	0
	.byte	3
	.byte	0
	.byte	0
	.byte	0
	.byte	4
	.byte	0
	.byte	0
	.byte	0
	.byte	5
	.byte	0
	.byte	0
	.byte	0
	.byte	6
	.byte	0
	.byte	0
	.byte	0
	.byte	7
	.byte	0
	.byte	0
	.byte	0
	.globl	_g_r8
	.globl	g_r8
	.p2align	5
_g_r8:
g_r8:
	.byte	3
	.byte	0
	.byte	1
	.byte	2
	.byte	7
	.byte	4
	.byte	5
	.byte	6
	.byte	11
	.byte	8
	.byte	9
	.byte	10
	.byte	15
	.byte	12
	.byte	13
	.byte	14
	.byte	3
	.byte	0
	.byte	1
	.byte	2
	.byte	7
	.byte	4
	.byte	5
	.byte	6
	.byte	11
	.byte	8
	.byte	9
	.byte	10
	.byte	15
	.byte	12
	.byte	13
	.byte	14
	.globl	_g_r16
	.globl	g_r16
	.p2align	5
_g_r16:
g_r16:
	.byte	2
	.byte	3
	.byte	0
	.byte	1
	.byte	6
	.byte	7
	.byte	4
	.byte	5
	.byte	10
	.byte	11
	.byte	8
	.byte	9
	.byte	14
	.byte	15
	.byte	12
	.byte	13
	.byte	2
	.byte	3
	.byte	0
	.byte	1
	.byte	6
	.byte	7
	.byte	4
	.byte	5
	.byte	10
	.byte	11
	.byte	8
	.byte	9
	.byte	14
	.byte	15
	.byte	12
	.byte	13
