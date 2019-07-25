	.text
	.p2align	5
	.globl	_chacha20_avx
	.globl	chacha20_avx
_chacha20_avx:
chacha20_avx:
	pushq	%rbp
#
	pushq	%r15
#
	subq	$564,	%rsp
#
	movq	%rsp,	%r15
	andq	$-32,	%rsp
#
	cmpl	$129, %edx
	jb  	Lchacha20_avx$1
	vmovdqu	g_r16(%rip), %xmm0
	vmovdqu	g_r8(%rip), %xmm1
	vmovdqu	%xmm0, 256(%rsp)
	vmovdqu	%xmm1, 272(%rsp)
	movl	%r9d, 560(%rsp)
	vmovdqu	g_sigma0(%rip), %xmm0
	vmovdqu	g_sigma1(%rip), %xmm1
	vmovdqu	g_sigma2(%rip), %xmm2
	vmovdqu	g_sigma3(%rip), %xmm3
	vpbroadcastd	(%rcx), %xmm4
	vpbroadcastd	4(%rcx), %xmm5
	vpbroadcastd	8(%rcx), %xmm6
	vpbroadcastd	12(%rcx), %xmm7
	vpbroadcastd	16(%rcx), %xmm8
	vpbroadcastd	20(%rcx), %xmm9
	vpbroadcastd	24(%rcx), %xmm10
	vpbroadcastd	28(%rcx), %xmm11
	vpbroadcastd	560(%rsp), %xmm12
	vpaddd	g_cnt(%rip), %xmm12, %xmm12
	vpbroadcastd	(%r8), %xmm13
	vpbroadcastd	4(%r8), %xmm14
	vpbroadcastd	8(%r8), %xmm15
	vmovdqu	%xmm0, 304(%rsp)
	vmovdqu	%xmm1, 320(%rsp)
	vmovdqu	%xmm2, 336(%rsp)
	vmovdqu	%xmm3, 352(%rsp)
	vmovdqu	%xmm4, 368(%rsp)
	vmovdqu	%xmm5, 384(%rsp)
	vmovdqu	%xmm6, 400(%rsp)
	vmovdqu	%xmm7, 416(%rsp)
	vmovdqu	%xmm8, 432(%rsp)
	vmovdqu	%xmm9, 448(%rsp)
	vmovdqu	%xmm10, 464(%rsp)
	vmovdqu	%xmm11, 480(%rsp)
	vmovdqu	%xmm12, 496(%rsp)
	vmovdqu	%xmm13, 512(%rsp)
	vmovdqu	%xmm14, 528(%rsp)
	vmovdqu	%xmm15, 544(%rsp)
	jmp 	Lchacha20_avx$28
Lchacha20_avx$29:
	vmovdqu	304(%rsp), %xmm0
	vmovdqu	320(%rsp), %xmm1
	vmovdqu	336(%rsp), %xmm2
	vmovdqu	352(%rsp), %xmm3
	vmovdqu	368(%rsp), %xmm4
	vmovdqu	384(%rsp), %xmm5
	vmovdqu	400(%rsp), %xmm6
	vmovdqu	416(%rsp), %xmm7
	vmovdqu	432(%rsp), %xmm8
	vmovdqu	448(%rsp), %xmm9
	vmovdqu	464(%rsp), %xmm10
	vmovdqu	480(%rsp), %xmm11
	vmovdqu	496(%rsp), %xmm12
	vmovdqu	512(%rsp), %xmm13
	vmovdqu	528(%rsp), %xmm14
	vmovdqu	544(%rsp), %xmm15
	vmovdqu	%xmm15, 288(%rsp)
	movq	$10, %rax
	.p2align	5
Lchacha20_avx$30:
	vpaddd	%xmm4, %xmm0, %xmm0
	vpaddd	%xmm6, %xmm2, %xmm2
	vpxor	%xmm0, %xmm12, %xmm12
	vpxor	%xmm2, %xmm14, %xmm14
	vpshufb	256(%rsp), %xmm12, %xmm12
	vpshufb	256(%rsp), %xmm14, %xmm14
	vpaddd	%xmm12, %xmm8, %xmm8
	vpaddd	%xmm14, %xmm10, %xmm10
	vpxor	%xmm8, %xmm4, %xmm4
	vpxor	%xmm10, %xmm6, %xmm6
	vpslld	$12, %xmm4, %xmm15
	vpsrld	$20, %xmm4, %xmm4
	vpxor	%xmm15, %xmm4, %xmm4
	vpslld	$12, %xmm6, %xmm15
	vpsrld	$20, %xmm6, %xmm6
	vpxor	%xmm15, %xmm6, %xmm6
	vpaddd	%xmm4, %xmm0, %xmm0
	vpaddd	%xmm6, %xmm2, %xmm2
	vpxor	%xmm0, %xmm12, %xmm12
	vpxor	%xmm2, %xmm14, %xmm14
	vpshufb	272(%rsp), %xmm12, %xmm12
	vpshufb	272(%rsp), %xmm14, %xmm14
	vpaddd	%xmm12, %xmm8, %xmm8
	vpaddd	%xmm14, %xmm10, %xmm10
	vpxor	%xmm8, %xmm4, %xmm4
	vpxor	%xmm10, %xmm6, %xmm6
	vpslld	$7, %xmm4, %xmm15
	vpsrld	$25, %xmm4, %xmm4
	vpxor	%xmm15, %xmm4, %xmm4
	vpslld	$7, %xmm6, %xmm15
	vpsrld	$25, %xmm6, %xmm6
	vpxor	%xmm15, %xmm6, %xmm6
	vmovdqu	288(%rsp), %xmm15
	vmovdqu	%xmm14, 288(%rsp)
	vpaddd	%xmm5, %xmm1, %xmm1
	vpaddd	%xmm7, %xmm3, %xmm3
	vpxor	%xmm1, %xmm13, %xmm13
	vpxor	%xmm3, %xmm15, %xmm14
	vpshufb	256(%rsp), %xmm13, %xmm13
	vpshufb	256(%rsp), %xmm14, %xmm14
	vpaddd	%xmm13, %xmm9, %xmm9
	vpaddd	%xmm14, %xmm11, %xmm11
	vpxor	%xmm9, %xmm5, %xmm5
	vpxor	%xmm11, %xmm7, %xmm7
	vpslld	$12, %xmm5, %xmm15
	vpsrld	$20, %xmm5, %xmm5
	vpxor	%xmm15, %xmm5, %xmm5
	vpslld	$12, %xmm7, %xmm15
	vpsrld	$20, %xmm7, %xmm7
	vpxor	%xmm15, %xmm7, %xmm7
	vpaddd	%xmm5, %xmm1, %xmm1
	vpaddd	%xmm7, %xmm3, %xmm3
	vpxor	%xmm1, %xmm13, %xmm13
	vpxor	%xmm3, %xmm14, %xmm14
	vpshufb	272(%rsp), %xmm13, %xmm13
	vpshufb	272(%rsp), %xmm14, %xmm14
	vpaddd	%xmm13, %xmm9, %xmm9
	vpaddd	%xmm14, %xmm11, %xmm11
	vpxor	%xmm9, %xmm5, %xmm5
	vpxor	%xmm11, %xmm7, %xmm7
	vpslld	$7, %xmm5, %xmm15
	vpsrld	$25, %xmm5, %xmm5
	vpxor	%xmm15, %xmm5, %xmm5
	vpslld	$7, %xmm7, %xmm15
	vpsrld	$25, %xmm7, %xmm7
	vpxor	%xmm15, %xmm7, %xmm7
	vpaddd	%xmm6, %xmm1, %xmm1
	vpaddd	%xmm5, %xmm0, %xmm0
	vpxor	%xmm1, %xmm12, %xmm12
	vpxor	%xmm0, %xmm14, %xmm14
	vpshufb	256(%rsp), %xmm12, %xmm12
	vpshufb	256(%rsp), %xmm14, %xmm14
	vpaddd	%xmm12, %xmm11, %xmm11
	vpaddd	%xmm14, %xmm10, %xmm10
	vpxor	%xmm11, %xmm6, %xmm6
	vpxor	%xmm10, %xmm5, %xmm5
	vpslld	$12, %xmm6, %xmm15
	vpsrld	$20, %xmm6, %xmm6
	vpxor	%xmm15, %xmm6, %xmm6
	vpslld	$12, %xmm5, %xmm15
	vpsrld	$20, %xmm5, %xmm5
	vpxor	%xmm15, %xmm5, %xmm5
	vpaddd	%xmm6, %xmm1, %xmm1
	vpaddd	%xmm5, %xmm0, %xmm0
	vpxor	%xmm1, %xmm12, %xmm12
	vpxor	%xmm0, %xmm14, %xmm14
	vpshufb	272(%rsp), %xmm12, %xmm12
	vpshufb	272(%rsp), %xmm14, %xmm14
	vpaddd	%xmm12, %xmm11, %xmm11
	vpaddd	%xmm14, %xmm10, %xmm10
	vpxor	%xmm11, %xmm6, %xmm6
	vpxor	%xmm10, %xmm5, %xmm5
	vpslld	$7, %xmm6, %xmm15
	vpsrld	$25, %xmm6, %xmm6
	vpxor	%xmm15, %xmm6, %xmm6
	vpslld	$7, %xmm5, %xmm15
	vpsrld	$25, %xmm5, %xmm5
	vpxor	%xmm15, %xmm5, %xmm5
	vmovdqu	288(%rsp), %xmm15
	vmovdqu	%xmm14, 288(%rsp)
	vpaddd	%xmm7, %xmm2, %xmm2
	vpaddd	%xmm4, %xmm3, %xmm3
	vpxor	%xmm2, %xmm13, %xmm13
	vpxor	%xmm3, %xmm15, %xmm14
	vpshufb	256(%rsp), %xmm13, %xmm13
	vpshufb	256(%rsp), %xmm14, %xmm14
	vpaddd	%xmm13, %xmm8, %xmm8
	vpaddd	%xmm14, %xmm9, %xmm9
	vpxor	%xmm8, %xmm7, %xmm7
	vpxor	%xmm9, %xmm4, %xmm4
	vpslld	$12, %xmm7, %xmm15
	vpsrld	$20, %xmm7, %xmm7
	vpxor	%xmm15, %xmm7, %xmm7
	vpslld	$12, %xmm4, %xmm15
	vpsrld	$20, %xmm4, %xmm4
	vpxor	%xmm15, %xmm4, %xmm4
	vpaddd	%xmm7, %xmm2, %xmm2
	vpaddd	%xmm4, %xmm3, %xmm3
	vpxor	%xmm2, %xmm13, %xmm13
	vpxor	%xmm3, %xmm14, %xmm14
	vpshufb	272(%rsp), %xmm13, %xmm13
	vpshufb	272(%rsp), %xmm14, %xmm14
	vpaddd	%xmm13, %xmm8, %xmm8
	vpaddd	%xmm14, %xmm9, %xmm9
	vpxor	%xmm8, %xmm7, %xmm7
	vpxor	%xmm9, %xmm4, %xmm4
	vpslld	$7, %xmm7, %xmm15
	vpsrld	$25, %xmm7, %xmm7
	vpxor	%xmm15, %xmm7, %xmm7
	vpslld	$7, %xmm4, %xmm15
	vpsrld	$25, %xmm4, %xmm4
	vpxor	%xmm15, %xmm4, %xmm4
	decq	%rax
	jne 	Lchacha20_avx$30
	vmovdqu	288(%rsp), %xmm15
	vpaddd	304(%rsp), %xmm0, %xmm0
	vpaddd	320(%rsp), %xmm1, %xmm1
	vpaddd	336(%rsp), %xmm2, %xmm2
	vpaddd	352(%rsp), %xmm3, %xmm3
	vpaddd	368(%rsp), %xmm4, %xmm4
	vpaddd	384(%rsp), %xmm5, %xmm5
	vpaddd	400(%rsp), %xmm6, %xmm6
	vpaddd	416(%rsp), %xmm7, %xmm7
	vpaddd	432(%rsp), %xmm8, %xmm8
	vpaddd	448(%rsp), %xmm9, %xmm9
	vpaddd	464(%rsp), %xmm10, %xmm10
	vpaddd	480(%rsp), %xmm11, %xmm11
	vpaddd	496(%rsp), %xmm12, %xmm12
	vpaddd	512(%rsp), %xmm13, %xmm13
	vpaddd	528(%rsp), %xmm14, %xmm14
	vpaddd	544(%rsp), %xmm15, %xmm15
	vmovdqu	%xmm8, 128(%rsp)
	vmovdqu	%xmm9, 144(%rsp)
	vmovdqu	%xmm10, 160(%rsp)
	vmovdqu	%xmm11, 176(%rsp)
	vmovdqu	%xmm12, 192(%rsp)
	vmovdqu	%xmm13, 208(%rsp)
	vmovdqu	%xmm14, 224(%rsp)
	vmovdqu	%xmm15, 240(%rsp)
	vmovdqu	%xmm0, %xmm0
	vmovdqu	%xmm1, %xmm1
	vmovdqu	%xmm2, %xmm2
	vmovdqu	%xmm3, %xmm3
	vmovdqu	%xmm4, %xmm4
	vmovdqu	%xmm5, %xmm5
	vmovdqu	%xmm6, %xmm6
	vmovdqu	%xmm7, %xmm7
	vpunpckldq	%xmm1, %xmm0, %xmm8
	vpunpckhdq	%xmm1, %xmm0, %xmm0
	vpunpckldq	%xmm3, %xmm2, %xmm1
	vpunpckhdq	%xmm3, %xmm2, %xmm2
	vpunpckldq	%xmm5, %xmm4, %xmm3
	vpunpckhdq	%xmm5, %xmm4, %xmm4
	vpunpckldq	%xmm7, %xmm6, %xmm5
	vpunpckhdq	%xmm7, %xmm6, %xmm6
	vpunpcklqdq	%xmm1, %xmm8, %xmm7
	vpunpcklqdq	%xmm5, %xmm3, %xmm9
	vpunpckhqdq	%xmm1, %xmm8, %xmm1
	vpunpckhqdq	%xmm5, %xmm3, %xmm3
	vpunpcklqdq	%xmm2, %xmm0, %xmm5
	vpunpcklqdq	%xmm6, %xmm4, %xmm8
	vpunpckhqdq	%xmm2, %xmm0, %xmm0
	vpunpckhqdq	%xmm6, %xmm4, %xmm2
	vpxor	(%rsi), %xmm7, %xmm4
	vpxor	16(%rsi), %xmm9, %xmm6
	vpxor	64(%rsi), %xmm1, %xmm1
	vpxor	80(%rsi), %xmm3, %xmm3
	vpxor	128(%rsi), %xmm5, %xmm5
	vpxor	144(%rsi), %xmm8, %xmm7
	vpxor	192(%rsi), %xmm0, %xmm0
	vpxor	208(%rsi), %xmm2, %xmm2
	vmovdqu	%xmm4, (%rdi)
	vmovdqu	%xmm6, 16(%rdi)
	vmovdqu	%xmm1, 64(%rdi)
	vmovdqu	%xmm3, 80(%rdi)
	vmovdqu	%xmm5, 128(%rdi)
	vmovdqu	%xmm7, 144(%rdi)
	vmovdqu	%xmm0, 192(%rdi)
	vmovdqu	%xmm2, 208(%rdi)
	vmovdqu	128(%rsp), %xmm0
	vmovdqu	160(%rsp), %xmm1
	vmovdqu	192(%rsp), %xmm2
	vmovdqu	224(%rsp), %xmm3
	vpunpckldq	144(%rsp), %xmm0, %xmm4
	vpunpckhdq	144(%rsp), %xmm0, %xmm0
	vpunpckldq	176(%rsp), %xmm1, %xmm5
	vpunpckhdq	176(%rsp), %xmm1, %xmm1
	vpunpckldq	208(%rsp), %xmm2, %xmm6
	vpunpckhdq	208(%rsp), %xmm2, %xmm2
	vpunpckldq	240(%rsp), %xmm3, %xmm7
	vpunpckhdq	240(%rsp), %xmm3, %xmm3
	vpunpcklqdq	%xmm5, %xmm4, %xmm8
	vpunpcklqdq	%xmm7, %xmm6, %xmm9
	vpunpckhqdq	%xmm5, %xmm4, %xmm4
	vpunpckhqdq	%xmm7, %xmm6, %xmm5
	vpunpcklqdq	%xmm1, %xmm0, %xmm6
	vpunpcklqdq	%xmm3, %xmm2, %xmm7
	vpunpckhqdq	%xmm1, %xmm0, %xmm0
	vpunpckhqdq	%xmm3, %xmm2, %xmm1
	vpxor	32(%rsi), %xmm8, %xmm2
	vpxor	48(%rsi), %xmm9, %xmm3
	vpxor	96(%rsi), %xmm4, %xmm4
	vpxor	112(%rsi), %xmm5, %xmm5
	vpxor	160(%rsi), %xmm6, %xmm6
	vpxor	176(%rsi), %xmm7, %xmm7
	vpxor	224(%rsi), %xmm0, %xmm0
	vpxor	240(%rsi), %xmm1, %xmm1
	vmovdqu	%xmm2, 32(%rdi)
	vmovdqu	%xmm3, 48(%rdi)
	vmovdqu	%xmm4, 96(%rdi)
	vmovdqu	%xmm5, 112(%rdi)
	vmovdqu	%xmm6, 160(%rdi)
	vmovdqu	%xmm7, 176(%rdi)
	vmovdqu	%xmm0, 224(%rdi)
	vmovdqu	%xmm1, 240(%rdi)
	addq	$256, %rdi
	addq	$256, %rsi
	subl	$256, %edx
	vmovdqu	g_cnt_inc(%rip), %xmm0
	vpaddd	496(%rsp), %xmm0, %xmm0
	vmovdqu	%xmm0, 496(%rsp)
Lchacha20_avx$28:
	cmpl	$256, %edx
	jnb 	Lchacha20_avx$29
	cmpl	$0, %edx
	jbe 	Lchacha20_avx$19
	vmovdqu	304(%rsp), %xmm0
	vmovdqu	320(%rsp), %xmm1
	vmovdqu	336(%rsp), %xmm2
	vmovdqu	352(%rsp), %xmm3
	vmovdqu	368(%rsp), %xmm4
	vmovdqu	384(%rsp), %xmm5
	vmovdqu	400(%rsp), %xmm6
	vmovdqu	416(%rsp), %xmm7
	vmovdqu	432(%rsp), %xmm8
	vmovdqu	448(%rsp), %xmm9
	vmovdqu	464(%rsp), %xmm10
	vmovdqu	480(%rsp), %xmm11
	vmovdqu	496(%rsp), %xmm12
	vmovdqu	512(%rsp), %xmm13
	vmovdqu	528(%rsp), %xmm14
	vmovdqu	544(%rsp), %xmm15
	vmovdqu	%xmm15, 288(%rsp)
	movq	$10, %rax
	.p2align	5
Lchacha20_avx$27:
	vpaddd	%xmm4, %xmm0, %xmm0
	vpaddd	%xmm6, %xmm2, %xmm2
	vpxor	%xmm0, %xmm12, %xmm12
	vpxor	%xmm2, %xmm14, %xmm14
	vpshufb	256(%rsp), %xmm12, %xmm12
	vpshufb	256(%rsp), %xmm14, %xmm14
	vpaddd	%xmm12, %xmm8, %xmm8
	vpaddd	%xmm14, %xmm10, %xmm10
	vpxor	%xmm8, %xmm4, %xmm4
	vpxor	%xmm10, %xmm6, %xmm6
	vpslld	$12, %xmm4, %xmm15
	vpsrld	$20, %xmm4, %xmm4
	vpxor	%xmm15, %xmm4, %xmm4
	vpslld	$12, %xmm6, %xmm15
	vpsrld	$20, %xmm6, %xmm6
	vpxor	%xmm15, %xmm6, %xmm6
	vpaddd	%xmm4, %xmm0, %xmm0
	vpaddd	%xmm6, %xmm2, %xmm2
	vpxor	%xmm0, %xmm12, %xmm12
	vpxor	%xmm2, %xmm14, %xmm14
	vpshufb	272(%rsp), %xmm12, %xmm12
	vpshufb	272(%rsp), %xmm14, %xmm14
	vpaddd	%xmm12, %xmm8, %xmm8
	vpaddd	%xmm14, %xmm10, %xmm10
	vpxor	%xmm8, %xmm4, %xmm4
	vpxor	%xmm10, %xmm6, %xmm6
	vpslld	$7, %xmm4, %xmm15
	vpsrld	$25, %xmm4, %xmm4
	vpxor	%xmm15, %xmm4, %xmm4
	vpslld	$7, %xmm6, %xmm15
	vpsrld	$25, %xmm6, %xmm6
	vpxor	%xmm15, %xmm6, %xmm6
	vmovdqu	288(%rsp), %xmm15
	vmovdqu	%xmm14, 288(%rsp)
	vpaddd	%xmm5, %xmm1, %xmm1
	vpaddd	%xmm7, %xmm3, %xmm3
	vpxor	%xmm1, %xmm13, %xmm13
	vpxor	%xmm3, %xmm15, %xmm14
	vpshufb	256(%rsp), %xmm13, %xmm13
	vpshufb	256(%rsp), %xmm14, %xmm14
	vpaddd	%xmm13, %xmm9, %xmm9
	vpaddd	%xmm14, %xmm11, %xmm11
	vpxor	%xmm9, %xmm5, %xmm5
	vpxor	%xmm11, %xmm7, %xmm7
	vpslld	$12, %xmm5, %xmm15
	vpsrld	$20, %xmm5, %xmm5
	vpxor	%xmm15, %xmm5, %xmm5
	vpslld	$12, %xmm7, %xmm15
	vpsrld	$20, %xmm7, %xmm7
	vpxor	%xmm15, %xmm7, %xmm7
	vpaddd	%xmm5, %xmm1, %xmm1
	vpaddd	%xmm7, %xmm3, %xmm3
	vpxor	%xmm1, %xmm13, %xmm13
	vpxor	%xmm3, %xmm14, %xmm14
	vpshufb	272(%rsp), %xmm13, %xmm13
	vpshufb	272(%rsp), %xmm14, %xmm14
	vpaddd	%xmm13, %xmm9, %xmm9
	vpaddd	%xmm14, %xmm11, %xmm11
	vpxor	%xmm9, %xmm5, %xmm5
	vpxor	%xmm11, %xmm7, %xmm7
	vpslld	$7, %xmm5, %xmm15
	vpsrld	$25, %xmm5, %xmm5
	vpxor	%xmm15, %xmm5, %xmm5
	vpslld	$7, %xmm7, %xmm15
	vpsrld	$25, %xmm7, %xmm7
	vpxor	%xmm15, %xmm7, %xmm7
	vpaddd	%xmm6, %xmm1, %xmm1
	vpaddd	%xmm5, %xmm0, %xmm0
	vpxor	%xmm1, %xmm12, %xmm12
	vpxor	%xmm0, %xmm14, %xmm14
	vpshufb	256(%rsp), %xmm12, %xmm12
	vpshufb	256(%rsp), %xmm14, %xmm14
	vpaddd	%xmm12, %xmm11, %xmm11
	vpaddd	%xmm14, %xmm10, %xmm10
	vpxor	%xmm11, %xmm6, %xmm6
	vpxor	%xmm10, %xmm5, %xmm5
	vpslld	$12, %xmm6, %xmm15
	vpsrld	$20, %xmm6, %xmm6
	vpxor	%xmm15, %xmm6, %xmm6
	vpslld	$12, %xmm5, %xmm15
	vpsrld	$20, %xmm5, %xmm5
	vpxor	%xmm15, %xmm5, %xmm5
	vpaddd	%xmm6, %xmm1, %xmm1
	vpaddd	%xmm5, %xmm0, %xmm0
	vpxor	%xmm1, %xmm12, %xmm12
	vpxor	%xmm0, %xmm14, %xmm14
	vpshufb	272(%rsp), %xmm12, %xmm12
	vpshufb	272(%rsp), %xmm14, %xmm14
	vpaddd	%xmm12, %xmm11, %xmm11
	vpaddd	%xmm14, %xmm10, %xmm10
	vpxor	%xmm11, %xmm6, %xmm6
	vpxor	%xmm10, %xmm5, %xmm5
	vpslld	$7, %xmm6, %xmm15
	vpsrld	$25, %xmm6, %xmm6
	vpxor	%xmm15, %xmm6, %xmm6
	vpslld	$7, %xmm5, %xmm15
	vpsrld	$25, %xmm5, %xmm5
	vpxor	%xmm15, %xmm5, %xmm5
	vmovdqu	288(%rsp), %xmm15
	vmovdqu	%xmm14, 288(%rsp)
	vpaddd	%xmm7, %xmm2, %xmm2
	vpaddd	%xmm4, %xmm3, %xmm3
	vpxor	%xmm2, %xmm13, %xmm13
	vpxor	%xmm3, %xmm15, %xmm14
	vpshufb	256(%rsp), %xmm13, %xmm13
	vpshufb	256(%rsp), %xmm14, %xmm14
	vpaddd	%xmm13, %xmm8, %xmm8
	vpaddd	%xmm14, %xmm9, %xmm9
	vpxor	%xmm8, %xmm7, %xmm7
	vpxor	%xmm9, %xmm4, %xmm4
	vpslld	$12, %xmm7, %xmm15
	vpsrld	$20, %xmm7, %xmm7
	vpxor	%xmm15, %xmm7, %xmm7
	vpslld	$12, %xmm4, %xmm15
	vpsrld	$20, %xmm4, %xmm4
	vpxor	%xmm15, %xmm4, %xmm4
	vpaddd	%xmm7, %xmm2, %xmm2
	vpaddd	%xmm4, %xmm3, %xmm3
	vpxor	%xmm2, %xmm13, %xmm13
	vpxor	%xmm3, %xmm14, %xmm14
	vpshufb	272(%rsp), %xmm13, %xmm13
	vpshufb	272(%rsp), %xmm14, %xmm14
	vpaddd	%xmm13, %xmm8, %xmm8
	vpaddd	%xmm14, %xmm9, %xmm9
	vpxor	%xmm8, %xmm7, %xmm7
	vpxor	%xmm9, %xmm4, %xmm4
	vpslld	$7, %xmm7, %xmm15
	vpsrld	$25, %xmm7, %xmm7
	vpxor	%xmm15, %xmm7, %xmm7
	vpslld	$7, %xmm4, %xmm15
	vpsrld	$25, %xmm4, %xmm4
	vpxor	%xmm15, %xmm4, %xmm4
	decq	%rax
	jne 	Lchacha20_avx$27
	vmovdqu	288(%rsp), %xmm15
	vpaddd	304(%rsp), %xmm0, %xmm0
	vpaddd	320(%rsp), %xmm1, %xmm1
	vpaddd	336(%rsp), %xmm2, %xmm2
	vpaddd	352(%rsp), %xmm3, %xmm3
	vpaddd	368(%rsp), %xmm4, %xmm4
	vpaddd	384(%rsp), %xmm5, %xmm5
	vpaddd	400(%rsp), %xmm6, %xmm6
	vpaddd	416(%rsp), %xmm7, %xmm7
	vpaddd	432(%rsp), %xmm8, %xmm8
	vpaddd	448(%rsp), %xmm9, %xmm9
	vpaddd	464(%rsp), %xmm10, %xmm10
	vpaddd	480(%rsp), %xmm11, %xmm11
	vpaddd	496(%rsp), %xmm12, %xmm12
	vpaddd	512(%rsp), %xmm13, %xmm13
	vpaddd	528(%rsp), %xmm14, %xmm14
	vpaddd	544(%rsp), %xmm15, %xmm15
	vmovdqu	%xmm8, 128(%rsp)
	vmovdqu	%xmm9, 144(%rsp)
	vmovdqu	%xmm10, 160(%rsp)
	vmovdqu	%xmm11, 176(%rsp)
	vmovdqu	%xmm12, 192(%rsp)
	vmovdqu	%xmm13, 208(%rsp)
	vmovdqu	%xmm14, 224(%rsp)
	vmovdqu	%xmm15, 240(%rsp)
	vmovdqu	%xmm0, %xmm0
	vmovdqu	%xmm1, %xmm1
	vmovdqu	%xmm2, %xmm2
	vmovdqu	%xmm3, %xmm3
	vmovdqu	%xmm4, %xmm4
	vmovdqu	%xmm5, %xmm5
	vmovdqu	%xmm6, %xmm6
	vmovdqu	%xmm7, %xmm7
	vpunpckldq	%xmm1, %xmm0, %xmm8
	vpunpckhdq	%xmm1, %xmm0, %xmm0
	vpunpckldq	%xmm3, %xmm2, %xmm1
	vpunpckhdq	%xmm3, %xmm2, %xmm2
	vpunpckldq	%xmm5, %xmm4, %xmm3
	vpunpckhdq	%xmm5, %xmm4, %xmm4
	vpunpckldq	%xmm7, %xmm6, %xmm5
	vpunpckhdq	%xmm7, %xmm6, %xmm6
	vpunpcklqdq	%xmm1, %xmm8, %xmm7
	vpunpcklqdq	%xmm5, %xmm3, %xmm9
	vpunpckhqdq	%xmm1, %xmm8, %xmm1
	vpunpckhqdq	%xmm5, %xmm3, %xmm3
	vpunpcklqdq	%xmm2, %xmm0, %xmm5
	vpunpcklqdq	%xmm6, %xmm4, %xmm8
	vpunpckhqdq	%xmm2, %xmm0, %xmm0
	vpunpckhqdq	%xmm6, %xmm4, %xmm2
	vmovdqu	%xmm7, (%rsp)
	vmovdqu	%xmm9, 16(%rsp)
	vmovdqu	%xmm1, 32(%rsp)
	vmovdqu	%xmm3, 48(%rsp)
	vmovdqu	%xmm5, 64(%rsp)
	vmovdqu	%xmm8, 80(%rsp)
	vmovdqu	%xmm0, 96(%rsp)
	vmovdqu	%xmm2, 112(%rsp)
	vmovdqu	128(%rsp), %xmm0
	vmovdqu	160(%rsp), %xmm1
	vmovdqu	192(%rsp), %xmm2
	vmovdqu	224(%rsp), %xmm3
	vpunpckldq	144(%rsp), %xmm0, %xmm4
	vpunpckhdq	144(%rsp), %xmm0, %xmm0
	vpunpckldq	176(%rsp), %xmm1, %xmm5
	vpunpckhdq	176(%rsp), %xmm1, %xmm1
	vpunpckldq	208(%rsp), %xmm2, %xmm6
	vpunpckhdq	208(%rsp), %xmm2, %xmm2
	vpunpckldq	240(%rsp), %xmm3, %xmm7
	vpunpckhdq	240(%rsp), %xmm3, %xmm3
	vpunpcklqdq	%xmm5, %xmm4, %xmm8
	vpunpcklqdq	%xmm7, %xmm6, %xmm9
	vpunpckhqdq	%xmm5, %xmm4, %xmm4
	vpunpckhqdq	%xmm7, %xmm6, %xmm5
	vpunpcklqdq	%xmm1, %xmm0, %xmm6
	vpunpcklqdq	%xmm3, %xmm2, %xmm7
	vpunpckhqdq	%xmm1, %xmm0, %xmm0
	vpunpckhqdq	%xmm3, %xmm2, %xmm1
	vmovdqu	(%rsp), %xmm2
	vmovdqu	16(%rsp), %xmm3
	vmovdqu	%xmm8, %xmm13
	vmovdqu	%xmm9, %xmm12
	vmovdqu	32(%rsp), %xmm8
	vmovdqu	48(%rsp), %xmm9
	vmovdqu	%xmm4, %xmm10
	vmovdqu	%xmm5, %xmm11
	cmpl	$128, %edx
	jb  	Lchacha20_avx$26
	vpxor	(%rsi), %xmm2, %xmm2
	vpxor	16(%rsi), %xmm3, %xmm3
	vpxor	32(%rsi), %xmm13, %xmm4
	vpxor	48(%rsi), %xmm12, %xmm5
	vpxor	64(%rsi), %xmm8, %xmm8
	vpxor	80(%rsi), %xmm9, %xmm9
	vpxor	96(%rsi), %xmm10, %xmm10
	vpxor	112(%rsi), %xmm11, %xmm11
	vmovdqu	%xmm2, (%rdi)
	vmovdqu	%xmm3, 16(%rdi)
	vmovdqu	%xmm4, 32(%rdi)
	vmovdqu	%xmm5, 48(%rdi)
	vmovdqu	%xmm8, 64(%rdi)
	vmovdqu	%xmm9, 80(%rdi)
	vmovdqu	%xmm10, 96(%rdi)
	vmovdqu	%xmm11, 112(%rdi)
	addq	$128, %rdi
	addq	$128, %rsi
	subl	$128, %edx
	vmovdqu	64(%rsp), %xmm2
	vmovdqu	80(%rsp), %xmm3
	vmovdqu	%xmm6, %xmm13
	vmovdqu	%xmm7, %xmm12
	vmovdqu	96(%rsp), %xmm8
	vmovdqu	112(%rsp), %xmm9
	vmovdqu	%xmm0, %xmm10
	vmovdqu	%xmm1, %xmm11
Lchacha20_avx$26:
	vmovdqu	%xmm2, %xmm0
	vmovdqu	%xmm3, %xmm1
	vmovdqu	%xmm13, %xmm2
	vmovdqu	%xmm12, %xmm3
	cmpl	$64, %edx
	jb  	Lchacha20_avx$25
	vpxor	(%rsi), %xmm0, %xmm0
	vpxor	16(%rsi), %xmm1, %xmm1
	vpxor	32(%rsi), %xmm2, %xmm2
	vpxor	48(%rsi), %xmm3, %xmm3
	vmovdqu	%xmm0, (%rdi)
	vmovdqu	%xmm1, 16(%rdi)
	vmovdqu	%xmm2, 32(%rdi)
	vmovdqu	%xmm3, 48(%rdi)
	addq	$64, %rdi
	addq	$64, %rsi
	subl	$64, %edx
	vmovdqu	%xmm8, %xmm0
	vmovdqu	%xmm9, %xmm1
	vmovdqu	%xmm10, %xmm2
	vmovdqu	%xmm11, %xmm3
Lchacha20_avx$25:
	vmovdqu	%xmm0, %xmm0
	vmovdqu	%xmm1, %xmm1
	cmpl	$32, %edx
	jb  	Lchacha20_avx$24
	vpxor	(%rsi), %xmm0, %xmm0
	vpxor	16(%rsi), %xmm1, %xmm1
	vmovdqu	%xmm0, (%rdi)
	vmovdqu	%xmm1, 16(%rdi)
	addq	$32, %rdi
	addq	$32, %rsi
	subl	$32, %edx
	vmovdqu	%xmm2, %xmm0
	vmovdqu	%xmm3, %xmm1
Lchacha20_avx$24:
	vmovdqu	%xmm0, %xmm0
	cmpl	$16, %edx
	jb  	Lchacha20_avx$23
	vpxor	(%rsi), %xmm0, %xmm0
	vmovdqu	%xmm0, (%rdi)
	addq	$16, %rdi
	addq	$16, %rsi
	subl	$16, %edx
	vmovdqu	%xmm1, %xmm0
Lchacha20_avx$23:
	vpextrq	$0, %xmm0, %rax
	cmpl	$8, %edx
	jb  	Lchacha20_avx$22
	xorq	(%rsi), %rax
	movq	%rax, (%rdi)
	addq	$8, %rdi
	addq	$8, %rsi
	subl	$8, %edx
	vpextrq	$1, %xmm0, %rax
Lchacha20_avx$22:
	jmp 	Lchacha20_avx$20
Lchacha20_avx$21:
	movb	%al, %cl
	xorb	(%rsi), %cl
	movb	%cl, (%rdi)
	shrq	$8, %rax
	incq	%rdi
	incq	%rsi
	decl	%edx
Lchacha20_avx$20:
	cmpl	$0, %edx
	jnbe	Lchacha20_avx$21
Lchacha20_avx$19:
	jmp 	Lchacha20_avx$2
Lchacha20_avx$1:
	vmovdqu	g_sigma(%rip), %xmm0
	vmovdqu	(%rcx), %xmm1
	vmovdqu	16(%rcx), %xmm2
	vmovdqu	g_p0(%rip), %xmm3
	vpinsrd	$0, %r9d, %xmm3, %xmm3
	vpinsrd	$1, (%r8), %xmm3, %xmm3
	vpinsrq	$1, 4(%r8), %xmm3, %xmm3
	cmpl	$64, %edx
	jnbe	Lchacha20_avx$3
	vmovdqu	%xmm0, %xmm4
	vmovdqu	%xmm1, %xmm5
	vmovdqu	%xmm2, %xmm6
	vmovdqu	%xmm3, %xmm7
	vmovdqu	g_r16(%rip), %xmm8
	vmovdqu	g_r8(%rip), %xmm9
	movq	$0, %rax
	jmp 	Lchacha20_avx$17
Lchacha20_avx$18:
	vpaddd	%xmm5, %xmm4, %xmm4
	vpxor	%xmm4, %xmm7, %xmm7
	vpshufb	%xmm8, %xmm7, %xmm7
	vpaddd	%xmm7, %xmm6, %xmm6
	vpxor	%xmm6, %xmm5, %xmm5
	vpslld	$12, %xmm5, %xmm10
	vpsrld	$20, %xmm5, %xmm5
	vpxor	%xmm10, %xmm5, %xmm5
	vpaddd	%xmm5, %xmm4, %xmm4
	vpxor	%xmm4, %xmm7, %xmm7
	vpshufb	%xmm9, %xmm7, %xmm7
	vpaddd	%xmm7, %xmm6, %xmm6
	vpxor	%xmm6, %xmm5, %xmm5
	vpslld	$7, %xmm5, %xmm10
	vpsrld	$25, %xmm5, %xmm5
	vpxor	%xmm10, %xmm5, %xmm5
	vpshufd	$57, %xmm5, %xmm5
	vpshufd	$78, %xmm6, %xmm6
	vpshufd	$-109, %xmm7, %xmm7
	vpaddd	%xmm5, %xmm4, %xmm4
	vpxor	%xmm4, %xmm7, %xmm7
	vpshufb	%xmm8, %xmm7, %xmm7
	vpaddd	%xmm7, %xmm6, %xmm6
	vpxor	%xmm6, %xmm5, %xmm5
	vpslld	$12, %xmm5, %xmm10
	vpsrld	$20, %xmm5, %xmm5
	vpxor	%xmm10, %xmm5, %xmm5
	vpaddd	%xmm5, %xmm4, %xmm4
	vpxor	%xmm4, %xmm7, %xmm7
	vpshufb	%xmm9, %xmm7, %xmm7
	vpaddd	%xmm7, %xmm6, %xmm6
	vpxor	%xmm6, %xmm5, %xmm5
	vpslld	$7, %xmm5, %xmm10
	vpsrld	$25, %xmm5, %xmm5
	vpxor	%xmm10, %xmm5, %xmm5
	vpshufd	$-109, %xmm5, %xmm5
	vpshufd	$78, %xmm6, %xmm6
	vpshufd	$57, %xmm7, %xmm7
	incq	%rax
Lchacha20_avx$17:
	cmpq	$10, %rax
	jb  	Lchacha20_avx$18
	vpaddd	%xmm0, %xmm4, %xmm0
	vpaddd	%xmm1, %xmm5, %xmm1
	vpaddd	%xmm2, %xmm6, %xmm2
	vpaddd	%xmm3, %xmm7, %xmm3
	vmovdqu	%xmm0, %xmm0
	vmovdqu	%xmm1, %xmm1
	cmpl	$32, %edx
	jb  	Lchacha20_avx$16
	vpxor	(%rsi), %xmm0, %xmm0
	vpxor	16(%rsi), %xmm1, %xmm1
	vmovdqu	%xmm0, (%rdi)
	vmovdqu	%xmm1, 16(%rdi)
	addq	$32, %rdi
	addq	$32, %rsi
	subl	$32, %edx
	vmovdqu	%xmm2, %xmm0
	vmovdqu	%xmm3, %xmm1
Lchacha20_avx$16:
	vmovdqu	%xmm0, %xmm0
	cmpl	$16, %edx
	jb  	Lchacha20_avx$15
	vpxor	(%rsi), %xmm0, %xmm0
	vmovdqu	%xmm0, (%rdi)
	addq	$16, %rdi
	addq	$16, %rsi
	subl	$16, %edx
	vmovdqu	%xmm1, %xmm0
Lchacha20_avx$15:
	vpextrq	$0, %xmm0, %rax
	cmpl	$8, %edx
	jb  	Lchacha20_avx$14
	xorq	(%rsi), %rax
	movq	%rax, (%rdi)
	addq	$8, %rdi
	addq	$8, %rsi
	subl	$8, %edx
	vpextrq	$1, %xmm0, %rax
Lchacha20_avx$14:
	jmp 	Lchacha20_avx$12
Lchacha20_avx$13:
	movb	%al, %cl
	xorb	(%rsi), %cl
	movb	%cl, (%rdi)
	shrq	$8, %rax
	incq	%rdi
	incq	%rsi
	decl	%edx
Lchacha20_avx$12:
	cmpl	$0, %edx
	jnbe	Lchacha20_avx$13
	jmp 	Lchacha20_avx$4
Lchacha20_avx$3:
	vmovdqu	%xmm0, %xmm4
	vmovdqu	%xmm1, %xmm5
	vmovdqu	%xmm2, %xmm6
	vmovdqu	%xmm3, %xmm7
	vmovdqu	%xmm0, %xmm8
	vmovdqu	%xmm1, %xmm9
	vmovdqu	%xmm2, %xmm10
	vmovdqu	%xmm3, %xmm11
	vpaddd	g_p1(%rip), %xmm11, %xmm11
	vmovdqu	g_r16(%rip), %xmm12
	vmovdqu	g_r8(%rip), %xmm13
	movq	$0, %rax
	jmp 	Lchacha20_avx$10
Lchacha20_avx$11:
	vpaddd	%xmm5, %xmm4, %xmm4
	vpaddd	%xmm9, %xmm8, %xmm8
	vpxor	%xmm4, %xmm7, %xmm7
	vpxor	%xmm8, %xmm11, %xmm11
	vpshufb	%xmm12, %xmm7, %xmm7
	vpshufb	%xmm12, %xmm11, %xmm11
	vpaddd	%xmm7, %xmm6, %xmm6
	vpaddd	%xmm11, %xmm10, %xmm10
	vpxor	%xmm6, %xmm5, %xmm5
	vpslld	$12, %xmm5, %xmm14
	vpsrld	$20, %xmm5, %xmm5
	vpxor	%xmm10, %xmm9, %xmm9
	vpxor	%xmm14, %xmm5, %xmm5
	vpslld	$12, %xmm9, %xmm14
	vpsrld	$20, %xmm9, %xmm9
	vpxor	%xmm14, %xmm9, %xmm9
	vpaddd	%xmm5, %xmm4, %xmm4
	vpaddd	%xmm9, %xmm8, %xmm8
	vpxor	%xmm4, %xmm7, %xmm7
	vpxor	%xmm8, %xmm11, %xmm11
	vpshufb	%xmm13, %xmm7, %xmm7
	vpshufb	%xmm13, %xmm11, %xmm11
	vpaddd	%xmm7, %xmm6, %xmm6
	vpaddd	%xmm11, %xmm10, %xmm10
	vpxor	%xmm6, %xmm5, %xmm5
	vpslld	$7, %xmm5, %xmm14
	vpsrld	$25, %xmm5, %xmm5
	vpxor	%xmm10, %xmm9, %xmm9
	vpxor	%xmm14, %xmm5, %xmm5
	vpslld	$7, %xmm9, %xmm14
	vpsrld	$25, %xmm9, %xmm9
	vpxor	%xmm14, %xmm9, %xmm9
	vpshufd	$57, %xmm5, %xmm5
	vpshufd	$78, %xmm6, %xmm6
	vpshufd	$-109, %xmm7, %xmm7
	vpshufd	$57, %xmm9, %xmm9
	vpshufd	$78, %xmm10, %xmm10
	vpshufd	$-109, %xmm11, %xmm11
	vpaddd	%xmm5, %xmm4, %xmm4
	vpaddd	%xmm9, %xmm8, %xmm8
	vpxor	%xmm4, %xmm7, %xmm7
	vpxor	%xmm8, %xmm11, %xmm11
	vpshufb	%xmm12, %xmm7, %xmm7
	vpshufb	%xmm12, %xmm11, %xmm11
	vpaddd	%xmm7, %xmm6, %xmm6
	vpaddd	%xmm11, %xmm10, %xmm10
	vpxor	%xmm6, %xmm5, %xmm5
	vpslld	$12, %xmm5, %xmm14
	vpsrld	$20, %xmm5, %xmm5
	vpxor	%xmm10, %xmm9, %xmm9
	vpxor	%xmm14, %xmm5, %xmm5
	vpslld	$12, %xmm9, %xmm14
	vpsrld	$20, %xmm9, %xmm9
	vpxor	%xmm14, %xmm9, %xmm9
	vpaddd	%xmm5, %xmm4, %xmm4
	vpaddd	%xmm9, %xmm8, %xmm8
	vpxor	%xmm4, %xmm7, %xmm7
	vpxor	%xmm8, %xmm11, %xmm11
	vpshufb	%xmm13, %xmm7, %xmm7
	vpshufb	%xmm13, %xmm11, %xmm11
	vpaddd	%xmm7, %xmm6, %xmm6
	vpaddd	%xmm11, %xmm10, %xmm10
	vpxor	%xmm6, %xmm5, %xmm5
	vpslld	$7, %xmm5, %xmm14
	vpsrld	$25, %xmm5, %xmm5
	vpxor	%xmm10, %xmm9, %xmm9
	vpxor	%xmm14, %xmm5, %xmm5
	vpslld	$7, %xmm9, %xmm14
	vpsrld	$25, %xmm9, %xmm9
	vpxor	%xmm14, %xmm9, %xmm9
	vpshufd	$-109, %xmm5, %xmm5
	vpshufd	$78, %xmm6, %xmm6
	vpshufd	$57, %xmm7, %xmm7
	vpshufd	$-109, %xmm9, %xmm9
	vpshufd	$78, %xmm10, %xmm10
	vpshufd	$57, %xmm11, %xmm11
	incq	%rax
Lchacha20_avx$10:
	cmpq	$10, %rax
	jb  	Lchacha20_avx$11
	vpaddd	%xmm0, %xmm4, %xmm4
	vpaddd	%xmm1, %xmm5, %xmm5
	vpaddd	%xmm2, %xmm6, %xmm6
	vpaddd	%xmm3, %xmm7, %xmm7
	vpaddd	%xmm0, %xmm8, %xmm0
	vpaddd	%xmm1, %xmm9, %xmm1
	vpaddd	%xmm2, %xmm10, %xmm2
	vpaddd	%xmm3, %xmm11, %xmm3
	vpaddd	g_p1(%rip), %xmm3, %xmm3
	vpxor	(%rsi), %xmm4, %xmm4
	vpxor	16(%rsi), %xmm5, %xmm5
	vpxor	32(%rsi), %xmm6, %xmm6
	vpxor	48(%rsi), %xmm7, %xmm7
	vmovdqu	%xmm4, (%rdi)
	vmovdqu	%xmm5, 16(%rdi)
	vmovdqu	%xmm6, 32(%rdi)
	vmovdqu	%xmm7, 48(%rdi)
	addq	$64, %rdi
	addq	$64, %rsi
	subl	$64, %edx
	vmovdqu	%xmm0, %xmm0
	vmovdqu	%xmm1, %xmm1
	cmpl	$32, %edx
	jb  	Lchacha20_avx$9
	vpxor	(%rsi), %xmm0, %xmm0
	vpxor	16(%rsi), %xmm1, %xmm1
	vmovdqu	%xmm0, (%rdi)
	vmovdqu	%xmm1, 16(%rdi)
	addq	$32, %rdi
	addq	$32, %rsi
	subl	$32, %edx
	vmovdqu	%xmm2, %xmm0
	vmovdqu	%xmm3, %xmm1
Lchacha20_avx$9:
	vmovdqu	%xmm0, %xmm0
	cmpl	$16, %edx
	jb  	Lchacha20_avx$8
	vpxor	(%rsi), %xmm0, %xmm0
	vmovdqu	%xmm0, (%rdi)
	addq	$16, %rdi
	addq	$16, %rsi
	subl	$16, %edx
	vmovdqu	%xmm1, %xmm0
Lchacha20_avx$8:
	vpextrq	$0, %xmm0, %rax
	cmpl	$8, %edx
	jb  	Lchacha20_avx$7
	xorq	(%rsi), %rax
	movq	%rax, (%rdi)
	addq	$8, %rdi
	addq	$8, %rsi
	subl	$8, %edx
	vpextrq	$1, %xmm0, %rax
Lchacha20_avx$7:
	jmp 	Lchacha20_avx$5
Lchacha20_avx$6:
	movb	%al, %cl
	xorb	(%rsi), %cl
	movb	%cl, (%rdi)
	shrq	$8, %rax
	incq	%rdi
	incq	%rsi
	decl	%edx
Lchacha20_avx$5:
	cmpl	$0, %edx
	jnbe	Lchacha20_avx$6
Lchacha20_avx$4:
Lchacha20_avx$2:
#
	movq	%r15,	%rsp
#
	addq	$564, %rsp
#
	popq	%r15
#
	popq	%rbp
	ret 
	.data
	.globl	_g_sigma3
	.globl	g_sigma3
	.p2align	4
_g_sigma3:
g_sigma3:
	.byte	116
	.byte	101
	.byte	32
	.byte	107
	.byte	116
	.byte	101
	.byte	32
	.byte	107
	.byte	116
	.byte	101
	.byte	32
	.byte	107
	.byte	116
	.byte	101
	.byte	32
	.byte	107
	.globl	_g_sigma2
	.globl	g_sigma2
	.p2align	4
_g_sigma2:
g_sigma2:
	.byte	50
	.byte	45
	.byte	98
	.byte	121
	.byte	50
	.byte	45
	.byte	98
	.byte	121
	.byte	50
	.byte	45
	.byte	98
	.byte	121
	.byte	50
	.byte	45
	.byte	98
	.byte	121
	.globl	_g_sigma1
	.globl	g_sigma1
	.p2align	4
_g_sigma1:
g_sigma1:
	.byte	110
	.byte	100
	.byte	32
	.byte	51
	.byte	110
	.byte	100
	.byte	32
	.byte	51
	.byte	110
	.byte	100
	.byte	32
	.byte	51
	.byte	110
	.byte	100
	.byte	32
	.byte	51
	.globl	_g_sigma0
	.globl	g_sigma0
	.p2align	4
_g_sigma0:
g_sigma0:
	.byte	101
	.byte	120
	.byte	112
	.byte	97
	.byte	101
	.byte	120
	.byte	112
	.byte	97
	.byte	101
	.byte	120
	.byte	112
	.byte	97
	.byte	101
	.byte	120
	.byte	112
	.byte	97
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
	.globl	_g_p1
	.globl	g_p1
	.p2align	4
_g_p1:
g_p1:
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
	.globl	_g_cnt_inc
	.globl	g_cnt_inc
	.p2align	4
_g_cnt_inc:
g_cnt_inc:
	.byte	4
	.byte	0
	.byte	0
	.byte	0
	.byte	4
	.byte	0
	.byte	0
	.byte	0
	.byte	4
	.byte	0
	.byte	0
	.byte	0
	.byte	4
	.byte	0
	.byte	0
	.byte	0
	.globl	_g_cnt
	.globl	g_cnt
	.p2align	4
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
	.globl	_g_r8
	.globl	g_r8
	.p2align	4
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
	.globl	_g_r16
	.globl	g_r16
	.p2align	4
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
