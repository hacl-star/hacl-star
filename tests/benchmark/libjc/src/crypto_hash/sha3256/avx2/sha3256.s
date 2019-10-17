	.text
	.p2align	5
	.globl	_keccak_1600
	.globl	keccak_1600
_keccak_1600:
keccak_1600:
	pushq	%rbp
	pushq	%rbx
	pushq	%r12
	pushq	%r13
	pushq	%r14
	subq	$256, %rsp
	movb	(%r8), %al
	movq	8(%r8), %r8
	movq	(%r9), %r10
	movq	8(%r9), %r11
	movq	16(%r9), %rbp
	movq	24(%r9), %r9
	vpbroadcastq	g_zero(%rip), %ymm2
	vmovdqu	%ymm2, %ymm3
	vmovdqu	%ymm2, %ymm4
	vmovdqu	%ymm2, %ymm12
	vmovdqu	%ymm2, %ymm10
	vmovdqu	%ymm2, %ymm11
	vmovdqu	%ymm2, %ymm9
	jmp 	Lkeccak_1600$15
Lkeccak_1600$16:
	movq	40(%rdx), %rbx
	movq	80(%rdx), %r12
	movq	120(%rdx), %r13
	movq	%r12, 224(%rsp)
	movq	$0, 232(%rsp)
	movq	%rbx, 240(%rsp)
	movq	%r13, 248(%rsp)
	vpbroadcastq	(%rdx), %ymm0
	vmovdqu	8(%rdx), %ymm1
	vpxor	%ymm0, %ymm2, %ymm2
	vpxor	%ymm1, %ymm3, %ymm3
	vpxor	224(%rsp), %ymm4, %ymm4
	vmovdqu	48(%rdx), %ymm0
	vmovdqu	88(%rdx), %ymm1
	vpbroadcastq	128(%rdx), %ymm5
	vpblendd	$-61, %ymm0, %ymm1, %ymm6
	vpblendd	$60, %ymm0, %ymm1, %ymm0
	vpbroadcastq	s_zero(%rip), %ymm1
	vpblendd	$-16, %ymm1, %ymm6, %ymm7
	vpblendd	$-52, %ymm1, %ymm0, %ymm8
	vpblendd	$51, %ymm1, %ymm0, %ymm0
	vpxor	%ymm7, %ymm9, %ymm9
	vpxor	%ymm8, %ymm10, %ymm10
	vpblendd	$15, %ymm1, %ymm6, %ymm1
	vpblendd	$3, %ymm5, %ymm0, %ymm0
	vpxor	%ymm1, %ymm11, %ymm11
	vpxor	%ymm0, %ymm12, %ymm12
	leaq	(%rdx,%r8), %rdx
	subq	%r8, %rcx
	leaq	96(%r10), %rbx
	leaq	96(%r11), %r12
	movq	%rbp, %r13
	movl	$24, %r14d
	.p2align	5
Lkeccak_1600$17:
	vpshufd	$78, %ymm4, %ymm0
	vpxor	%ymm12, %ymm11, %ymm1
	vpxor	%ymm9, %ymm10, %ymm5
	vpxor	%ymm3, %ymm1, %ymm1
	vpxor	%ymm5, %ymm1, %ymm1
	vpermq	$-109, %ymm1, %ymm5
	vpxor	%ymm4, %ymm0, %ymm0
	vpermq	$78, %ymm0, %ymm6
	vpsrlq	$63, %ymm1, %ymm7
	vpaddq	%ymm1, %ymm1, %ymm1
	vpor	%ymm1, %ymm7, %ymm1
	vpermq	$57, %ymm1, %ymm7
	vpxor	%ymm5, %ymm1, %ymm1
	vpermq	$0, %ymm1, %ymm1
	vpxor	%ymm2, %ymm0, %ymm0
	vpxor	%ymm6, %ymm0, %ymm0
	vpsrlq	$63, %ymm0, %ymm6
	vpaddq	%ymm0, %ymm0, %ymm8
	vpor	%ymm6, %ymm8, %ymm6
	vpxor	%ymm1, %ymm4, %ymm4
	vpxor	%ymm1, %ymm2, %ymm1
	vpblendd	$-64, %ymm6, %ymm7, %ymm2
	vpblendd	$3, %ymm0, %ymm5, %ymm0
	vpxor	%ymm0, %ymm2, %ymm0
	vpsllvq	-96(%rbx), %ymm4, %ymm2
	vpsrlvq	-96(%r12), %ymm4, %ymm4
	vpor	%ymm2, %ymm4, %ymm2
	vpxor	%ymm0, %ymm12, %ymm4
	vpsllvq	-32(%rbx), %ymm4, %ymm5
	vpsrlvq	-32(%r12), %ymm4, %ymm4
	vpor	%ymm5, %ymm4, %ymm4
	vpxor	%ymm0, %ymm10, %ymm5
	vpsllvq	(%rbx), %ymm5, %ymm6
	vpsrlvq	(%r12), %ymm5, %ymm5
	vpor	%ymm6, %ymm5, %ymm5
	vpxor	%ymm0, %ymm11, %ymm6
	vpsllvq	32(%rbx), %ymm6, %ymm7
	vpsrlvq	32(%r12), %ymm6, %ymm6
	vpor	%ymm7, %ymm6, %ymm6
	vpxor	%ymm0, %ymm9, %ymm7
	vpermq	$-115, %ymm2, %ymm2
	vpermq	$-115, %ymm4, %ymm8
	vpsllvq	64(%rbx), %ymm7, %ymm4
	vpsrlvq	64(%r12), %ymm7, %ymm7
	vpor	%ymm4, %ymm7, %ymm7
	vpxor	%ymm0, %ymm3, %ymm0
	vpermq	$27, %ymm5, %ymm3
	vpermq	$114, %ymm6, %ymm5
	vpsllvq	-64(%rbx), %ymm0, %ymm4
	vpsrlvq	-64(%r12), %ymm0, %ymm0
	vpor	%ymm4, %ymm0, %ymm0
	vpsrldq	$8, %ymm7, %ymm4
	vpandn	%ymm4, %ymm7, %ymm6
	vpblendd	$12, %ymm5, %ymm0, %ymm4
	vpblendd	$12, %ymm0, %ymm8, %ymm9
	vpblendd	$12, %ymm8, %ymm2, %ymm10
	vpblendd	$12, %ymm2, %ymm0, %ymm11
	vpblendd	$48, %ymm8, %ymm4, %ymm4
	vpblendd	$48, %ymm3, %ymm9, %ymm9
	vpblendd	$48, %ymm0, %ymm10, %ymm10
	vpblendd	$48, %ymm5, %ymm11, %ymm11
	vpblendd	$-64, %ymm3, %ymm4, %ymm4
	vpblendd	$-64, %ymm5, %ymm9, %ymm9
	vpblendd	$-64, %ymm5, %ymm10, %ymm10
	vpblendd	$-64, %ymm8, %ymm11, %ymm11
	vpandn	%ymm9, %ymm4, %ymm4
	vpandn	%ymm11, %ymm10, %ymm9
	vpblendd	$12, %ymm0, %ymm3, %ymm10
	vpblendd	$12, %ymm3, %ymm2, %ymm11
	vpxor	%ymm2, %ymm4, %ymm12
	vpblendd	$48, %ymm2, %ymm10, %ymm4
	vpblendd	$48, %ymm8, %ymm11, %ymm10
	vpxor	%ymm3, %ymm9, %ymm9
	vpblendd	$-64, %ymm8, %ymm4, %ymm4
	vpblendd	$-64, %ymm0, %ymm10, %ymm10
	vpandn	%ymm10, %ymm4, %ymm4
	vpxor	%ymm5, %ymm4, %ymm10
	vpermq	$30, %ymm7, %ymm4
	vpblendd	$48, %ymm1, %ymm4, %ymm4
	vpermq	$57, %ymm7, %ymm11
	vpblendd	$-64, %ymm1, %ymm11, %ymm11
	vpandn	%ymm4, %ymm11, %ymm13
	vpblendd	$12, %ymm3, %ymm8, %ymm4
	vpblendd	$12, %ymm8, %ymm5, %ymm11
	vpblendd	$48, %ymm5, %ymm4, %ymm4
	vpblendd	$48, %ymm2, %ymm11, %ymm11
	vpblendd	$-64, %ymm2, %ymm4, %ymm4
	vpblendd	$-64, %ymm3, %ymm11, %ymm11
	vpandn	%ymm11, %ymm4, %ymm4
	vpxor	%ymm0, %ymm4, %ymm4
	vpermq	$0, %ymm6, %ymm6
	vpermq	$27, %ymm12, %ymm12
	vpermq	$-115, %ymm9, %ymm11
	vpermq	$114, %ymm10, %ymm9
	vpblendd	$12, %ymm2, %ymm5, %ymm10
	vpblendd	$12, %ymm5, %ymm3, %ymm5
	vpblendd	$48, %ymm3, %ymm10, %ymm3
	vpblendd	$48, %ymm0, %ymm5, %ymm5
	vpblendd	$-64, %ymm0, %ymm3, %ymm0
	vpblendd	$-64, %ymm2, %ymm5, %ymm2
	vpandn	%ymm2, %ymm0, %ymm0
	vpxor	%ymm6, %ymm1, %ymm1
	vpxor	%ymm7, %ymm13, %ymm3
	vpxor	%ymm8, %ymm0, %ymm10
	vpxor	(%r13), %ymm1, %ymm2
	leaq	32(%r13), %r13
	decl	%r14d
	jne 	Lkeccak_1600$17
Lkeccak_1600$15:
	cmpq	%r8, %rcx
	jnb 	Lkeccak_1600$16
	vpbroadcastq	g_zero(%rip), %ymm0
	vmovdqu	%ymm0, (%rsp)
	vmovdqu	%ymm0, 32(%rsp)
	vmovdqu	%ymm0, 64(%rsp)
	vmovdqu	%ymm0, 96(%rsp)
	vmovdqu	%ymm0, 128(%rsp)
	vmovdqu	%ymm0, 160(%rsp)
	vmovdqu	%ymm0, 192(%rsp)
	movq	%rcx, %rbx
	shrq	$3, %rbx
	movq	$0, %r12
	jmp 	Lkeccak_1600$13
Lkeccak_1600$14:
	movq	(%rdx,%r12,8), %r13
	movq	(%r9,%r12,8), %r14
	movq	%r13, (%rsp,%r14,8)
	leaq	1(%r12), %r12
Lkeccak_1600$13:
	cmpq	%rbx, %r12
	jb  	Lkeccak_1600$14
	movq	(%r9,%r12,8), %rbx
	shlq	$3, %rbx
	shlq	$3, %r12
	jmp 	Lkeccak_1600$11
Lkeccak_1600$12:
	movb	(%rdx,%r12), %r13b
	movb	%r13b, (%rsp,%rbx)
	leaq	1(%r12), %r12
	leaq	1(%rbx), %rbx
Lkeccak_1600$11:
	cmpq	%rcx, %r12
	jb  	Lkeccak_1600$12
	movb	%al, (%rsp,%rbx)
	movq	%r8, %rax
	leaq	-1(%rax), %rax
	shrq	$3, %rax
	movq	(%r9,%rax,8), %rax
	shlq	$3, %rax
	movq	%r8, %rcx
	leaq	-1(%rcx), %rcx
	andq	$7, %rcx
	leaq	(%rax,%rcx), %rax
	xorb	$-128, (%rsp,%rax)
	movq	(%rsp), %rax
	movq	%rax, 8(%rsp)
	movq	%rax, 16(%rsp)
	movq	%rax, 24(%rsp)
	vpxor	(%rsp), %ymm2, %ymm0
	vpxor	32(%rsp), %ymm3, %ymm1
	vpxor	64(%rsp), %ymm4, %ymm2
	vpxor	96(%rsp), %ymm12, %ymm3
	vpxor	128(%rsp), %ymm10, %ymm4
	vpxor	160(%rsp), %ymm11, %ymm5
	vpxor	192(%rsp), %ymm9, %ymm6
	jmp 	Lkeccak_1600$6
Lkeccak_1600$7:
	leaq	96(%r10), %rax
	leaq	96(%r11), %rcx
	movq	%rbp, %rdx
	movl	$24, %ebx
	.p2align	5
Lkeccak_1600$10:
	vpshufd	$78, %ymm2, %ymm7
	vpxor	%ymm3, %ymm5, %ymm8
	vpxor	%ymm6, %ymm4, %ymm9
	vpxor	%ymm1, %ymm8, %ymm8
	vpxor	%ymm9, %ymm8, %ymm8
	vpermq	$-109, %ymm8, %ymm9
	vpxor	%ymm2, %ymm7, %ymm7
	vpermq	$78, %ymm7, %ymm10
	vpsrlq	$63, %ymm8, %ymm11
	vpaddq	%ymm8, %ymm8, %ymm8
	vpor	%ymm8, %ymm11, %ymm8
	vpermq	$57, %ymm8, %ymm11
	vpxor	%ymm9, %ymm8, %ymm8
	vpermq	$0, %ymm8, %ymm8
	vpxor	%ymm0, %ymm7, %ymm7
	vpxor	%ymm10, %ymm7, %ymm7
	vpsrlq	$63, %ymm7, %ymm10
	vpaddq	%ymm7, %ymm7, %ymm12
	vpor	%ymm10, %ymm12, %ymm10
	vpxor	%ymm8, %ymm2, %ymm2
	vpxor	%ymm8, %ymm0, %ymm0
	vpblendd	$-64, %ymm10, %ymm11, %ymm8
	vpblendd	$3, %ymm7, %ymm9, %ymm7
	vpxor	%ymm7, %ymm8, %ymm7
	vpsllvq	-96(%rax), %ymm2, %ymm8
	vpsrlvq	-96(%rcx), %ymm2, %ymm2
	vpor	%ymm8, %ymm2, %ymm2
	vpxor	%ymm7, %ymm3, %ymm3
	vpsllvq	-32(%rax), %ymm3, %ymm8
	vpsrlvq	-32(%rcx), %ymm3, %ymm3
	vpor	%ymm8, %ymm3, %ymm3
	vpxor	%ymm7, %ymm4, %ymm4
	vpsllvq	(%rax), %ymm4, %ymm8
	vpsrlvq	(%rcx), %ymm4, %ymm4
	vpor	%ymm8, %ymm4, %ymm4
	vpxor	%ymm7, %ymm5, %ymm5
	vpsllvq	32(%rax), %ymm5, %ymm8
	vpsrlvq	32(%rcx), %ymm5, %ymm5
	vpor	%ymm8, %ymm5, %ymm5
	vpxor	%ymm7, %ymm6, %ymm6
	vpermq	$-115, %ymm2, %ymm8
	vpermq	$-115, %ymm3, %ymm9
	vpsllvq	64(%rax), %ymm6, %ymm2
	vpsrlvq	64(%rcx), %ymm6, %ymm3
	vpor	%ymm2, %ymm3, %ymm10
	vpxor	%ymm7, %ymm1, %ymm1
	vpermq	$27, %ymm4, %ymm4
	vpermq	$114, %ymm5, %ymm7
	vpsllvq	-64(%rax), %ymm1, %ymm2
	vpsrlvq	-64(%rcx), %ymm1, %ymm1
	vpor	%ymm2, %ymm1, %ymm1
	vpsrldq	$8, %ymm10, %ymm2
	vpandn	%ymm2, %ymm10, %ymm3
	vpblendd	$12, %ymm7, %ymm1, %ymm2
	vpblendd	$12, %ymm1, %ymm9, %ymm5
	vpblendd	$12, %ymm9, %ymm8, %ymm6
	vpblendd	$12, %ymm8, %ymm1, %ymm11
	vpblendd	$48, %ymm9, %ymm2, %ymm2
	vpblendd	$48, %ymm4, %ymm5, %ymm5
	vpblendd	$48, %ymm1, %ymm6, %ymm6
	vpblendd	$48, %ymm7, %ymm11, %ymm11
	vpblendd	$-64, %ymm4, %ymm2, %ymm2
	vpblendd	$-64, %ymm7, %ymm5, %ymm5
	vpblendd	$-64, %ymm7, %ymm6, %ymm6
	vpblendd	$-64, %ymm9, %ymm11, %ymm11
	vpandn	%ymm5, %ymm2, %ymm2
	vpandn	%ymm11, %ymm6, %ymm5
	vpblendd	$12, %ymm1, %ymm4, %ymm6
	vpblendd	$12, %ymm4, %ymm8, %ymm11
	vpxor	%ymm8, %ymm2, %ymm12
	vpblendd	$48, %ymm8, %ymm6, %ymm2
	vpblendd	$48, %ymm9, %ymm11, %ymm6
	vpxor	%ymm4, %ymm5, %ymm5
	vpblendd	$-64, %ymm9, %ymm2, %ymm2
	vpblendd	$-64, %ymm1, %ymm6, %ymm6
	vpandn	%ymm6, %ymm2, %ymm2
	vpxor	%ymm7, %ymm2, %ymm6
	vpermq	$30, %ymm10, %ymm2
	vpblendd	$48, %ymm0, %ymm2, %ymm2
	vpermq	$57, %ymm10, %ymm11
	vpblendd	$-64, %ymm0, %ymm11, %ymm11
	vpandn	%ymm2, %ymm11, %ymm11
	vpblendd	$12, %ymm4, %ymm9, %ymm2
	vpblendd	$12, %ymm9, %ymm7, %ymm13
	vpblendd	$48, %ymm7, %ymm2, %ymm2
	vpblendd	$48, %ymm8, %ymm13, %ymm13
	vpblendd	$-64, %ymm8, %ymm2, %ymm2
	vpblendd	$-64, %ymm4, %ymm13, %ymm13
	vpandn	%ymm13, %ymm2, %ymm2
	vpxor	%ymm1, %ymm2, %ymm2
	vpermq	$0, %ymm3, %ymm13
	vpermq	$27, %ymm12, %ymm3
	vpermq	$-115, %ymm5, %ymm5
	vpermq	$114, %ymm6, %ymm6
	vpblendd	$12, %ymm8, %ymm7, %ymm12
	vpblendd	$12, %ymm7, %ymm4, %ymm7
	vpblendd	$48, %ymm4, %ymm12, %ymm4
	vpblendd	$48, %ymm1, %ymm7, %ymm7
	vpblendd	$-64, %ymm1, %ymm4, %ymm1
	vpblendd	$-64, %ymm8, %ymm7, %ymm4
	vpandn	%ymm4, %ymm1, %ymm4
	vpxor	%ymm13, %ymm0, %ymm0
	vpxor	%ymm10, %ymm11, %ymm1
	vpxor	%ymm9, %ymm4, %ymm4
	vpxor	(%rdx), %ymm0, %ymm0
	leaq	32(%rdx), %rdx
	decl	%ebx
	jne 	Lkeccak_1600$10
	vmovdqu	%ymm0, (%rsp)
	vmovdqu	%ymm1, 32(%rsp)
	vmovdqu	%ymm2, 64(%rsp)
	vmovdqu	%ymm3, 96(%rsp)
	vmovdqu	%ymm4, 128(%rsp)
	vmovdqu	%ymm5, 160(%rsp)
	vmovdqu	%ymm6, 192(%rsp)
	movq	%r8, %rax
	shrq	$3, %rax
	movq	$0, %rcx
	jmp 	Lkeccak_1600$8
Lkeccak_1600$9:
	movq	(%r9,%rcx,8), %rdx
	movq	(%rsp,%rdx,8), %rdx
	movq	%rdx, (%rdi,%rcx,8)
	leaq	1(%rcx), %rcx
Lkeccak_1600$8:
	cmpq	%rax, %rcx
	jb  	Lkeccak_1600$9
	leaq	(%rdi,%r8), %rdi
	subq	%r8, %rsi
Lkeccak_1600$6:
	cmpq	%r8, %rsi
	jnbe	Lkeccak_1600$7
	leaq	96(%r10), %rax
	leaq	96(%r11), %rcx
	movl	$24, %edx
	.p2align	5
Lkeccak_1600$5:
	vpshufd	$78, %ymm2, %ymm7
	vpxor	%ymm3, %ymm5, %ymm8
	vpxor	%ymm6, %ymm4, %ymm9
	vpxor	%ymm1, %ymm8, %ymm8
	vpxor	%ymm9, %ymm8, %ymm8
	vpermq	$-109, %ymm8, %ymm9
	vpxor	%ymm2, %ymm7, %ymm7
	vpermq	$78, %ymm7, %ymm10
	vpsrlq	$63, %ymm8, %ymm11
	vpaddq	%ymm8, %ymm8, %ymm8
	vpor	%ymm8, %ymm11, %ymm8
	vpermq	$57, %ymm8, %ymm11
	vpxor	%ymm9, %ymm8, %ymm8
	vpermq	$0, %ymm8, %ymm8
	vpxor	%ymm0, %ymm7, %ymm7
	vpxor	%ymm10, %ymm7, %ymm7
	vpsrlq	$63, %ymm7, %ymm10
	vpaddq	%ymm7, %ymm7, %ymm12
	vpor	%ymm10, %ymm12, %ymm10
	vpxor	%ymm8, %ymm2, %ymm2
	vpxor	%ymm8, %ymm0, %ymm0
	vpblendd	$-64, %ymm10, %ymm11, %ymm8
	vpblendd	$3, %ymm7, %ymm9, %ymm7
	vpxor	%ymm7, %ymm8, %ymm7
	vpsllvq	-96(%rax), %ymm2, %ymm8
	vpsrlvq	-96(%rcx), %ymm2, %ymm2
	vpor	%ymm8, %ymm2, %ymm2
	vpxor	%ymm7, %ymm3, %ymm3
	vpsllvq	-32(%rax), %ymm3, %ymm8
	vpsrlvq	-32(%rcx), %ymm3, %ymm3
	vpor	%ymm8, %ymm3, %ymm3
	vpxor	%ymm7, %ymm4, %ymm4
	vpsllvq	(%rax), %ymm4, %ymm8
	vpsrlvq	(%rcx), %ymm4, %ymm4
	vpor	%ymm8, %ymm4, %ymm4
	vpxor	%ymm7, %ymm5, %ymm5
	vpsllvq	32(%rax), %ymm5, %ymm8
	vpsrlvq	32(%rcx), %ymm5, %ymm5
	vpor	%ymm8, %ymm5, %ymm5
	vpxor	%ymm7, %ymm6, %ymm6
	vpermq	$-115, %ymm2, %ymm8
	vpermq	$-115, %ymm3, %ymm9
	vpsllvq	64(%rax), %ymm6, %ymm2
	vpsrlvq	64(%rcx), %ymm6, %ymm3
	vpor	%ymm2, %ymm3, %ymm10
	vpxor	%ymm7, %ymm1, %ymm1
	vpermq	$27, %ymm4, %ymm4
	vpermq	$114, %ymm5, %ymm7
	vpsllvq	-64(%rax), %ymm1, %ymm2
	vpsrlvq	-64(%rcx), %ymm1, %ymm1
	vpor	%ymm2, %ymm1, %ymm1
	vpsrldq	$8, %ymm10, %ymm2
	vpandn	%ymm2, %ymm10, %ymm3
	vpblendd	$12, %ymm7, %ymm1, %ymm2
	vpblendd	$12, %ymm1, %ymm9, %ymm5
	vpblendd	$12, %ymm9, %ymm8, %ymm6
	vpblendd	$12, %ymm8, %ymm1, %ymm11
	vpblendd	$48, %ymm9, %ymm2, %ymm2
	vpblendd	$48, %ymm4, %ymm5, %ymm5
	vpblendd	$48, %ymm1, %ymm6, %ymm6
	vpblendd	$48, %ymm7, %ymm11, %ymm11
	vpblendd	$-64, %ymm4, %ymm2, %ymm2
	vpblendd	$-64, %ymm7, %ymm5, %ymm5
	vpblendd	$-64, %ymm7, %ymm6, %ymm6
	vpblendd	$-64, %ymm9, %ymm11, %ymm11
	vpandn	%ymm5, %ymm2, %ymm2
	vpandn	%ymm11, %ymm6, %ymm5
	vpblendd	$12, %ymm1, %ymm4, %ymm6
	vpblendd	$12, %ymm4, %ymm8, %ymm11
	vpxor	%ymm8, %ymm2, %ymm12
	vpblendd	$48, %ymm8, %ymm6, %ymm2
	vpblendd	$48, %ymm9, %ymm11, %ymm6
	vpxor	%ymm4, %ymm5, %ymm5
	vpblendd	$-64, %ymm9, %ymm2, %ymm2
	vpblendd	$-64, %ymm1, %ymm6, %ymm6
	vpandn	%ymm6, %ymm2, %ymm2
	vpxor	%ymm7, %ymm2, %ymm6
	vpermq	$30, %ymm10, %ymm2
	vpblendd	$48, %ymm0, %ymm2, %ymm2
	vpermq	$57, %ymm10, %ymm11
	vpblendd	$-64, %ymm0, %ymm11, %ymm11
	vpandn	%ymm2, %ymm11, %ymm11
	vpblendd	$12, %ymm4, %ymm9, %ymm2
	vpblendd	$12, %ymm9, %ymm7, %ymm13
	vpblendd	$48, %ymm7, %ymm2, %ymm2
	vpblendd	$48, %ymm8, %ymm13, %ymm13
	vpblendd	$-64, %ymm8, %ymm2, %ymm2
	vpblendd	$-64, %ymm4, %ymm13, %ymm13
	vpandn	%ymm13, %ymm2, %ymm2
	vpxor	%ymm1, %ymm2, %ymm2
	vpermq	$0, %ymm3, %ymm13
	vpermq	$27, %ymm12, %ymm3
	vpermq	$-115, %ymm5, %ymm5
	vpermq	$114, %ymm6, %ymm6
	vpblendd	$12, %ymm8, %ymm7, %ymm12
	vpblendd	$12, %ymm7, %ymm4, %ymm7
	vpblendd	$48, %ymm4, %ymm12, %ymm4
	vpblendd	$48, %ymm1, %ymm7, %ymm7
	vpblendd	$-64, %ymm1, %ymm4, %ymm1
	vpblendd	$-64, %ymm8, %ymm7, %ymm4
	vpandn	%ymm4, %ymm1, %ymm4
	vpxor	%ymm13, %ymm0, %ymm0
	vpxor	%ymm10, %ymm11, %ymm1
	vpxor	%ymm9, %ymm4, %ymm4
	vpxor	(%rbp), %ymm0, %ymm0
	leaq	32(%rbp), %rbp
	decl	%edx
	jne 	Lkeccak_1600$5
	vmovdqu	%ymm0, (%rsp)
	vmovdqu	%ymm1, 32(%rsp)
	vmovdqu	%ymm2, 64(%rsp)
	vmovdqu	%ymm3, 96(%rsp)
	vmovdqu	%ymm4, 128(%rsp)
	vmovdqu	%ymm5, 160(%rsp)
	vmovdqu	%ymm6, 192(%rsp)
	movq	%rsi, %rax
	shrq	$3, %rax
	movq	$0, %rcx
	jmp 	Lkeccak_1600$3
Lkeccak_1600$4:
	movq	(%r9,%rcx,8), %rdx
	movq	(%rsp,%rdx,8), %rdx
	movq	%rdx, (%rdi,%rcx,8)
	leaq	1(%rcx), %rcx
Lkeccak_1600$3:
	cmpq	%rax, %rcx
	jb  	Lkeccak_1600$4
	movq	(%r9,%rcx,8), %rax
	shlq	$3, %rcx
	shlq	$3, %rax
	jmp 	Lkeccak_1600$1
Lkeccak_1600$2:
	movb	(%rsp,%rax), %dl
	movb	%dl, (%rdi,%rcx)
	leaq	1(%rcx), %rcx
	leaq	1(%rax), %rax
Lkeccak_1600$1:
	cmpq	%rsi, %rcx
	jb  	Lkeccak_1600$2
	addq	$256, %rsp
	popq	%r14
	popq	%r13
	popq	%r12
	popq	%rbx
	popq	%rbp
	ret 
	.data
	.globl	_g_zero
	.globl	g_zero
	.p2align	3
_g_zero:
g_zero:
	.quad	0
	.globl	_s_zero
	.globl	s_zero
	.p2align	3
_s_zero:
s_zero:
	.quad	0
