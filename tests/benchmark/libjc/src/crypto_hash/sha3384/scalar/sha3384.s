	.text
	.p2align	5
	.globl	_keccak_1600
	.globl	keccak_1600
_keccak_1600:
keccak_1600:
	pushq	%rbp
	pushq	%rbx
	pushq	%r12
	subq	$456, %rsp
	movq	%rdi, 200(%rsp)
	movq	%rsi, 448(%rsp)
	movzbq	(%r8), %rax
	movq	%rax, 440(%rsp)
	movq	8(%r8), %rax
	xorl	%esi, %esi
	movq	$0, %rdi
	jmp 	Lkeccak_1600$20
Lkeccak_1600$21:
	movq	%rsi, (%rsp,%rdi,8)
	leaq	1(%rdi), %rdi
Lkeccak_1600$20:
	cmpq	$25, %rdi
	jb  	Lkeccak_1600$21
	jmp 	Lkeccak_1600$15
Lkeccak_1600$16:
	movq	%rax, %rsi
	shrq	$3, %rsi
	movq	$0, %rdi
	jmp 	Lkeccak_1600$18
Lkeccak_1600$19:
	movq	(%rdx,%rdi,8), %r8
	xorq	%r8, (%rsp,%rdi,8)
	leaq	1(%rdi), %rdi
Lkeccak_1600$18:
	cmpq	%rsi, %rdi
	jb  	Lkeccak_1600$19
	leaq	(%rdx,%rax), %rdx
	subq	%rax, %rcx
	movq	%rdx, 224(%rsp)
	movq	%rcx, 216(%rsp)
	movq	%rax, 208(%rsp)
Lkeccak_1600$17:
	movq	(%r9), %rax
	movq	%rax, 432(%rsp)
	movq	(%rsp), %rax
	movq	8(%rsp), %rcx
	movq	16(%rsp), %rdx
	movq	24(%rsp), %rsi
	movq	32(%rsp), %rdi
	xorq	40(%rsp), %rax
	xorq	48(%rsp), %rcx
	xorq	56(%rsp), %rdx
	xorq	64(%rsp), %rsi
	xorq	72(%rsp), %rdi
	xorq	80(%rsp), %rax
	xorq	88(%rsp), %rcx
	xorq	96(%rsp), %rdx
	xorq	104(%rsp), %rsi
	xorq	112(%rsp), %rdi
	xorq	120(%rsp), %rax
	xorq	128(%rsp), %rcx
	xorq	136(%rsp), %rdx
	xorq	144(%rsp), %rsi
	xorq	152(%rsp), %rdi
	xorq	160(%rsp), %rax
	xorq	168(%rsp), %rcx
	xorq	176(%rsp), %rdx
	xorq	184(%rsp), %rsi
	xorq	192(%rsp), %rdi
	movq	%rcx, %r8
	rolq	$1, %r8
	xorq	%rdi, %r8
	movq	%rdx, %r10
	rolq	$1, %r10
	xorq	%rax, %r10
	movq	%rsi, %r11
	rolq	$1, %r11
	xorq	%rcx, %r11
	movq	%rdi, %rcx
	rolq	$1, %rcx
	xorq	%rdx, %rcx
	rolq	$1, %rax
	xorq	%rsi, %rax
	movq	(%rsp), %rdx
	xorq	%r8, %rdx
	movq	48(%rsp), %rsi
	xorq	%r10, %rsi
	rolq	$44, %rsi
	movq	96(%rsp), %rdi
	xorq	%r11, %rdi
	rolq	$43, %rdi
	movq	144(%rsp), %rbp
	xorq	%rcx, %rbp
	rolq	$21, %rbp
	movq	192(%rsp), %rbx
	xorq	%rax, %rbx
	rolq	$14, %rbx
	andnq	%rdi, %rsi, %r12
	xorq	432(%rsp), %r12
	xorq	%rdx, %r12
	movq	%r12, 232(%rsp)
	andnq	%rbp, %rdi, %r12
	xorq	%rsi, %r12
	movq	%r12, 240(%rsp)
	andnq	%rbx, %rbp, %r12
	xorq	%rdi, %r12
	movq	%r12, 248(%rsp)
	andnq	%rdx, %rbx, %rdi
	xorq	%rbp, %rdi
	movq	%rdi, 256(%rsp)
	andnq	%rsi, %rdx, %rdx
	xorq	%rbx, %rdx
	movq	%rdx, 264(%rsp)
	movq	24(%rsp), %rdx
	xorq	%rcx, %rdx
	rolq	$28, %rdx
	movq	72(%rsp), %rsi
	xorq	%rax, %rsi
	rolq	$20, %rsi
	movq	80(%rsp), %rdi
	xorq	%r8, %rdi
	rolq	$3, %rdi
	movq	128(%rsp), %rbp
	xorq	%r10, %rbp
	rolq	$45, %rbp
	movq	176(%rsp), %rbx
	xorq	%r11, %rbx
	rolq	$61, %rbx
	andnq	%rdi, %rsi, %r12
	xorq	%rdx, %r12
	movq	%r12, 272(%rsp)
	andnq	%rbp, %rdi, %r12
	xorq	%rsi, %r12
	movq	%r12, 280(%rsp)
	andnq	%rbx, %rbp, %r12
	xorq	%rdi, %r12
	movq	%r12, 288(%rsp)
	andnq	%rdx, %rbx, %rdi
	xorq	%rbp, %rdi
	movq	%rdi, 296(%rsp)
	andnq	%rsi, %rdx, %rdx
	xorq	%rbx, %rdx
	movq	%rdx, 304(%rsp)
	movq	8(%rsp), %rdx
	xorq	%r10, %rdx
	rolq	$1, %rdx
	movq	56(%rsp), %rsi
	xorq	%r11, %rsi
	rolq	$6, %rsi
	movq	104(%rsp), %rdi
	xorq	%rcx, %rdi
	rolq	$25, %rdi
	movq	152(%rsp), %rbp
	xorq	%rax, %rbp
	rolq	$8, %rbp
	movq	160(%rsp), %rbx
	xorq	%r8, %rbx
	rolq	$18, %rbx
	andnq	%rdi, %rsi, %r12
	xorq	%rdx, %r12
	movq	%r12, 312(%rsp)
	andnq	%rbp, %rdi, %r12
	xorq	%rsi, %r12
	movq	%r12, 320(%rsp)
	andnq	%rbx, %rbp, %r12
	xorq	%rdi, %r12
	movq	%r12, 328(%rsp)
	andnq	%rdx, %rbx, %rdi
	xorq	%rbp, %rdi
	movq	%rdi, 336(%rsp)
	andnq	%rsi, %rdx, %rdx
	xorq	%rbx, %rdx
	movq	%rdx, 344(%rsp)
	movq	32(%rsp), %rdx
	xorq	%rax, %rdx
	rolq	$27, %rdx
	movq	40(%rsp), %rsi
	xorq	%r8, %rsi
	rolq	$36, %rsi
	movq	88(%rsp), %rdi
	xorq	%r10, %rdi
	rolq	$10, %rdi
	movq	136(%rsp), %rbp
	xorq	%r11, %rbp
	rolq	$15, %rbp
	movq	184(%rsp), %rbx
	xorq	%rcx, %rbx
	rolq	$56, %rbx
	andnq	%rdi, %rsi, %r12
	xorq	%rdx, %r12
	movq	%r12, 352(%rsp)
	andnq	%rbp, %rdi, %r12
	xorq	%rsi, %r12
	movq	%r12, 360(%rsp)
	andnq	%rbx, %rbp, %r12
	xorq	%rdi, %r12
	movq	%r12, 368(%rsp)
	andnq	%rdx, %rbx, %rdi
	xorq	%rbp, %rdi
	movq	%rdi, 376(%rsp)
	andnq	%rsi, %rdx, %rdx
	xorq	%rbx, %rdx
	movq	%rdx, 384(%rsp)
	movq	16(%rsp), %rdx
	xorq	%r11, %rdx
	rolq	$62, %rdx
	movq	64(%rsp), %rsi
	xorq	%rcx, %rsi
	rolq	$55, %rsi
	movq	%rsi, %rcx
	movq	112(%rsp), %rsi
	xorq	%rax, %rsi
	rolq	$39, %rsi
	movq	%rsi, %rax
	movq	120(%rsp), %rsi
	xorq	%r8, %rsi
	rolq	$41, %rsi
	movq	168(%rsp), %rdi
	xorq	%r10, %rdi
	rolq	$2, %rdi
	andnq	%rax, %rcx, %r8
	xorq	%rdx, %r8
	movq	%r8, 392(%rsp)
	andnq	%rsi, %rax, %r8
	xorq	%rcx, %r8
	movq	%r8, 400(%rsp)
	andnq	%rdi, %rsi, %r8
	xorq	%rax, %r8
	movq	%r8, 408(%rsp)
	andnq	%rdx, %rdi, %rax
	xorq	%rsi, %rax
	movq	%rax, 416(%rsp)
	andnq	%rcx, %rdx, %rax
	xorq	%rdi, %rax
	movq	%rax, 424(%rsp)
	movq	8(%r9), %rax
	movq	%rax, 432(%rsp)
	movq	232(%rsp), %rax
	movq	240(%rsp), %rcx
	movq	248(%rsp), %rdx
	movq	256(%rsp), %rsi
	movq	264(%rsp), %rdi
	xorq	272(%rsp), %rax
	xorq	280(%rsp), %rcx
	xorq	288(%rsp), %rdx
	xorq	296(%rsp), %rsi
	xorq	304(%rsp), %rdi
	xorq	312(%rsp), %rax
	xorq	320(%rsp), %rcx
	xorq	328(%rsp), %rdx
	xorq	336(%rsp), %rsi
	xorq	344(%rsp), %rdi
	xorq	352(%rsp), %rax
	xorq	360(%rsp), %rcx
	xorq	368(%rsp), %rdx
	xorq	376(%rsp), %rsi
	xorq	384(%rsp), %rdi
	xorq	392(%rsp), %rax
	xorq	400(%rsp), %rcx
	xorq	408(%rsp), %rdx
	xorq	416(%rsp), %rsi
	xorq	424(%rsp), %rdi
	movq	%rcx, %r8
	rolq	$1, %r8
	xorq	%rdi, %r8
	movq	%rdx, %r10
	rolq	$1, %r10
	xorq	%rax, %r10
	movq	%rsi, %r11
	rolq	$1, %r11
	xorq	%rcx, %r11
	movq	%rdi, %rcx
	rolq	$1, %rcx
	xorq	%rdx, %rcx
	rolq	$1, %rax
	xorq	%rsi, %rax
	movq	232(%rsp), %rdx
	xorq	%r8, %rdx
	movq	280(%rsp), %rsi
	xorq	%r10, %rsi
	rolq	$44, %rsi
	movq	328(%rsp), %rdi
	xorq	%r11, %rdi
	rolq	$43, %rdi
	movq	376(%rsp), %rbp
	xorq	%rcx, %rbp
	rolq	$21, %rbp
	movq	424(%rsp), %rbx
	xorq	%rax, %rbx
	rolq	$14, %rbx
	andnq	%rdi, %rsi, %r12
	xorq	432(%rsp), %r12
	xorq	%rdx, %r12
	movq	%r12, (%rsp)
	andnq	%rbp, %rdi, %r12
	xorq	%rsi, %r12
	movq	%r12, 8(%rsp)
	andnq	%rbx, %rbp, %r12
	xorq	%rdi, %r12
	movq	%r12, 16(%rsp)
	andnq	%rdx, %rbx, %rdi
	xorq	%rbp, %rdi
	movq	%rdi, 24(%rsp)
	andnq	%rsi, %rdx, %rdx
	xorq	%rbx, %rdx
	movq	%rdx, 32(%rsp)
	movq	256(%rsp), %rdx
	xorq	%rcx, %rdx
	rolq	$28, %rdx
	movq	304(%rsp), %rsi
	xorq	%rax, %rsi
	rolq	$20, %rsi
	movq	312(%rsp), %rdi
	xorq	%r8, %rdi
	rolq	$3, %rdi
	movq	360(%rsp), %rbp
	xorq	%r10, %rbp
	rolq	$45, %rbp
	movq	408(%rsp), %rbx
	xorq	%r11, %rbx
	rolq	$61, %rbx
	andnq	%rdi, %rsi, %r12
	xorq	%rdx, %r12
	movq	%r12, 40(%rsp)
	andnq	%rbp, %rdi, %r12
	xorq	%rsi, %r12
	movq	%r12, 48(%rsp)
	andnq	%rbx, %rbp, %r12
	xorq	%rdi, %r12
	movq	%r12, 56(%rsp)
	andnq	%rdx, %rbx, %rdi
	xorq	%rbp, %rdi
	movq	%rdi, 64(%rsp)
	andnq	%rsi, %rdx, %rdx
	xorq	%rbx, %rdx
	movq	%rdx, 72(%rsp)
	movq	240(%rsp), %rdx
	xorq	%r10, %rdx
	rolq	$1, %rdx
	movq	288(%rsp), %rsi
	xorq	%r11, %rsi
	rolq	$6, %rsi
	movq	336(%rsp), %rdi
	xorq	%rcx, %rdi
	rolq	$25, %rdi
	movq	384(%rsp), %rbp
	xorq	%rax, %rbp
	rolq	$8, %rbp
	movq	392(%rsp), %rbx
	xorq	%r8, %rbx
	rolq	$18, %rbx
	andnq	%rdi, %rsi, %r12
	xorq	%rdx, %r12
	movq	%r12, 80(%rsp)
	andnq	%rbp, %rdi, %r12
	xorq	%rsi, %r12
	movq	%r12, 88(%rsp)
	andnq	%rbx, %rbp, %r12
	xorq	%rdi, %r12
	movq	%r12, 96(%rsp)
	andnq	%rdx, %rbx, %rdi
	xorq	%rbp, %rdi
	movq	%rdi, 104(%rsp)
	andnq	%rsi, %rdx, %rdx
	xorq	%rbx, %rdx
	movq	%rdx, 112(%rsp)
	movq	264(%rsp), %rdx
	xorq	%rax, %rdx
	rolq	$27, %rdx
	movq	272(%rsp), %rsi
	xorq	%r8, %rsi
	rolq	$36, %rsi
	movq	320(%rsp), %rdi
	xorq	%r10, %rdi
	rolq	$10, %rdi
	movq	368(%rsp), %rbp
	xorq	%r11, %rbp
	rolq	$15, %rbp
	movq	416(%rsp), %rbx
	xorq	%rcx, %rbx
	rolq	$56, %rbx
	andnq	%rdi, %rsi, %r12
	xorq	%rdx, %r12
	movq	%r12, 120(%rsp)
	andnq	%rbp, %rdi, %r12
	xorq	%rsi, %r12
	movq	%r12, 128(%rsp)
	andnq	%rbx, %rbp, %r12
	xorq	%rdi, %r12
	movq	%r12, 136(%rsp)
	andnq	%rdx, %rbx, %rdi
	xorq	%rbp, %rdi
	movq	%rdi, 144(%rsp)
	andnq	%rsi, %rdx, %rdx
	xorq	%rbx, %rdx
	movq	%rdx, 152(%rsp)
	movq	248(%rsp), %rdx
	xorq	%r11, %rdx
	rolq	$62, %rdx
	movq	296(%rsp), %rsi
	xorq	%rcx, %rsi
	rolq	$55, %rsi
	movq	%rsi, %rcx
	movq	344(%rsp), %rsi
	xorq	%rax, %rsi
	rolq	$39, %rsi
	movq	%rsi, %rax
	movq	352(%rsp), %rsi
	xorq	%r8, %rsi
	rolq	$41, %rsi
	movq	400(%rsp), %rdi
	xorq	%r10, %rdi
	rolq	$2, %rdi
	andnq	%rax, %rcx, %r8
	xorq	%rdx, %r8
	movq	%r8, 160(%rsp)
	andnq	%rsi, %rax, %r8
	xorq	%rcx, %r8
	movq	%r8, 168(%rsp)
	andnq	%rdi, %rsi, %r8
	xorq	%rax, %r8
	movq	%r8, 176(%rsp)
	andnq	%rdx, %rdi, %rax
	xorq	%rsi, %rax
	movq	%rax, 184(%rsp)
	andnq	%rcx, %rdx, %rax
	xorq	%rdi, %rax
	movq	%rax, 192(%rsp)
	leaq	16(%r9), %r9
	testb	$-1, %r9b
	jne 	Lkeccak_1600$17
	leaq	-192(%r9), %r9
	movq	224(%rsp), %rdx
	movq	216(%rsp), %rcx
	movq	208(%rsp), %rax
Lkeccak_1600$15:
	cmpq	%rax, %rcx
	jnb 	Lkeccak_1600$16
	movq	440(%rsp), %rsi
	movb	%sil, %sil
	movq	%rcx, %rdi
	shrq	$3, %rdi
	movq	$0, %r8
	jmp 	Lkeccak_1600$13
Lkeccak_1600$14:
	movq	(%rdx,%r8,8), %r10
	xorq	%r10, (%rsp,%r8,8)
	leaq	1(%r8), %r8
Lkeccak_1600$13:
	cmpq	%rdi, %r8
	jb  	Lkeccak_1600$14
	shlq	$3, %r8
	jmp 	Lkeccak_1600$11
Lkeccak_1600$12:
	movb	(%rdx,%r8), %dil
	xorb	%dil, (%rsp,%r8)
	leaq	1(%r8), %r8
Lkeccak_1600$11:
	cmpq	%rcx, %r8
	jb  	Lkeccak_1600$12
	xorb	%sil, (%rsp,%r8)
	movq	%rax, %rcx
	leaq	-1(%rcx), %rcx
	xorb	$-128, (%rsp,%rcx)
	movq	448(%rsp), %rdx
	jmp 	Lkeccak_1600$6
Lkeccak_1600$7:
	movq	%rdx, 448(%rsp)
	movq	%rax, 440(%rsp)
Lkeccak_1600$10:
	movq	(%r9), %rax
	movq	%rax, 432(%rsp)
	movq	(%rsp), %rax
	movq	8(%rsp), %rcx
	movq	16(%rsp), %rdx
	movq	24(%rsp), %rsi
	movq	32(%rsp), %rdi
	xorq	40(%rsp), %rax
	xorq	48(%rsp), %rcx
	xorq	56(%rsp), %rdx
	xorq	64(%rsp), %rsi
	xorq	72(%rsp), %rdi
	xorq	80(%rsp), %rax
	xorq	88(%rsp), %rcx
	xorq	96(%rsp), %rdx
	xorq	104(%rsp), %rsi
	xorq	112(%rsp), %rdi
	xorq	120(%rsp), %rax
	xorq	128(%rsp), %rcx
	xorq	136(%rsp), %rdx
	xorq	144(%rsp), %rsi
	xorq	152(%rsp), %rdi
	xorq	160(%rsp), %rax
	xorq	168(%rsp), %rcx
	xorq	176(%rsp), %rdx
	xorq	184(%rsp), %rsi
	xorq	192(%rsp), %rdi
	movq	%rcx, %r8
	rolq	$1, %r8
	xorq	%rdi, %r8
	movq	%rdx, %r10
	rolq	$1, %r10
	xorq	%rax, %r10
	movq	%rsi, %r11
	rolq	$1, %r11
	xorq	%rcx, %r11
	movq	%rdi, %rcx
	rolq	$1, %rcx
	xorq	%rdx, %rcx
	rolq	$1, %rax
	xorq	%rsi, %rax
	movq	(%rsp), %rdx
	xorq	%r8, %rdx
	movq	48(%rsp), %rsi
	xorq	%r10, %rsi
	rolq	$44, %rsi
	movq	96(%rsp), %rdi
	xorq	%r11, %rdi
	rolq	$43, %rdi
	movq	144(%rsp), %rbp
	xorq	%rcx, %rbp
	rolq	$21, %rbp
	movq	192(%rsp), %rbx
	xorq	%rax, %rbx
	rolq	$14, %rbx
	andnq	%rdi, %rsi, %r12
	xorq	432(%rsp), %r12
	xorq	%rdx, %r12
	movq	%r12, 232(%rsp)
	andnq	%rbp, %rdi, %r12
	xorq	%rsi, %r12
	movq	%r12, 240(%rsp)
	andnq	%rbx, %rbp, %r12
	xorq	%rdi, %r12
	movq	%r12, 248(%rsp)
	andnq	%rdx, %rbx, %rdi
	xorq	%rbp, %rdi
	movq	%rdi, 256(%rsp)
	andnq	%rsi, %rdx, %rdx
	xorq	%rbx, %rdx
	movq	%rdx, 264(%rsp)
	movq	24(%rsp), %rdx
	xorq	%rcx, %rdx
	rolq	$28, %rdx
	movq	72(%rsp), %rsi
	xorq	%rax, %rsi
	rolq	$20, %rsi
	movq	80(%rsp), %rdi
	xorq	%r8, %rdi
	rolq	$3, %rdi
	movq	128(%rsp), %rbp
	xorq	%r10, %rbp
	rolq	$45, %rbp
	movq	176(%rsp), %rbx
	xorq	%r11, %rbx
	rolq	$61, %rbx
	andnq	%rdi, %rsi, %r12
	xorq	%rdx, %r12
	movq	%r12, 272(%rsp)
	andnq	%rbp, %rdi, %r12
	xorq	%rsi, %r12
	movq	%r12, 280(%rsp)
	andnq	%rbx, %rbp, %r12
	xorq	%rdi, %r12
	movq	%r12, 288(%rsp)
	andnq	%rdx, %rbx, %rdi
	xorq	%rbp, %rdi
	movq	%rdi, 296(%rsp)
	andnq	%rsi, %rdx, %rdx
	xorq	%rbx, %rdx
	movq	%rdx, 304(%rsp)
	movq	8(%rsp), %rdx
	xorq	%r10, %rdx
	rolq	$1, %rdx
	movq	56(%rsp), %rsi
	xorq	%r11, %rsi
	rolq	$6, %rsi
	movq	104(%rsp), %rdi
	xorq	%rcx, %rdi
	rolq	$25, %rdi
	movq	152(%rsp), %rbp
	xorq	%rax, %rbp
	rolq	$8, %rbp
	movq	160(%rsp), %rbx
	xorq	%r8, %rbx
	rolq	$18, %rbx
	andnq	%rdi, %rsi, %r12
	xorq	%rdx, %r12
	movq	%r12, 312(%rsp)
	andnq	%rbp, %rdi, %r12
	xorq	%rsi, %r12
	movq	%r12, 320(%rsp)
	andnq	%rbx, %rbp, %r12
	xorq	%rdi, %r12
	movq	%r12, 328(%rsp)
	andnq	%rdx, %rbx, %rdi
	xorq	%rbp, %rdi
	movq	%rdi, 336(%rsp)
	andnq	%rsi, %rdx, %rdx
	xorq	%rbx, %rdx
	movq	%rdx, 344(%rsp)
	movq	32(%rsp), %rdx
	xorq	%rax, %rdx
	rolq	$27, %rdx
	movq	40(%rsp), %rsi
	xorq	%r8, %rsi
	rolq	$36, %rsi
	movq	88(%rsp), %rdi
	xorq	%r10, %rdi
	rolq	$10, %rdi
	movq	136(%rsp), %rbp
	xorq	%r11, %rbp
	rolq	$15, %rbp
	movq	184(%rsp), %rbx
	xorq	%rcx, %rbx
	rolq	$56, %rbx
	andnq	%rdi, %rsi, %r12
	xorq	%rdx, %r12
	movq	%r12, 352(%rsp)
	andnq	%rbp, %rdi, %r12
	xorq	%rsi, %r12
	movq	%r12, 360(%rsp)
	andnq	%rbx, %rbp, %r12
	xorq	%rdi, %r12
	movq	%r12, 368(%rsp)
	andnq	%rdx, %rbx, %rdi
	xorq	%rbp, %rdi
	movq	%rdi, 376(%rsp)
	andnq	%rsi, %rdx, %rdx
	xorq	%rbx, %rdx
	movq	%rdx, 384(%rsp)
	movq	16(%rsp), %rdx
	xorq	%r11, %rdx
	rolq	$62, %rdx
	movq	64(%rsp), %rsi
	xorq	%rcx, %rsi
	rolq	$55, %rsi
	movq	%rsi, %rcx
	movq	112(%rsp), %rsi
	xorq	%rax, %rsi
	rolq	$39, %rsi
	movq	%rsi, %rax
	movq	120(%rsp), %rsi
	xorq	%r8, %rsi
	rolq	$41, %rsi
	movq	168(%rsp), %rdi
	xorq	%r10, %rdi
	rolq	$2, %rdi
	andnq	%rax, %rcx, %r8
	xorq	%rdx, %r8
	movq	%r8, 392(%rsp)
	andnq	%rsi, %rax, %r8
	xorq	%rcx, %r8
	movq	%r8, 400(%rsp)
	andnq	%rdi, %rsi, %r8
	xorq	%rax, %r8
	movq	%r8, 408(%rsp)
	andnq	%rdx, %rdi, %rax
	xorq	%rsi, %rax
	movq	%rax, 416(%rsp)
	andnq	%rcx, %rdx, %rax
	xorq	%rdi, %rax
	movq	%rax, 424(%rsp)
	movq	8(%r9), %rax
	movq	%rax, 432(%rsp)
	movq	232(%rsp), %rax
	movq	240(%rsp), %rcx
	movq	248(%rsp), %rdx
	movq	256(%rsp), %rsi
	movq	264(%rsp), %rdi
	xorq	272(%rsp), %rax
	xorq	280(%rsp), %rcx
	xorq	288(%rsp), %rdx
	xorq	296(%rsp), %rsi
	xorq	304(%rsp), %rdi
	xorq	312(%rsp), %rax
	xorq	320(%rsp), %rcx
	xorq	328(%rsp), %rdx
	xorq	336(%rsp), %rsi
	xorq	344(%rsp), %rdi
	xorq	352(%rsp), %rax
	xorq	360(%rsp), %rcx
	xorq	368(%rsp), %rdx
	xorq	376(%rsp), %rsi
	xorq	384(%rsp), %rdi
	xorq	392(%rsp), %rax
	xorq	400(%rsp), %rcx
	xorq	408(%rsp), %rdx
	xorq	416(%rsp), %rsi
	xorq	424(%rsp), %rdi
	movq	%rcx, %r8
	rolq	$1, %r8
	xorq	%rdi, %r8
	movq	%rdx, %r10
	rolq	$1, %r10
	xorq	%rax, %r10
	movq	%rsi, %r11
	rolq	$1, %r11
	xorq	%rcx, %r11
	movq	%rdi, %rcx
	rolq	$1, %rcx
	xorq	%rdx, %rcx
	rolq	$1, %rax
	xorq	%rsi, %rax
	movq	232(%rsp), %rdx
	xorq	%r8, %rdx
	movq	280(%rsp), %rsi
	xorq	%r10, %rsi
	rolq	$44, %rsi
	movq	328(%rsp), %rdi
	xorq	%r11, %rdi
	rolq	$43, %rdi
	movq	376(%rsp), %rbp
	xorq	%rcx, %rbp
	rolq	$21, %rbp
	movq	424(%rsp), %rbx
	xorq	%rax, %rbx
	rolq	$14, %rbx
	andnq	%rdi, %rsi, %r12
	xorq	432(%rsp), %r12
	xorq	%rdx, %r12
	movq	%r12, (%rsp)
	andnq	%rbp, %rdi, %r12
	xorq	%rsi, %r12
	movq	%r12, 8(%rsp)
	andnq	%rbx, %rbp, %r12
	xorq	%rdi, %r12
	movq	%r12, 16(%rsp)
	andnq	%rdx, %rbx, %rdi
	xorq	%rbp, %rdi
	movq	%rdi, 24(%rsp)
	andnq	%rsi, %rdx, %rdx
	xorq	%rbx, %rdx
	movq	%rdx, 32(%rsp)
	movq	256(%rsp), %rdx
	xorq	%rcx, %rdx
	rolq	$28, %rdx
	movq	304(%rsp), %rsi
	xorq	%rax, %rsi
	rolq	$20, %rsi
	movq	312(%rsp), %rdi
	xorq	%r8, %rdi
	rolq	$3, %rdi
	movq	360(%rsp), %rbp
	xorq	%r10, %rbp
	rolq	$45, %rbp
	movq	408(%rsp), %rbx
	xorq	%r11, %rbx
	rolq	$61, %rbx
	andnq	%rdi, %rsi, %r12
	xorq	%rdx, %r12
	movq	%r12, 40(%rsp)
	andnq	%rbp, %rdi, %r12
	xorq	%rsi, %r12
	movq	%r12, 48(%rsp)
	andnq	%rbx, %rbp, %r12
	xorq	%rdi, %r12
	movq	%r12, 56(%rsp)
	andnq	%rdx, %rbx, %rdi
	xorq	%rbp, %rdi
	movq	%rdi, 64(%rsp)
	andnq	%rsi, %rdx, %rdx
	xorq	%rbx, %rdx
	movq	%rdx, 72(%rsp)
	movq	240(%rsp), %rdx
	xorq	%r10, %rdx
	rolq	$1, %rdx
	movq	288(%rsp), %rsi
	xorq	%r11, %rsi
	rolq	$6, %rsi
	movq	336(%rsp), %rdi
	xorq	%rcx, %rdi
	rolq	$25, %rdi
	movq	384(%rsp), %rbp
	xorq	%rax, %rbp
	rolq	$8, %rbp
	movq	392(%rsp), %rbx
	xorq	%r8, %rbx
	rolq	$18, %rbx
	andnq	%rdi, %rsi, %r12
	xorq	%rdx, %r12
	movq	%r12, 80(%rsp)
	andnq	%rbp, %rdi, %r12
	xorq	%rsi, %r12
	movq	%r12, 88(%rsp)
	andnq	%rbx, %rbp, %r12
	xorq	%rdi, %r12
	movq	%r12, 96(%rsp)
	andnq	%rdx, %rbx, %rdi
	xorq	%rbp, %rdi
	movq	%rdi, 104(%rsp)
	andnq	%rsi, %rdx, %rdx
	xorq	%rbx, %rdx
	movq	%rdx, 112(%rsp)
	movq	264(%rsp), %rdx
	xorq	%rax, %rdx
	rolq	$27, %rdx
	movq	272(%rsp), %rsi
	xorq	%r8, %rsi
	rolq	$36, %rsi
	movq	320(%rsp), %rdi
	xorq	%r10, %rdi
	rolq	$10, %rdi
	movq	368(%rsp), %rbp
	xorq	%r11, %rbp
	rolq	$15, %rbp
	movq	416(%rsp), %rbx
	xorq	%rcx, %rbx
	rolq	$56, %rbx
	andnq	%rdi, %rsi, %r12
	xorq	%rdx, %r12
	movq	%r12, 120(%rsp)
	andnq	%rbp, %rdi, %r12
	xorq	%rsi, %r12
	movq	%r12, 128(%rsp)
	andnq	%rbx, %rbp, %r12
	xorq	%rdi, %r12
	movq	%r12, 136(%rsp)
	andnq	%rdx, %rbx, %rdi
	xorq	%rbp, %rdi
	movq	%rdi, 144(%rsp)
	andnq	%rsi, %rdx, %rdx
	xorq	%rbx, %rdx
	movq	%rdx, 152(%rsp)
	movq	248(%rsp), %rdx
	xorq	%r11, %rdx
	rolq	$62, %rdx
	movq	296(%rsp), %rsi
	xorq	%rcx, %rsi
	rolq	$55, %rsi
	movq	%rsi, %rcx
	movq	344(%rsp), %rsi
	xorq	%rax, %rsi
	rolq	$39, %rsi
	movq	%rsi, %rax
	movq	352(%rsp), %rsi
	xorq	%r8, %rsi
	rolq	$41, %rsi
	movq	400(%rsp), %rdi
	xorq	%r10, %rdi
	rolq	$2, %rdi
	andnq	%rax, %rcx, %r8
	xorq	%rdx, %r8
	movq	%r8, 160(%rsp)
	andnq	%rsi, %rax, %r8
	xorq	%rcx, %r8
	movq	%r8, 168(%rsp)
	andnq	%rdi, %rsi, %r8
	xorq	%rax, %r8
	movq	%r8, 176(%rsp)
	andnq	%rdx, %rdi, %rax
	xorq	%rsi, %rax
	movq	%rax, 184(%rsp)
	andnq	%rcx, %rdx, %rax
	xorq	%rdi, %rax
	movq	%rax, 192(%rsp)
	leaq	16(%r9), %r9
	testb	$-1, %r9b
	jne 	Lkeccak_1600$10
	leaq	-192(%r9), %r9
	movq	200(%rsp), %rcx
	movq	448(%rsp), %rdx
	movq	440(%rsp), %rax
	movq	%rax, %rsi
	shrq	$3, %rsi
	movq	$0, %rdi
	jmp 	Lkeccak_1600$8
Lkeccak_1600$9:
	movq	(%rsp,%rdi,8), %r8
	movq	%r8, (%rcx,%rdi,8)
	leaq	1(%rdi), %rdi
Lkeccak_1600$8:
	cmpq	%rsi, %rdi
	jb  	Lkeccak_1600$9
	leaq	(%rcx,%rax), %rcx
	subq	%rax, %rdx
	movq	%rcx, 200(%rsp)
Lkeccak_1600$6:
	cmpq	%rax, %rdx
	jnbe	Lkeccak_1600$7
	movq	%rdx, 440(%rsp)
Lkeccak_1600$5:
	movq	(%r9), %rax
	movq	%rax, 448(%rsp)
	movq	(%rsp), %rax
	movq	8(%rsp), %rcx
	movq	16(%rsp), %rdx
	movq	24(%rsp), %rsi
	movq	32(%rsp), %rdi
	xorq	40(%rsp), %rax
	xorq	48(%rsp), %rcx
	xorq	56(%rsp), %rdx
	xorq	64(%rsp), %rsi
	xorq	72(%rsp), %rdi
	xorq	80(%rsp), %rax
	xorq	88(%rsp), %rcx
	xorq	96(%rsp), %rdx
	xorq	104(%rsp), %rsi
	xorq	112(%rsp), %rdi
	xorq	120(%rsp), %rax
	xorq	128(%rsp), %rcx
	xorq	136(%rsp), %rdx
	xorq	144(%rsp), %rsi
	xorq	152(%rsp), %rdi
	xorq	160(%rsp), %rax
	xorq	168(%rsp), %rcx
	xorq	176(%rsp), %rdx
	xorq	184(%rsp), %rsi
	xorq	192(%rsp), %rdi
	movq	%rcx, %r8
	rolq	$1, %r8
	xorq	%rdi, %r8
	movq	%rdx, %r10
	rolq	$1, %r10
	xorq	%rax, %r10
	movq	%rsi, %r11
	rolq	$1, %r11
	xorq	%rcx, %r11
	movq	%rdi, %rcx
	rolq	$1, %rcx
	xorq	%rdx, %rcx
	rolq	$1, %rax
	xorq	%rsi, %rax
	movq	(%rsp), %rdx
	xorq	%r8, %rdx
	movq	48(%rsp), %rsi
	xorq	%r10, %rsi
	rolq	$44, %rsi
	movq	96(%rsp), %rdi
	xorq	%r11, %rdi
	rolq	$43, %rdi
	movq	144(%rsp), %rbp
	xorq	%rcx, %rbp
	rolq	$21, %rbp
	movq	192(%rsp), %rbx
	xorq	%rax, %rbx
	rolq	$14, %rbx
	andnq	%rdi, %rsi, %r12
	xorq	448(%rsp), %r12
	xorq	%rdx, %r12
	movq	%r12, 232(%rsp)
	andnq	%rbp, %rdi, %r12
	xorq	%rsi, %r12
	movq	%r12, 240(%rsp)
	andnq	%rbx, %rbp, %r12
	xorq	%rdi, %r12
	movq	%r12, 248(%rsp)
	andnq	%rdx, %rbx, %rdi
	xorq	%rbp, %rdi
	movq	%rdi, 256(%rsp)
	andnq	%rsi, %rdx, %rdx
	xorq	%rbx, %rdx
	movq	%rdx, 264(%rsp)
	movq	24(%rsp), %rdx
	xorq	%rcx, %rdx
	rolq	$28, %rdx
	movq	72(%rsp), %rsi
	xorq	%rax, %rsi
	rolq	$20, %rsi
	movq	80(%rsp), %rdi
	xorq	%r8, %rdi
	rolq	$3, %rdi
	movq	128(%rsp), %rbp
	xorq	%r10, %rbp
	rolq	$45, %rbp
	movq	176(%rsp), %rbx
	xorq	%r11, %rbx
	rolq	$61, %rbx
	andnq	%rdi, %rsi, %r12
	xorq	%rdx, %r12
	movq	%r12, 272(%rsp)
	andnq	%rbp, %rdi, %r12
	xorq	%rsi, %r12
	movq	%r12, 280(%rsp)
	andnq	%rbx, %rbp, %r12
	xorq	%rdi, %r12
	movq	%r12, 288(%rsp)
	andnq	%rdx, %rbx, %rdi
	xorq	%rbp, %rdi
	movq	%rdi, 296(%rsp)
	andnq	%rsi, %rdx, %rdx
	xorq	%rbx, %rdx
	movq	%rdx, 304(%rsp)
	movq	8(%rsp), %rdx
	xorq	%r10, %rdx
	rolq	$1, %rdx
	movq	56(%rsp), %rsi
	xorq	%r11, %rsi
	rolq	$6, %rsi
	movq	104(%rsp), %rdi
	xorq	%rcx, %rdi
	rolq	$25, %rdi
	movq	152(%rsp), %rbp
	xorq	%rax, %rbp
	rolq	$8, %rbp
	movq	160(%rsp), %rbx
	xorq	%r8, %rbx
	rolq	$18, %rbx
	andnq	%rdi, %rsi, %r12
	xorq	%rdx, %r12
	movq	%r12, 312(%rsp)
	andnq	%rbp, %rdi, %r12
	xorq	%rsi, %r12
	movq	%r12, 320(%rsp)
	andnq	%rbx, %rbp, %r12
	xorq	%rdi, %r12
	movq	%r12, 328(%rsp)
	andnq	%rdx, %rbx, %rdi
	xorq	%rbp, %rdi
	movq	%rdi, 336(%rsp)
	andnq	%rsi, %rdx, %rdx
	xorq	%rbx, %rdx
	movq	%rdx, 344(%rsp)
	movq	32(%rsp), %rdx
	xorq	%rax, %rdx
	rolq	$27, %rdx
	movq	40(%rsp), %rsi
	xorq	%r8, %rsi
	rolq	$36, %rsi
	movq	88(%rsp), %rdi
	xorq	%r10, %rdi
	rolq	$10, %rdi
	movq	136(%rsp), %rbp
	xorq	%r11, %rbp
	rolq	$15, %rbp
	movq	184(%rsp), %rbx
	xorq	%rcx, %rbx
	rolq	$56, %rbx
	andnq	%rdi, %rsi, %r12
	xorq	%rdx, %r12
	movq	%r12, 352(%rsp)
	andnq	%rbp, %rdi, %r12
	xorq	%rsi, %r12
	movq	%r12, 360(%rsp)
	andnq	%rbx, %rbp, %r12
	xorq	%rdi, %r12
	movq	%r12, 368(%rsp)
	andnq	%rdx, %rbx, %rdi
	xorq	%rbp, %rdi
	movq	%rdi, 376(%rsp)
	andnq	%rsi, %rdx, %rdx
	xorq	%rbx, %rdx
	movq	%rdx, 384(%rsp)
	movq	16(%rsp), %rdx
	xorq	%r11, %rdx
	rolq	$62, %rdx
	movq	64(%rsp), %rsi
	xorq	%rcx, %rsi
	rolq	$55, %rsi
	movq	%rsi, %rcx
	movq	112(%rsp), %rsi
	xorq	%rax, %rsi
	rolq	$39, %rsi
	movq	%rsi, %rax
	movq	120(%rsp), %rsi
	xorq	%r8, %rsi
	rolq	$41, %rsi
	movq	168(%rsp), %rdi
	xorq	%r10, %rdi
	rolq	$2, %rdi
	andnq	%rax, %rcx, %r8
	xorq	%rdx, %r8
	movq	%r8, 392(%rsp)
	andnq	%rsi, %rax, %r8
	xorq	%rcx, %r8
	movq	%r8, 400(%rsp)
	andnq	%rdi, %rsi, %r8
	xorq	%rax, %r8
	movq	%r8, 408(%rsp)
	andnq	%rdx, %rdi, %rax
	xorq	%rsi, %rax
	movq	%rax, 416(%rsp)
	andnq	%rcx, %rdx, %rax
	xorq	%rdi, %rax
	movq	%rax, 424(%rsp)
	movq	8(%r9), %rax
	movq	%rax, 448(%rsp)
	movq	232(%rsp), %rax
	movq	240(%rsp), %rcx
	movq	248(%rsp), %rdx
	movq	256(%rsp), %rsi
	movq	264(%rsp), %rdi
	xorq	272(%rsp), %rax
	xorq	280(%rsp), %rcx
	xorq	288(%rsp), %rdx
	xorq	296(%rsp), %rsi
	xorq	304(%rsp), %rdi
	xorq	312(%rsp), %rax
	xorq	320(%rsp), %rcx
	xorq	328(%rsp), %rdx
	xorq	336(%rsp), %rsi
	xorq	344(%rsp), %rdi
	xorq	352(%rsp), %rax
	xorq	360(%rsp), %rcx
	xorq	368(%rsp), %rdx
	xorq	376(%rsp), %rsi
	xorq	384(%rsp), %rdi
	xorq	392(%rsp), %rax
	xorq	400(%rsp), %rcx
	xorq	408(%rsp), %rdx
	xorq	416(%rsp), %rsi
	xorq	424(%rsp), %rdi
	movq	%rcx, %r8
	rolq	$1, %r8
	xorq	%rdi, %r8
	movq	%rdx, %r10
	rolq	$1, %r10
	xorq	%rax, %r10
	movq	%rsi, %r11
	rolq	$1, %r11
	xorq	%rcx, %r11
	movq	%rdi, %rcx
	rolq	$1, %rcx
	xorq	%rdx, %rcx
	rolq	$1, %rax
	xorq	%rsi, %rax
	movq	232(%rsp), %rdx
	xorq	%r8, %rdx
	movq	280(%rsp), %rsi
	xorq	%r10, %rsi
	rolq	$44, %rsi
	movq	328(%rsp), %rdi
	xorq	%r11, %rdi
	rolq	$43, %rdi
	movq	376(%rsp), %rbp
	xorq	%rcx, %rbp
	rolq	$21, %rbp
	movq	424(%rsp), %rbx
	xorq	%rax, %rbx
	rolq	$14, %rbx
	andnq	%rdi, %rsi, %r12
	xorq	448(%rsp), %r12
	xorq	%rdx, %r12
	movq	%r12, (%rsp)
	andnq	%rbp, %rdi, %r12
	xorq	%rsi, %r12
	movq	%r12, 8(%rsp)
	andnq	%rbx, %rbp, %r12
	xorq	%rdi, %r12
	movq	%r12, 16(%rsp)
	andnq	%rdx, %rbx, %rdi
	xorq	%rbp, %rdi
	movq	%rdi, 24(%rsp)
	andnq	%rsi, %rdx, %rdx
	xorq	%rbx, %rdx
	movq	%rdx, 32(%rsp)
	movq	256(%rsp), %rdx
	xorq	%rcx, %rdx
	rolq	$28, %rdx
	movq	304(%rsp), %rsi
	xorq	%rax, %rsi
	rolq	$20, %rsi
	movq	312(%rsp), %rdi
	xorq	%r8, %rdi
	rolq	$3, %rdi
	movq	360(%rsp), %rbp
	xorq	%r10, %rbp
	rolq	$45, %rbp
	movq	408(%rsp), %rbx
	xorq	%r11, %rbx
	rolq	$61, %rbx
	andnq	%rdi, %rsi, %r12
	xorq	%rdx, %r12
	movq	%r12, 40(%rsp)
	andnq	%rbp, %rdi, %r12
	xorq	%rsi, %r12
	movq	%r12, 48(%rsp)
	andnq	%rbx, %rbp, %r12
	xorq	%rdi, %r12
	movq	%r12, 56(%rsp)
	andnq	%rdx, %rbx, %rdi
	xorq	%rbp, %rdi
	movq	%rdi, 64(%rsp)
	andnq	%rsi, %rdx, %rdx
	xorq	%rbx, %rdx
	movq	%rdx, 72(%rsp)
	movq	240(%rsp), %rdx
	xorq	%r10, %rdx
	rolq	$1, %rdx
	movq	288(%rsp), %rsi
	xorq	%r11, %rsi
	rolq	$6, %rsi
	movq	336(%rsp), %rdi
	xorq	%rcx, %rdi
	rolq	$25, %rdi
	movq	384(%rsp), %rbp
	xorq	%rax, %rbp
	rolq	$8, %rbp
	movq	392(%rsp), %rbx
	xorq	%r8, %rbx
	rolq	$18, %rbx
	andnq	%rdi, %rsi, %r12
	xorq	%rdx, %r12
	movq	%r12, 80(%rsp)
	andnq	%rbp, %rdi, %r12
	xorq	%rsi, %r12
	movq	%r12, 88(%rsp)
	andnq	%rbx, %rbp, %r12
	xorq	%rdi, %r12
	movq	%r12, 96(%rsp)
	andnq	%rdx, %rbx, %rdi
	xorq	%rbp, %rdi
	movq	%rdi, 104(%rsp)
	andnq	%rsi, %rdx, %rdx
	xorq	%rbx, %rdx
	movq	%rdx, 112(%rsp)
	movq	264(%rsp), %rdx
	xorq	%rax, %rdx
	rolq	$27, %rdx
	movq	272(%rsp), %rsi
	xorq	%r8, %rsi
	rolq	$36, %rsi
	movq	320(%rsp), %rdi
	xorq	%r10, %rdi
	rolq	$10, %rdi
	movq	368(%rsp), %rbp
	xorq	%r11, %rbp
	rolq	$15, %rbp
	movq	416(%rsp), %rbx
	xorq	%rcx, %rbx
	rolq	$56, %rbx
	andnq	%rdi, %rsi, %r12
	xorq	%rdx, %r12
	movq	%r12, 120(%rsp)
	andnq	%rbp, %rdi, %r12
	xorq	%rsi, %r12
	movq	%r12, 128(%rsp)
	andnq	%rbx, %rbp, %r12
	xorq	%rdi, %r12
	movq	%r12, 136(%rsp)
	andnq	%rdx, %rbx, %rdi
	xorq	%rbp, %rdi
	movq	%rdi, 144(%rsp)
	andnq	%rsi, %rdx, %rdx
	xorq	%rbx, %rdx
	movq	%rdx, 152(%rsp)
	movq	248(%rsp), %rdx
	xorq	%r11, %rdx
	rolq	$62, %rdx
	movq	296(%rsp), %rsi
	xorq	%rcx, %rsi
	rolq	$55, %rsi
	movq	%rsi, %rcx
	movq	344(%rsp), %rsi
	xorq	%rax, %rsi
	rolq	$39, %rsi
	movq	%rsi, %rax
	movq	352(%rsp), %rsi
	xorq	%r8, %rsi
	rolq	$41, %rsi
	movq	400(%rsp), %rdi
	xorq	%r10, %rdi
	rolq	$2, %rdi
	andnq	%rax, %rcx, %r8
	xorq	%rdx, %r8
	movq	%r8, 160(%rsp)
	andnq	%rsi, %rax, %r8
	xorq	%rcx, %r8
	movq	%r8, 168(%rsp)
	andnq	%rdi, %rsi, %r8
	xorq	%rax, %r8
	movq	%r8, 176(%rsp)
	andnq	%rdx, %rdi, %rax
	xorq	%rsi, %rax
	movq	%rax, 184(%rsp)
	andnq	%rcx, %rdx, %rax
	xorq	%rdi, %rax
	movq	%rax, 192(%rsp)
	leaq	16(%r9), %r9
	testb	$-1, %r9b
	jne 	Lkeccak_1600$5
	movq	200(%rsp), %rax
	movq	440(%rsp), %rcx
	movq	%rcx, %rdx
	shrq	$3, %rdx
	movq	$0, %rsi
	jmp 	Lkeccak_1600$3
Lkeccak_1600$4:
	movq	(%rsp,%rsi,8), %rdi
	movq	%rdi, (%rax,%rsi,8)
	leaq	1(%rsi), %rsi
Lkeccak_1600$3:
	cmpq	%rdx, %rsi
	jb  	Lkeccak_1600$4
	shlq	$3, %rsi
	jmp 	Lkeccak_1600$1
Lkeccak_1600$2:
	movb	(%rsp,%rsi), %dl
	movb	%dl, (%rax,%rsi)
	leaq	1(%rsi), %rsi
Lkeccak_1600$1:
	cmpq	%rcx, %rsi
	jb  	Lkeccak_1600$2
	addq	$456, %rsp
	popq	%r12
	popq	%rbx
	popq	%rbp
	ret 
