	.text
	.p2align	5
	.globl	_curve25519_ref4
	.globl	curve25519_ref4
_curve25519_ref4:
curve25519_ref4:
	pushq	%rbp
	pushq	%rbx
	pushq	%r12
	pushq	%r13
	pushq	%r14
	pushq	%r15
	subq	$488, %rsp
	movq	%rsi, 448(%rsp)
	movq	(%rsi), %rax
	movq	%rax, 456(%rsp)
	movq	8(%rsi), %rax
	movq	%rax, 464(%rsp)
	movq	16(%rsi), %rax
	movq	%rax, 472(%rsp)
	movq	24(%rsi), %rax
	movq	%rax, 480(%rsp)
	movq	(%rsi), %rax
	andq	$-8, %rax
	movq	8(%rsi), %rcx
	movq	16(%rsi), %r8
	movq	24(%rsi), %r9
	movq	$9223372036854775807, %r10
	andq	%r10, %r9
	movq	$4611686018427387904, %r10
	orq 	%r10, %r9
	movq	%rax, (%rsi)
	movq	%rcx, 8(%rsi)
	movq	%r8, 16(%rsi)
	movq	%r9, 24(%rsi)
	movq	(%rdx), %rax
	movq	%rax, 416(%rsp)
	movq	8(%rdx), %rax
	movq	%rax, 424(%rsp)
	movq	16(%rdx), %rax
	movq	%rax, 432(%rsp)
	movq	24(%rdx), %rax
	movq	$9223372036854775807, %rcx
	andq	%rcx, %rax
	movq	%rax, 440(%rsp)
	movq	416(%rsp), %rax
	movq	424(%rsp), %rcx
	movq	432(%rsp), %rdx
	movq	440(%rsp), %r8
	movq	%rax, 128(%rsp)
	movq	%rcx, 136(%rsp)
	movq	%rdx, 144(%rsp)
	movq	%r8, 152(%rsp)
	movq	%rax, 192(%rsp)
	movq	%rcx, 200(%rsp)
	movq	%rdx, 208(%rsp)
	movq	%r8, 216(%rsp)
	movq	$1, (%rsp)
	movq	$0, 8(%rsp)
	movq	$0, 16(%rsp)
	movq	$0, 24(%rsp)
	movq	$0, 64(%rsp)
	movq	$0, 72(%rsp)
	movq	$0, 80(%rsp)
	movq	$0, 88(%rsp)
	movq	$1, 160(%rsp)
	movq	$0, 168(%rsp)
	movq	$0, 176(%rsp)
	movq	$0, 184(%rsp)
	movq	$62, %rcx
	movq	$3, %rdx
	movq	$0, 384(%rsp)
Lcurve25519_ref4$8:
	movq	(%rsi,%rdx,8), %rax
	movq	%rdx, 408(%rsp)
	movq	%rax, 400(%rsp)
Lcurve25519_ref4$9:
	movq	400(%rsp), %rax
	shrq	%cl, %rax
	movq	%rcx, 392(%rsp)
	andq	$1, %rax
	movq	384(%rsp), %rcx
	xorq	%rax, %rcx
	movq	%rax, 384(%rsp)
	subq	$1, %rcx
	movq	64(%rsp), %rax
	movq	160(%rsp), %rcx
	movq	%rax, %rdx
	cmovnbq	%rcx, %rax
	cmovnbq	%rdx, %rcx
	movq	%rax, 64(%rsp)
	movq	%rcx, 160(%rsp)
	movq	72(%rsp), %rax
	movq	168(%rsp), %rcx
	movq	%rax, %rdx
	cmovnbq	%rcx, %rax
	cmovnbq	%rdx, %rcx
	movq	%rax, 72(%rsp)
	movq	%rcx, 168(%rsp)
	movq	80(%rsp), %rax
	movq	176(%rsp), %rcx
	movq	%rax, %rdx
	cmovnbq	%rcx, %rax
	cmovnbq	%rdx, %rcx
	movq	%rax, 80(%rsp)
	movq	%rcx, 176(%rsp)
	movq	88(%rsp), %rax
	movq	184(%rsp), %rcx
	movq	%rax, %rdx
	cmovnbq	%rcx, %rax
	cmovnbq	%rdx, %rcx
	movq	%rax, 88(%rsp)
	movq	%rcx, 184(%rsp)
	movq	(%rsp), %rax
	movq	192(%rsp), %rcx
	movq	%rax, %rdx
	cmovnbq	%rcx, %rax
	cmovnbq	%rdx, %rcx
	movq	%rcx, 192(%rsp)
	movq	8(%rsp), %rcx
	movq	200(%rsp), %rdx
	movq	%rcx, %r8
	cmovnbq	%rdx, %rcx
	cmovnbq	%r8, %rdx
	movq	%rdx, 200(%rsp)
	movq	16(%rsp), %rdx
	movq	208(%rsp), %r8
	movq	%rdx, %r9
	cmovnbq	%r8, %rdx
	cmovnbq	%r9, %r8
	movq	%r8, 208(%rsp)
	movq	24(%rsp), %r8
	movq	216(%rsp), %r9
	movq	%r8, %r10
	cmovnbq	%r9, %r8
	cmovnbq	%r10, %r9
	movq	%r9, 216(%rsp)
	movq	%rax, %r9
	movq	%rcx, %r10
	movq	%rdx, %r11
	movq	%r8, %rbp
	addq	64(%rsp), %rax
	adcq	72(%rsp), %rcx
	adcq	80(%rsp), %rdx
	adcq	88(%rsp), %r8
	movq	$0, %rbx
	movq	$38, %r12
	cmovnbq	%rbx, %r12
	addq	%r12, %rax
	adcq	%rbx, %rcx
	adcq	%rbx, %rdx
	adcq	%rbx, %r8
	cmovbq	%r12, %rbx
	addq	%rbx, %rax
	subq	64(%rsp), %r9
	sbbq	72(%rsp), %r10
	sbbq	80(%rsp), %r11
	sbbq	88(%rsp), %rbp
	movq	$0, %rbx
	movq	$38, %r12
	cmovnbq	%rbx, %r12
	subq	%r12, %r9
	sbbq	%rbx, %r10
	sbbq	%rbx, %r11
	sbbq	%rbx, %rbp
	cmovbq	%r12, %rbx
	subq	%rbx, %r9
	movq	%rax, 256(%rsp)
	movq	%rcx, 264(%rsp)
	movq	%rdx, 272(%rsp)
	movq	%r8, 280(%rsp)
	movq	%r9, 320(%rsp)
	movq	%r10, 328(%rsp)
	movq	%r11, 336(%rsp)
	movq	%rbp, 344(%rsp)
	movq	$0, %rcx
	movq	$0, %r8
	movq	328(%rsp), %rax
	mulq	320(%rsp)
	movq	%rax, %r9
	movq	%rdx, %r10
	movq	336(%rsp), %rax
	mulq	328(%rsp)
	movq	%rax, %r11
	movq	%rdx, %rbp
	movq	344(%rsp), %rax
	mulq	336(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %r12
	movq	336(%rsp), %rax
	mulq	320(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	%r8, %rbp
	movq	344(%rsp), %rax
	mulq	328(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	adcq	%r8, %r12
	movq	344(%rsp), %rax
	mulq	320(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	%r8, %rbx
	adcq	%r8, %r12
	adcq	%r8, %rcx
	addq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%rbx, %rbx
	adcq	%r12, %r12
	adcq	%rcx, %rcx
	movq	320(%rsp), %rax
	mulq	320(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r13
	movq	328(%rsp), %rax
	mulq	328(%rsp)
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	336(%rsp), %rax
	mulq	336(%rsp)
	addq	%r13, %r9
	adcq	%r14, %r10
	adcq	%r15, %r11
	adcq	%rax, %rbp
	adcq	%rdx, %rbx
	adcq	$0, %r12
	adcq	$0, %rcx
	movq	344(%rsp), %rax
	mulq	344(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %rcx
	movq	$38, %r13
	movq	%rbp, %rax
	mulq	__38(%rip)
	movq	%rax, %rbp
	movq	%rdx, %r14
	movq	%rbx, %rax
	mulq	__38(%rip)
	addq	%rax, %r14
	movq	$0, %rbx
	movq	%r12, %rax
	adcq	%rdx, %rbx
	mulq	%r13
	addq	%rax, %rbx
	movq	$0, %r12
	movq	%rcx, %rax
	adcq	%rdx, %r12
	mulq	%r13
	addq	%rax, %r12
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %rbp
	adcq	%r9, %r14
	adcq	%r10, %rbx
	adcq	%r11, %r12
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %rbp
	adcq	%rcx, %r14
	adcq	%rcx, %rbx
	adcq	%rcx, %r12
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %rbp
	movq	%rbp, 96(%rsp)
	movq	%r14, 104(%rsp)
	movq	%rbx, 112(%rsp)
	movq	%r12, 120(%rsp)
	movq	$0, %rcx
	movq	$0, %r8
	movq	264(%rsp), %rax
	mulq	256(%rsp)
	movq	%rax, %r9
	movq	%rdx, %r10
	movq	272(%rsp), %rax
	mulq	264(%rsp)
	movq	%rax, %r11
	movq	%rdx, %rbp
	movq	280(%rsp), %rax
	mulq	272(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %r12
	movq	272(%rsp), %rax
	mulq	256(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	%r8, %rbp
	movq	280(%rsp), %rax
	mulq	264(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	adcq	%r8, %r12
	movq	280(%rsp), %rax
	mulq	256(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	%r8, %rbx
	adcq	%r8, %r12
	adcq	%r8, %rcx
	addq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%rbx, %rbx
	adcq	%r12, %r12
	adcq	%rcx, %rcx
	movq	256(%rsp), %rax
	mulq	256(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r13
	movq	264(%rsp), %rax
	mulq	264(%rsp)
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	272(%rsp), %rax
	mulq	272(%rsp)
	addq	%r13, %r9
	adcq	%r14, %r10
	adcq	%r15, %r11
	adcq	%rax, %rbp
	adcq	%rdx, %rbx
	adcq	$0, %r12
	adcq	$0, %rcx
	movq	280(%rsp), %rax
	mulq	280(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %rcx
	movq	$38, %r13
	movq	%rbp, %rax
	mulq	__38(%rip)
	movq	%rax, %rbp
	movq	%rdx, %r14
	movq	%rbx, %rax
	mulq	__38(%rip)
	addq	%rax, %r14
	movq	$0, %rbx
	movq	%r12, %rax
	adcq	%rdx, %rbx
	mulq	%r13
	addq	%rax, %rbx
	movq	$0, %r12
	movq	%rcx, %rax
	adcq	%rdx, %r12
	mulq	%r13
	addq	%rax, %r12
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %rbp
	adcq	%r9, %r14
	adcq	%r10, %rbx
	adcq	%r11, %r12
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %rbp
	adcq	%rcx, %r14
	adcq	%rcx, %rbx
	adcq	%rcx, %r12
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %rbp
	movq	%rbp, 416(%rsp)
	movq	%r14, 424(%rsp)
	movq	%rbx, 432(%rsp)
	movq	%r12, 440(%rsp)
	movq	%rbp, %rax
	movq	%r14, %rcx
	movq	%rbx, %rdx
	movq	%r12, %r8
	subq	96(%rsp), %rax
	sbbq	104(%rsp), %rcx
	sbbq	112(%rsp), %rdx
	sbbq	120(%rsp), %r8
	movq	$0, %r9
	movq	$38, %r10
	cmovnbq	%r9, %r10
	subq	%r10, %rax
	sbbq	%r9, %rcx
	sbbq	%r9, %rdx
	sbbq	%r9, %r8
	cmovbq	%r10, %r9
	subq	%r9, %rax
	movq	%rax, 32(%rsp)
	movq	%rcx, 40(%rsp)
	movq	%rdx, 48(%rsp)
	movq	%r8, 56(%rsp)
	movq	192(%rsp), %rax
	movq	200(%rsp), %rcx
	movq	208(%rsp), %rdx
	movq	216(%rsp), %r8
	movq	%rax, %r9
	movq	%rcx, %r10
	movq	%rdx, %r11
	movq	%r8, %rbp
	addq	160(%rsp), %rax
	adcq	168(%rsp), %rcx
	adcq	176(%rsp), %rdx
	adcq	184(%rsp), %r8
	movq	$0, %rbx
	movq	$38, %r12
	cmovnbq	%rbx, %r12
	addq	%r12, %rax
	adcq	%rbx, %rcx
	adcq	%rbx, %rdx
	adcq	%rbx, %r8
	cmovbq	%r12, %rbx
	addq	%rbx, %rax
	subq	160(%rsp), %r9
	sbbq	168(%rsp), %r10
	sbbq	176(%rsp), %r11
	sbbq	184(%rsp), %rbp
	movq	$0, %rbx
	movq	$38, %r12
	cmovnbq	%rbx, %r12
	subq	%r12, %r9
	sbbq	%rbx, %r10
	sbbq	%rbx, %r11
	sbbq	%rbx, %rbp
	cmovbq	%r12, %rbx
	subq	%rbx, %r9
	movq	%rax, 352(%rsp)
	movq	%rcx, 360(%rsp)
	movq	%rdx, 368(%rsp)
	movq	%r8, 376(%rsp)
	movq	%r9, 288(%rsp)
	movq	%r10, 296(%rsp)
	movq	%r11, 304(%rsp)
	movq	%rbp, 312(%rsp)
	movq	$0, %rcx
	movq	$0, %r8
	movq	$0, %r9
	movq	$0, %r10
	movq	$0, %r11
	movq	$0, %rbp
	movq	352(%rsp), %rbx
	movq	320(%rsp), %rax
	mulq	%rbx
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	328(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r13
	adcq	%rdx, %rcx
	movq	336(%rsp), %rax
	mulq	%rbx
	addq	%rax, %rcx
	adcq	%rdx, %r8
	movq	344(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	360(%rsp), %rbx
	movq	320(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r13
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	328(%rsp), %rax
	mulq	%rbx
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r14, %rcx
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	336(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r14, %r8
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	344(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r14, %r9
	adcq	%rdx, %r10
	movq	368(%rsp), %rbx
	movq	320(%rsp), %rax
	mulq	%rbx
	addq	%rax, %rcx
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	328(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r14, %r8
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	336(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r14, %r9
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	344(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r14, %r10
	adcq	%rdx, %r11
	movq	376(%rsp), %rbx
	movq	320(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r8
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	328(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r14, %r9
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	336(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r14, %r10
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	344(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%r14, %r11
	adcq	%rdx, %rbp
	movq	$38, %rbx
	movq	%r9, %rax
	mulq	__38(%rip)
	movq	%rax, %r9
	movq	%rdx, %r14
	movq	%r10, %rax
	mulq	__38(%rip)
	addq	%rax, %r14
	movq	$0, %r10
	movq	%r11, %rax
	adcq	%rdx, %r10
	mulq	%rbx
	addq	%rax, %r10
	movq	$0, %r11
	movq	%rbp, %rax
	adcq	%rdx, %r11
	mulq	%rbx
	addq	%rax, %r11
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r12, %r9
	adcq	%r13, %r14
	adcq	%rcx, %r10
	adcq	%r8, %r11
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r9
	adcq	%rcx, %r14
	adcq	%rcx, %r10
	adcq	%rcx, %r11
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r9
	movq	%r9, 224(%rsp)
	movq	%r14, 232(%rsp)
	movq	%r10, 240(%rsp)
	movq	%r11, 248(%rsp)
	movq	$0, %rcx
	movq	$0, %r8
	movq	$0, %r9
	movq	$0, %r10
	movq	$0, %r11
	movq	$0, %rbp
	movq	288(%rsp), %rbx
	movq	256(%rsp), %rax
	mulq	%rbx
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	264(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r13
	adcq	%rdx, %rcx
	movq	272(%rsp), %rax
	mulq	%rbx
	addq	%rax, %rcx
	adcq	%rdx, %r8
	movq	280(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	296(%rsp), %rbx
	movq	256(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r13
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	264(%rsp), %rax
	mulq	%rbx
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r14, %rcx
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	272(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r14, %r8
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	280(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r14, %r9
	adcq	%rdx, %r10
	movq	304(%rsp), %rbx
	movq	256(%rsp), %rax
	mulq	%rbx
	addq	%rax, %rcx
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	264(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r14, %r8
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	272(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r14, %r9
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	280(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r14, %r10
	adcq	%rdx, %r11
	movq	312(%rsp), %rbx
	movq	256(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r8
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	264(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r14, %r9
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	272(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r14, %r10
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	280(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%r14, %r11
	adcq	%rdx, %rbp
	movq	$38, %rbx
	movq	%r9, %rax
	mulq	__38(%rip)
	movq	%rax, %r9
	movq	%rdx, %r14
	movq	%r10, %rax
	mulq	__38(%rip)
	addq	%rax, %r14
	movq	$0, %r10
	movq	%r11, %rax
	adcq	%rdx, %r10
	mulq	%rbx
	addq	%rax, %r10
	movq	$0, %r11
	movq	%rbp, %rax
	adcq	%rdx, %r11
	mulq	%rbx
	addq	%rax, %r11
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r12, %r9
	adcq	%r13, %r14
	adcq	%rcx, %r10
	adcq	%r8, %r11
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r9
	adcq	%rcx, %r14
	adcq	%rcx, %r10
	adcq	%rcx, %r11
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r9
	movq	%r9, %rax
	movq	%r14, %rcx
	movq	%r10, %rdx
	movq	%r11, %r8
	addq	224(%rsp), %rax
	adcq	232(%rsp), %rcx
	adcq	240(%rsp), %rdx
	adcq	248(%rsp), %r8
	movq	$0, %rbp
	movq	$38, %rbx
	cmovnbq	%rbp, %rbx
	addq	%rbx, %rax
	adcq	%rbp, %rcx
	adcq	%rbp, %rdx
	adcq	%rbp, %r8
	cmovbq	%rbx, %rbp
	addq	%rbp, %rax
	subq	224(%rsp), %r9
	sbbq	232(%rsp), %r14
	sbbq	240(%rsp), %r10
	sbbq	248(%rsp), %r11
	movq	$0, %rbp
	movq	$38, %rbx
	cmovnbq	%rbp, %rbx
	subq	%rbx, %r9
	sbbq	%rbp, %r14
	sbbq	%rbp, %r10
	sbbq	%rbp, %r11
	cmovbq	%rbx, %rbp
	subq	%rbp, %r9
	movq	%rax, 192(%rsp)
	movq	%rcx, 200(%rsp)
	movq	%rdx, 208(%rsp)
	movq	%r8, 216(%rsp)
	movq	%r9, 160(%rsp)
	movq	%r14, 168(%rsp)
	movq	%r10, 176(%rsp)
	movq	%r11, 184(%rsp)
	movq	$0, %rcx
	movq	$0, %r8
	movq	200(%rsp), %rax
	mulq	192(%rsp)
	movq	%rax, %r9
	movq	%rdx, %r10
	movq	208(%rsp), %rax
	mulq	200(%rsp)
	movq	%rax, %r11
	movq	%rdx, %rbp
	movq	216(%rsp), %rax
	mulq	208(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %r12
	movq	208(%rsp), %rax
	mulq	192(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	%r8, %rbp
	movq	216(%rsp), %rax
	mulq	200(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	adcq	%r8, %r12
	movq	216(%rsp), %rax
	mulq	192(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	%r8, %rbx
	adcq	%r8, %r12
	adcq	%r8, %rcx
	addq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%rbx, %rbx
	adcq	%r12, %r12
	adcq	%rcx, %rcx
	movq	192(%rsp), %rax
	mulq	192(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r13
	movq	200(%rsp), %rax
	mulq	200(%rsp)
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	208(%rsp), %rax
	mulq	208(%rsp)
	addq	%r13, %r9
	adcq	%r14, %r10
	adcq	%r15, %r11
	adcq	%rax, %rbp
	adcq	%rdx, %rbx
	adcq	$0, %r12
	adcq	$0, %rcx
	movq	216(%rsp), %rax
	mulq	216(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %rcx
	movq	$38, %r13
	movq	%rbp, %rax
	mulq	__38(%rip)
	movq	%rax, %rbp
	movq	%rdx, %r14
	movq	%rbx, %rax
	mulq	__38(%rip)
	addq	%rax, %r14
	movq	$0, %rbx
	movq	%r12, %rax
	adcq	%rdx, %rbx
	mulq	%r13
	addq	%rax, %rbx
	movq	$0, %r12
	movq	%rcx, %rax
	adcq	%rdx, %r12
	mulq	%r13
	addq	%rax, %r12
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %rbp
	adcq	%r9, %r14
	adcq	%r10, %rbx
	adcq	%r11, %r12
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %rbp
	adcq	%rcx, %r14
	adcq	%rcx, %rbx
	adcq	%rcx, %r12
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %rbp
	movq	%rbp, 192(%rsp)
	movq	%r14, 200(%rsp)
	movq	%rbx, 208(%rsp)
	movq	%r12, 216(%rsp)
	movq	$0, %rcx
	movq	$0, %r8
	movq	168(%rsp), %rax
	mulq	160(%rsp)
	movq	%rax, %r9
	movq	%rdx, %r10
	movq	176(%rsp), %rax
	mulq	168(%rsp)
	movq	%rax, %r11
	movq	%rdx, %rbp
	movq	184(%rsp), %rax
	mulq	176(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %r12
	movq	176(%rsp), %rax
	mulq	160(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	%r8, %rbp
	movq	184(%rsp), %rax
	mulq	168(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rbx
	adcq	%r8, %r12
	movq	184(%rsp), %rax
	mulq	160(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	%r8, %rbx
	adcq	%r8, %r12
	adcq	%r8, %rcx
	addq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%rbx, %rbx
	adcq	%r12, %r12
	adcq	%rcx, %rcx
	movq	160(%rsp), %rax
	mulq	160(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r13
	movq	168(%rsp), %rax
	mulq	168(%rsp)
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	176(%rsp), %rax
	mulq	176(%rsp)
	addq	%r13, %r9
	adcq	%r14, %r10
	adcq	%r15, %r11
	adcq	%rax, %rbp
	adcq	%rdx, %rbx
	adcq	$0, %r12
	adcq	$0, %rcx
	movq	184(%rsp), %rax
	mulq	184(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %rcx
	movq	$38, %r13
	movq	%rbp, %rax
	mulq	__38(%rip)
	movq	%rax, %rbp
	movq	%rdx, %r14
	movq	%rbx, %rax
	mulq	__38(%rip)
	addq	%rax, %r14
	movq	$0, %rbx
	movq	%r12, %rax
	adcq	%rdx, %rbx
	mulq	%r13
	addq	%rax, %rbx
	movq	$0, %r12
	movq	%rcx, %rax
	adcq	%rdx, %r12
	mulq	%r13
	addq	%rax, %r12
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r8, %rbp
	adcq	%r9, %r14
	adcq	%r10, %rbx
	adcq	%r11, %r12
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %rbp
	adcq	%rcx, %r14
	adcq	%rcx, %rbx
	adcq	%rcx, %r12
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %rbp
	movq	%rbp, 160(%rsp)
	movq	%r14, 168(%rsp)
	movq	%rbx, 176(%rsp)
	movq	%r12, 184(%rsp)
	movq	$0, %rcx
	movq	$0, %r8
	movq	$0, %r9
	movq	$0, %r10
	movq	$0, %r11
	movq	$0, %rbp
	movq	160(%rsp), %rbx
	movq	128(%rsp), %rax
	mulq	%rbx
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	136(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r13
	adcq	%rdx, %rcx
	movq	144(%rsp), %rax
	mulq	%rbx
	addq	%rax, %rcx
	adcq	%rdx, %r8
	movq	152(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	168(%rsp), %rbx
	movq	128(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r13
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	136(%rsp), %rax
	mulq	%rbx
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r14, %rcx
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	144(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r14, %r8
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	152(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r14, %r9
	adcq	%rdx, %r10
	movq	176(%rsp), %rbx
	movq	128(%rsp), %rax
	mulq	%rbx
	addq	%rax, %rcx
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	136(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r14, %r8
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	144(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r14, %r9
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	152(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r14, %r10
	adcq	%rdx, %r11
	movq	184(%rsp), %rbx
	movq	128(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r8
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	136(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r14, %r9
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	144(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r14, %r10
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	152(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%r14, %r11
	adcq	%rdx, %rbp
	movq	$38, %rbx
	movq	%r9, %rax
	mulq	__38(%rip)
	movq	%rax, %r9
	movq	%rdx, %r14
	movq	%r10, %rax
	mulq	__38(%rip)
	addq	%rax, %r14
	movq	$0, %r10
	movq	%r11, %rax
	adcq	%rdx, %r10
	mulq	%rbx
	addq	%rax, %r10
	movq	$0, %r11
	movq	%rbp, %rax
	adcq	%rdx, %r11
	mulq	%rbx
	addq	%rax, %r11
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r12, %r9
	adcq	%r13, %r14
	adcq	%rcx, %r10
	adcq	%r8, %r11
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r9
	adcq	%rcx, %r14
	adcq	%rcx, %r10
	adcq	%rcx, %r11
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r9
	movq	%r9, 160(%rsp)
	movq	%r14, 168(%rsp)
	movq	%r10, 176(%rsp)
	movq	%r11, 184(%rsp)
	movq	$121666, %rcx
	movq	32(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	48(%rsp), %rax
	mulq	%rcx
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	40(%rsp), %rax
	mulq	%rcx
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	56(%rsp), %rax
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rdx, %rax
	addq	%rbp, %r9
	adcq	%rbx, %r10
	adcq	%rcx, %r11
	adcq	$0, %rax
	movq	$38, %rcx
	mulq	%rcx
	addq	%rax, %r8
	adcq	$0, %r9
	adcq	$0, %r10
	adcq	$0, %r11
	movq	$38, %rax
	movq	$0, %rcx
	cmovnbq	%rcx, %rax
	addq	%rax, %r8
	addq	96(%rsp), %r8
	adcq	104(%rsp), %r9
	adcq	112(%rsp), %r10
	adcq	120(%rsp), %r11
	movq	$0, %rax
	movq	$38, %rcx
	cmovnbq	%rax, %rcx
	addq	%rcx, %r8
	adcq	%rax, %r9
	adcq	%rax, %r10
	adcq	%rax, %r11
	cmovbq	%rcx, %rax
	addq	%rax, %r8
	movq	%r8, 64(%rsp)
	movq	%r9, 72(%rsp)
	movq	%r10, 80(%rsp)
	movq	%r11, 88(%rsp)
	movq	$0, %rcx
	movq	$0, %r8
	movq	$0, %r9
	movq	$0, %r10
	movq	$0, %r11
	movq	$0, %rbp
	movq	64(%rsp), %rbx
	movq	32(%rsp), %rax
	mulq	%rbx
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	40(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r13
	adcq	%rdx, %rcx
	movq	48(%rsp), %rax
	mulq	%rbx
	addq	%rax, %rcx
	adcq	%rdx, %r8
	movq	56(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	72(%rsp), %rbx
	movq	32(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r13
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	40(%rsp), %rax
	mulq	%rbx
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r14, %rcx
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	48(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r14, %r8
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	56(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r14, %r9
	adcq	%rdx, %r10
	movq	80(%rsp), %rbx
	movq	32(%rsp), %rax
	mulq	%rbx
	addq	%rax, %rcx
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	40(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r14, %r8
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	48(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r14, %r9
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	56(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r14, %r10
	adcq	%rdx, %r11
	movq	88(%rsp), %rbx
	movq	32(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r8
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	40(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r14, %r9
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	48(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r14, %r10
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	56(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%r14, %r11
	adcq	%rdx, %rbp
	movq	$38, %rbx
	movq	%r9, %rax
	mulq	__38(%rip)
	movq	%rax, %r9
	movq	%rdx, %r14
	movq	%r10, %rax
	mulq	__38(%rip)
	addq	%rax, %r14
	movq	$0, %r10
	movq	%r11, %rax
	adcq	%rdx, %r10
	mulq	%rbx
	addq	%rax, %r10
	movq	$0, %r11
	movq	%rbp, %rax
	adcq	%rdx, %r11
	mulq	%rbx
	addq	%rax, %r11
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r12, %r9
	adcq	%r13, %r14
	adcq	%rcx, %r10
	adcq	%r8, %r11
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r9
	adcq	%rcx, %r14
	adcq	%rcx, %r10
	adcq	%rcx, %r11
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r9
	movq	%r9, 64(%rsp)
	movq	%r14, 72(%rsp)
	movq	%r10, 80(%rsp)
	movq	%r11, 88(%rsp)
	movq	$0, %rcx
	movq	$0, %r8
	movq	$0, %r9
	movq	$0, %r10
	movq	$0, %r11
	movq	$0, %rbp
	movq	416(%rsp), %rbx
	movq	96(%rsp), %rax
	mulq	%rbx
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	104(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r13
	adcq	%rdx, %rcx
	movq	112(%rsp), %rax
	mulq	%rbx
	addq	%rax, %rcx
	adcq	%rdx, %r8
	movq	120(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	424(%rsp), %rbx
	movq	96(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r13
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	104(%rsp), %rax
	mulq	%rbx
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r14, %rcx
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	112(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r14, %r8
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	120(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r14, %r9
	adcq	%rdx, %r10
	movq	432(%rsp), %rbx
	movq	96(%rsp), %rax
	mulq	%rbx
	addq	%rax, %rcx
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	104(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r14, %r8
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	112(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r14, %r9
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	120(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r14, %r10
	adcq	%rdx, %r11
	movq	440(%rsp), %rbx
	movq	96(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r8
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	104(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r14, %r9
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	112(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r14, %r10
	movq	$0, %r14
	adcq	%rdx, %r14
	movq	120(%rsp), %rax
	mulq	%rbx
	addq	%rax, %r11
	adcq	$0, %rdx
	addq	%r14, %r11
	adcq	%rdx, %rbp
	movq	$38, %rbx
	movq	%r9, %rax
	mulq	__38(%rip)
	movq	%rax, %r9
	movq	%rdx, %r14
	movq	%r10, %rax
	mulq	__38(%rip)
	addq	%rax, %r14
	movq	$0, %r10
	movq	%r11, %rax
	adcq	%rdx, %r10
	mulq	%rbx
	addq	%rax, %r10
	movq	$0, %r11
	movq	%rbp, %rax
	adcq	%rdx, %r11
	mulq	%rbx
	addq	%rax, %r11
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%r12, %r9
	adcq	%r13, %r14
	adcq	%rcx, %r10
	adcq	%r8, %r11
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r9
	adcq	%rcx, %r14
	adcq	%rcx, %r10
	adcq	%rcx, %r11
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r9
	movq	%r9, (%rsp)
	movq	%r14, 8(%rsp)
	movq	%r10, 16(%rsp)
	movq	%r11, 24(%rsp)
	movq	392(%rsp), %rcx
	addq	$-1, %rcx
	cmpq	$0, %rcx
	jnl 	Lcurve25519_ref4$9
	movq	$63, %rcx
	movq	408(%rsp), %rdx
	addq	$-1, %rdx
	cmpq	$0, %rdx
	jnl 	Lcurve25519_ref4$8
	movq	$0, %rcx
	movq	$0, %rsi
	movq	72(%rsp), %rax
	mulq	64(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	80(%rsp), %rax
	mulq	72(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	88(%rsp), %rax
	mulq	80(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	80(%rsp), %rax
	mulq	64(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	%rsi, %r11
	movq	88(%rsp), %rax
	mulq	72(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	%rsi, %rbx
	movq	88(%rsp), %rax
	mulq	64(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	%rsi, %rbp
	adcq	%rsi, %rbx
	adcq	%rsi, %rcx
	addq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%rbx, %rbx
	adcq	%rcx, %rcx
	movq	64(%rsp), %rax
	mulq	64(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %r12
	movq	72(%rsp), %rax
	mulq	72(%rsp)
	movq	%rax, %r13
	movq	%rdx, %r14
	movq	80(%rsp), %rax
	mulq	80(%rsp)
	addq	%r12, %r8
	adcq	%r13, %r9
	adcq	%r14, %r10
	adcq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %rbx
	adcq	$0, %rcx
	movq	88(%rsp), %rax
	mulq	88(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %rcx
	movq	$38, %r12
	movq	%r11, %rax
	mulq	__38(%rip)
	movq	%rax, %r11
	movq	%rdx, %r13
	movq	%rbp, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %rbp
	movq	%rbx, %rax
	adcq	%rdx, %rbp
	mulq	%r12
	addq	%rax, %rbp
	movq	$0, %rbx
	movq	%rcx, %rax
	adcq	%rdx, %rbx
	mulq	%r12
	addq	%rax, %rbx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rsi, %r11
	adcq	%r8, %r13
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r11
	adcq	%rcx, %r13
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r11
	movq	%r11, 416(%rsp)
	movq	%r13, 424(%rsp)
	movq	%rbp, 432(%rsp)
	movq	%rbx, 440(%rsp)
	movq	$0, %rcx
	movq	$0, %rsi
	movq	424(%rsp), %rax
	mulq	416(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	432(%rsp), %rax
	mulq	424(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	440(%rsp), %rax
	mulq	432(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	432(%rsp), %rax
	mulq	416(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	%rsi, %r11
	movq	440(%rsp), %rax
	mulq	424(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	%rsi, %rbx
	movq	440(%rsp), %rax
	mulq	416(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	%rsi, %rbp
	adcq	%rsi, %rbx
	adcq	%rsi, %rcx
	addq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%rbx, %rbx
	adcq	%rcx, %rcx
	movq	416(%rsp), %rax
	mulq	416(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %r12
	movq	424(%rsp), %rax
	mulq	424(%rsp)
	movq	%rax, %r13
	movq	%rdx, %r14
	movq	432(%rsp), %rax
	mulq	432(%rsp)
	addq	%r12, %r8
	adcq	%r13, %r9
	adcq	%r14, %r10
	adcq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %rbx
	adcq	$0, %rcx
	movq	440(%rsp), %rax
	mulq	440(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %rcx
	movq	$38, %r12
	movq	%r11, %rax
	mulq	__38(%rip)
	movq	%rax, %r11
	movq	%rdx, %r13
	movq	%rbp, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %rbp
	movq	%rbx, %rax
	adcq	%rdx, %rbp
	mulq	%r12
	addq	%rax, %rbp
	movq	$0, %rbx
	movq	%rcx, %rax
	adcq	%rdx, %rbx
	mulq	%r12
	addq	%rax, %rbx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rsi, %r11
	adcq	%r8, %r13
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r11
	adcq	%rcx, %r13
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r11
	movq	%r11, 160(%rsp)
	movq	%r13, 168(%rsp)
	movq	%rbp, 176(%rsp)
	movq	%rbx, 184(%rsp)
	movq	$0, %rcx
	movq	$0, %rsi
	movq	168(%rsp), %rax
	mulq	160(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	176(%rsp), %rax
	mulq	168(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	184(%rsp), %rax
	mulq	176(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	176(%rsp), %rax
	mulq	160(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	%rsi, %r11
	movq	184(%rsp), %rax
	mulq	168(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	%rsi, %rbx
	movq	184(%rsp), %rax
	mulq	160(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	%rsi, %rbp
	adcq	%rsi, %rbx
	adcq	%rsi, %rcx
	addq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%rbx, %rbx
	adcq	%rcx, %rcx
	movq	160(%rsp), %rax
	mulq	160(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %r12
	movq	168(%rsp), %rax
	mulq	168(%rsp)
	movq	%rax, %r13
	movq	%rdx, %r14
	movq	176(%rsp), %rax
	mulq	176(%rsp)
	addq	%r12, %r8
	adcq	%r13, %r9
	adcq	%r14, %r10
	adcq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %rbx
	adcq	$0, %rcx
	movq	184(%rsp), %rax
	mulq	184(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %rcx
	movq	$38, %r12
	movq	%r11, %rax
	mulq	__38(%rip)
	movq	%rax, %r11
	movq	%rdx, %r13
	movq	%rbp, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %rbp
	movq	%rbx, %rax
	adcq	%rdx, %rbp
	mulq	%r12
	addq	%rax, %rbp
	movq	$0, %rbx
	movq	%rcx, %rax
	adcq	%rdx, %rbx
	mulq	%r12
	addq	%rax, %rbx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rsi, %r11
	adcq	%r8, %r13
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r11
	adcq	%rcx, %r13
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r11
	movq	%r11, 160(%rsp)
	movq	%r13, 168(%rsp)
	movq	%rbp, 176(%rsp)
	movq	%rbx, 184(%rsp)
	movq	$0, %rcx
	movq	$0, %rsi
	movq	$0, %r8
	movq	$0, %r9
	movq	$0, %r10
	movq	$0, %r11
	movq	160(%rsp), %rbp
	movq	64(%rsp), %rax
	mulq	%rbp
	movq	%rax, %rbx
	movq	%rdx, %r12
	movq	72(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r12
	adcq	%rdx, %rcx
	movq	80(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	88(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	%rdx, %r8
	movq	168(%rsp), %rbp
	movq	64(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r12
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	72(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r13, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	80(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	88(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	adcq	%rdx, %r9
	movq	176(%rsp), %rbp
	movq	64(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	72(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	80(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	88(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r13, %r9
	adcq	%rdx, %r10
	movq	184(%rsp), %rbp
	movq	64(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	72(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	80(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r13, %r9
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	88(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r13, %r10
	adcq	%rdx, %r11
	movq	$38, %rbp
	movq	%r8, %rax
	mulq	__38(%rip)
	movq	%rax, %r8
	movq	%rdx, %r13
	movq	%r9, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %r9
	movq	%r10, %rax
	adcq	%rdx, %r9
	mulq	%rbp
	addq	%rax, %r9
	movq	$0, %r10
	movq	%r11, %rax
	adcq	%rdx, %r10
	mulq	%rbp
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rbx, %r8
	adcq	%r12, %r13
	adcq	%rcx, %r9
	adcq	%rsi, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r8
	adcq	%rcx, %r13
	adcq	%rcx, %r9
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r8
	movq	%r8, 352(%rsp)
	movq	%r13, 360(%rsp)
	movq	%r9, 368(%rsp)
	movq	%r10, 376(%rsp)
	movq	$0, %rcx
	movq	$0, %rsi
	movq	$0, %r8
	movq	$0, %r9
	movq	$0, %r10
	movq	$0, %r11
	movq	352(%rsp), %rbp
	movq	416(%rsp), %rax
	mulq	%rbp
	movq	%rax, %rbx
	movq	%rdx, %r12
	movq	424(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r12
	adcq	%rdx, %rcx
	movq	432(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	440(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	%rdx, %r8
	movq	360(%rsp), %rbp
	movq	416(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r12
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	424(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r13, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	432(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	440(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	adcq	%rdx, %r9
	movq	368(%rsp), %rbp
	movq	416(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	424(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	432(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	440(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r13, %r9
	adcq	%rdx, %r10
	movq	376(%rsp), %rbp
	movq	416(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	424(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	432(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r13, %r9
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	440(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r13, %r10
	adcq	%rdx, %r11
	movq	$38, %rbp
	movq	%r8, %rax
	mulq	__38(%rip)
	movq	%rax, %r8
	movq	%rdx, %r13
	movq	%r9, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %r9
	movq	%r10, %rax
	adcq	%rdx, %r9
	mulq	%rbp
	addq	%rax, %r9
	movq	$0, %r10
	movq	%r11, %rax
	adcq	%rdx, %r10
	mulq	%rbp
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rbx, %r8
	adcq	%r12, %r13
	adcq	%rcx, %r9
	adcq	%rsi, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r8
	adcq	%rcx, %r13
	adcq	%rcx, %r9
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r8
	movq	%r8, 128(%rsp)
	movq	%r13, 136(%rsp)
	movq	%r9, 144(%rsp)
	movq	%r10, 152(%rsp)
	movq	$0, %rcx
	movq	$0, %rsi
	movq	136(%rsp), %rax
	mulq	128(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	144(%rsp), %rax
	mulq	136(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	152(%rsp), %rax
	mulq	144(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	144(%rsp), %rax
	mulq	128(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	%rsi, %r11
	movq	152(%rsp), %rax
	mulq	136(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	%rsi, %rbx
	movq	152(%rsp), %rax
	mulq	128(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	%rsi, %rbp
	adcq	%rsi, %rbx
	adcq	%rsi, %rcx
	addq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%rbx, %rbx
	adcq	%rcx, %rcx
	movq	128(%rsp), %rax
	mulq	128(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %r12
	movq	136(%rsp), %rax
	mulq	136(%rsp)
	movq	%rax, %r13
	movq	%rdx, %r14
	movq	144(%rsp), %rax
	mulq	144(%rsp)
	addq	%r12, %r8
	adcq	%r13, %r9
	adcq	%r14, %r10
	adcq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %rbx
	adcq	$0, %rcx
	movq	152(%rsp), %rax
	mulq	152(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %rcx
	movq	$38, %r12
	movq	%r11, %rax
	mulq	__38(%rip)
	movq	%rax, %r11
	movq	%rdx, %r13
	movq	%rbp, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %rbp
	movq	%rbx, %rax
	adcq	%rdx, %rbp
	mulq	%r12
	addq	%rax, %rbp
	movq	$0, %rbx
	movq	%rcx, %rax
	adcq	%rdx, %rbx
	mulq	%r12
	addq	%rax, %rbx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rsi, %r11
	adcq	%r8, %r13
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r11
	adcq	%rcx, %r13
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r11
	movq	%r11, 160(%rsp)
	movq	%r13, 168(%rsp)
	movq	%rbp, 176(%rsp)
	movq	%rbx, 184(%rsp)
	movq	$0, %rcx
	movq	$0, %rsi
	movq	$0, %r8
	movq	$0, %r9
	movq	$0, %r10
	movq	$0, %r11
	movq	160(%rsp), %rbp
	movq	352(%rsp), %rax
	mulq	%rbp
	movq	%rax, %rbx
	movq	%rdx, %r12
	movq	360(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r12
	adcq	%rdx, %rcx
	movq	368(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	376(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	%rdx, %r8
	movq	168(%rsp), %rbp
	movq	352(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r12
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	360(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r13, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	368(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	376(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	adcq	%rdx, %r9
	movq	176(%rsp), %rbp
	movq	352(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	360(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	368(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	376(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r13, %r9
	adcq	%rdx, %r10
	movq	184(%rsp), %rbp
	movq	352(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	360(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	368(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r13, %r9
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	376(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r13, %r10
	adcq	%rdx, %r11
	movq	$38, %rbp
	movq	%r8, %rax
	mulq	__38(%rip)
	movq	%rax, %r8
	movq	%rdx, %r13
	movq	%r9, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %r9
	movq	%r10, %rax
	adcq	%rdx, %r9
	mulq	%rbp
	addq	%rax, %r9
	movq	$0, %r10
	movq	%r11, %rax
	adcq	%rdx, %r10
	mulq	%rbp
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rbx, %r8
	adcq	%r12, %r13
	adcq	%rcx, %r9
	adcq	%rsi, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r8
	adcq	%rcx, %r13
	adcq	%rcx, %r9
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r8
	movq	%r8, 320(%rsp)
	movq	%r13, 328(%rsp)
	movq	%r9, 336(%rsp)
	movq	%r10, 344(%rsp)
	movq	$0, %rcx
	movq	$0, %rsi
	movq	328(%rsp), %rax
	mulq	320(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	336(%rsp), %rax
	mulq	328(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	344(%rsp), %rax
	mulq	336(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	336(%rsp), %rax
	mulq	320(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	%rsi, %r11
	movq	344(%rsp), %rax
	mulq	328(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	%rsi, %rbx
	movq	344(%rsp), %rax
	mulq	320(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	%rsi, %rbp
	adcq	%rsi, %rbx
	adcq	%rsi, %rcx
	addq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%rbx, %rbx
	adcq	%rcx, %rcx
	movq	320(%rsp), %rax
	mulq	320(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %r12
	movq	328(%rsp), %rax
	mulq	328(%rsp)
	movq	%rax, %r13
	movq	%rdx, %r14
	movq	336(%rsp), %rax
	mulq	336(%rsp)
	addq	%r12, %r8
	adcq	%r13, %r9
	adcq	%r14, %r10
	adcq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %rbx
	adcq	$0, %rcx
	movq	344(%rsp), %rax
	mulq	344(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %rcx
	movq	$38, %r12
	movq	%r11, %rax
	mulq	__38(%rip)
	movq	%rax, %r11
	movq	%rdx, %r13
	movq	%rbp, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %rbp
	movq	%rbx, %rax
	adcq	%rdx, %rbp
	mulq	%r12
	addq	%rax, %rbp
	movq	$0, %rbx
	movq	%rcx, %rax
	adcq	%rdx, %rbx
	mulq	%r12
	addq	%rax, %rbx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rsi, %r11
	adcq	%r8, %r13
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r11
	adcq	%rcx, %r13
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r11
	movq	%r11, 160(%rsp)
	movq	%r13, 168(%rsp)
	movq	%rbp, 176(%rsp)
	movq	%rbx, 184(%rsp)
	movq	$3, 408(%rsp)
Lcurve25519_ref4$7:
	movq	160(%rsp), %rcx
	movq	168(%rsp), %rsi
	movq	176(%rsp), %r8
	movq	%rsi, %rax
	mulq	%rcx
	movq	%rax, %r9
	movq	%rdx, %r10
	movq	%r8, %rax
	mulq	%rsi
	movq	%rax, %r11
	movq	%rdx, %rbp
	movq	184(%rsp), %rax
	mulq	%r8
	movq	%rax, %r8
	movq	%rdx, %rbx
	movq	$0, %r12
	movq	176(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	$0, %rbp
	movq	184(%rsp), %rax
	mulq	%rsi
	addq	%rax, %rbp
	adcq	%rdx, %r8
	adcq	$0, %rbx
	movq	184(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %r8
	adcq	$0, %rbx
	adcq	$0, %r12
	addq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%r8, %r8
	adcq	%rbx, %rbx
	adcq	%r12, %r12
	movq	%rcx, %rax
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rdx, %r13
	movq	%rsi, %rax
	mulq	%rsi
	movq	%rax, %rsi
	movq	%rdx, %r14
	movq	176(%rsp), %rax
	mulq	176(%rsp)
	addq	%r13, %r9
	adcq	%rsi, %r10
	adcq	%r14, %r11
	adcq	%rax, %rbp
	adcq	%rdx, %r8
	adcq	$0, %rbx
	adcq	$0, %r12
	movq	184(%rsp), %rax
	mulq	184(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r12
	movq	$38, %rsi
	movq	%rbp, %rax
	mulq	__38(%rip)
	movq	%rax, %rbp
	movq	%rdx, %r13
	movq	%r8, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %r8
	movq	%rbx, %rax
	adcq	%rdx, %r8
	mulq	%rsi
	addq	%rax, %r8
	movq	$0, %rbx
	movq	%r12, %rax
	adcq	%rdx, %rbx
	mulq	%rsi
	addq	%rax, %rbx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %rbp
	adcq	%r9, %r13
	adcq	%r10, %r8
	adcq	%r11, %rbx
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %rbp
	adcq	%rcx, %r13
	adcq	%rcx, %r8
	adcq	%rcx, %rbx
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %rbp
	movq	%rbp, 160(%rsp)
	movq	%r13, 168(%rsp)
	movq	%r8, 176(%rsp)
	movq	%rbx, 184(%rsp)
	movq	408(%rsp), %rax
	subq	$1, %rax
	movq	%rax, 408(%rsp)
	jnb 	Lcurve25519_ref4$7
	movq	$0, %rcx
	movq	$0, %rsi
	movq	$0, %r8
	movq	$0, %r9
	movq	$0, %r10
	movq	$0, %r11
	movq	160(%rsp), %rbp
	movq	320(%rsp), %rax
	mulq	%rbp
	movq	%rax, %rbx
	movq	%rdx, %r12
	movq	328(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r12
	adcq	%rdx, %rcx
	movq	336(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	344(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	%rdx, %r8
	movq	168(%rsp), %rbp
	movq	320(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r12
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	328(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r13, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	336(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	344(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	adcq	%rdx, %r9
	movq	176(%rsp), %rbp
	movq	320(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	328(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	336(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	344(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r13, %r9
	adcq	%rdx, %r10
	movq	184(%rsp), %rbp
	movq	320(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	328(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	336(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r13, %r9
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	344(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r13, %r10
	adcq	%rdx, %r11
	movq	$38, %rbp
	movq	%r8, %rax
	mulq	__38(%rip)
	movq	%rax, %r8
	movq	%rdx, %r13
	movq	%r9, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %r9
	movq	%r10, %rax
	adcq	%rdx, %r9
	mulq	%rbp
	addq	%rax, %r9
	movq	$0, %r10
	movq	%r11, %rax
	adcq	%rdx, %r10
	mulq	%rbp
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rbx, %r8
	adcq	%r12, %r13
	adcq	%rcx, %r9
	adcq	%rsi, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r8
	adcq	%rcx, %r13
	adcq	%rcx, %r9
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r8
	movq	%r8, 256(%rsp)
	movq	%r13, 264(%rsp)
	movq	%r9, 272(%rsp)
	movq	%r10, 280(%rsp)
	movq	$0, %rcx
	movq	$0, %rsi
	movq	264(%rsp), %rax
	mulq	256(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	272(%rsp), %rax
	mulq	264(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	280(%rsp), %rax
	mulq	272(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	272(%rsp), %rax
	mulq	256(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	%rsi, %r11
	movq	280(%rsp), %rax
	mulq	264(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	%rsi, %rbx
	movq	280(%rsp), %rax
	mulq	256(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	%rsi, %rbp
	adcq	%rsi, %rbx
	adcq	%rsi, %rcx
	addq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%rbx, %rbx
	adcq	%rcx, %rcx
	movq	256(%rsp), %rax
	mulq	256(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %r12
	movq	264(%rsp), %rax
	mulq	264(%rsp)
	movq	%rax, %r13
	movq	%rdx, %r14
	movq	272(%rsp), %rax
	mulq	272(%rsp)
	addq	%r12, %r8
	adcq	%r13, %r9
	adcq	%r14, %r10
	adcq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %rbx
	adcq	$0, %rcx
	movq	280(%rsp), %rax
	mulq	280(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %rcx
	movq	$38, %r12
	movq	%r11, %rax
	mulq	__38(%rip)
	movq	%rax, %r11
	movq	%rdx, %r13
	movq	%rbp, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %rbp
	movq	%rbx, %rax
	adcq	%rdx, %rbp
	mulq	%r12
	addq	%rax, %rbp
	movq	$0, %rbx
	movq	%rcx, %rax
	adcq	%rdx, %rbx
	mulq	%r12
	addq	%rax, %rbx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rsi, %r11
	adcq	%r8, %r13
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r11
	adcq	%rcx, %r13
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r11
	movq	%r11, 160(%rsp)
	movq	%r13, 168(%rsp)
	movq	%rbp, 176(%rsp)
	movq	%rbx, 184(%rsp)
	movq	$8, 408(%rsp)
Lcurve25519_ref4$6:
	movq	160(%rsp), %rcx
	movq	168(%rsp), %rsi
	movq	176(%rsp), %r8
	movq	%rsi, %rax
	mulq	%rcx
	movq	%rax, %r9
	movq	%rdx, %r10
	movq	%r8, %rax
	mulq	%rsi
	movq	%rax, %r11
	movq	%rdx, %rbp
	movq	184(%rsp), %rax
	mulq	%r8
	movq	%rax, %r8
	movq	%rdx, %rbx
	movq	$0, %r12
	movq	176(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	$0, %rbp
	movq	184(%rsp), %rax
	mulq	%rsi
	addq	%rax, %rbp
	adcq	%rdx, %r8
	adcq	$0, %rbx
	movq	184(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %r8
	adcq	$0, %rbx
	adcq	$0, %r12
	addq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%r8, %r8
	adcq	%rbx, %rbx
	adcq	%r12, %r12
	movq	%rcx, %rax
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rdx, %r13
	movq	%rsi, %rax
	mulq	%rsi
	movq	%rax, %rsi
	movq	%rdx, %r14
	movq	176(%rsp), %rax
	mulq	176(%rsp)
	addq	%r13, %r9
	adcq	%rsi, %r10
	adcq	%r14, %r11
	adcq	%rax, %rbp
	adcq	%rdx, %r8
	adcq	$0, %rbx
	adcq	$0, %r12
	movq	184(%rsp), %rax
	mulq	184(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r12
	movq	$38, %rsi
	movq	%rbp, %rax
	mulq	__38(%rip)
	movq	%rax, %rbp
	movq	%rdx, %r13
	movq	%r8, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %r8
	movq	%rbx, %rax
	adcq	%rdx, %r8
	mulq	%rsi
	addq	%rax, %r8
	movq	$0, %rbx
	movq	%r12, %rax
	adcq	%rdx, %rbx
	mulq	%rsi
	addq	%rax, %rbx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %rbp
	adcq	%r9, %r13
	adcq	%r10, %r8
	adcq	%r11, %rbx
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %rbp
	adcq	%rcx, %r13
	adcq	%rcx, %r8
	adcq	%rcx, %rbx
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %rbp
	movq	%rbp, 160(%rsp)
	movq	%r13, 168(%rsp)
	movq	%r8, 176(%rsp)
	movq	%rbx, 184(%rsp)
	movq	408(%rsp), %rax
	subq	$1, %rax
	movq	%rax, 408(%rsp)
	jnb 	Lcurve25519_ref4$6
	movq	$0, %rcx
	movq	$0, %rsi
	movq	$0, %r8
	movq	$0, %r9
	movq	$0, %r10
	movq	$0, %r11
	movq	160(%rsp), %rbp
	movq	256(%rsp), %rax
	mulq	%rbp
	movq	%rax, %rbx
	movq	%rdx, %r12
	movq	264(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r12
	adcq	%rdx, %rcx
	movq	272(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	280(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	%rdx, %r8
	movq	168(%rsp), %rbp
	movq	256(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r12
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	264(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r13, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	272(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	280(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	adcq	%rdx, %r9
	movq	176(%rsp), %rbp
	movq	256(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	264(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	272(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	280(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r13, %r9
	adcq	%rdx, %r10
	movq	184(%rsp), %rbp
	movq	256(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	264(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	272(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r13, %r9
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	280(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r13, %r10
	adcq	%rdx, %r11
	movq	$38, %rbp
	movq	%r8, %rax
	mulq	__38(%rip)
	movq	%rax, %r8
	movq	%rdx, %r13
	movq	%r9, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %r9
	movq	%r10, %rax
	adcq	%rdx, %r9
	mulq	%rbp
	addq	%rax, %r9
	movq	$0, %r10
	movq	%r11, %rax
	adcq	%rdx, %r10
	mulq	%rbp
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rbx, %r8
	adcq	%r12, %r13
	adcq	%rcx, %r9
	adcq	%rsi, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r8
	adcq	%rcx, %r13
	adcq	%rcx, %r9
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r8
	movq	%r8, 288(%rsp)
	movq	%r13, 296(%rsp)
	movq	%r9, 304(%rsp)
	movq	%r10, 312(%rsp)
	movq	$0, %rcx
	movq	$0, %rsi
	movq	296(%rsp), %rax
	mulq	288(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	304(%rsp), %rax
	mulq	296(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	312(%rsp), %rax
	mulq	304(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	304(%rsp), %rax
	mulq	288(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	%rsi, %r11
	movq	312(%rsp), %rax
	mulq	296(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	%rsi, %rbx
	movq	312(%rsp), %rax
	mulq	288(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	%rsi, %rbp
	adcq	%rsi, %rbx
	adcq	%rsi, %rcx
	addq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%rbx, %rbx
	adcq	%rcx, %rcx
	movq	288(%rsp), %rax
	mulq	288(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %r12
	movq	296(%rsp), %rax
	mulq	296(%rsp)
	movq	%rax, %r13
	movq	%rdx, %r14
	movq	304(%rsp), %rax
	mulq	304(%rsp)
	addq	%r12, %r8
	adcq	%r13, %r9
	adcq	%r14, %r10
	adcq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %rbx
	adcq	$0, %rcx
	movq	312(%rsp), %rax
	mulq	312(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %rcx
	movq	$38, %r12
	movq	%r11, %rax
	mulq	__38(%rip)
	movq	%rax, %r11
	movq	%rdx, %r13
	movq	%rbp, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %rbp
	movq	%rbx, %rax
	adcq	%rdx, %rbp
	mulq	%r12
	addq	%rax, %rbp
	movq	$0, %rbx
	movq	%rcx, %rax
	adcq	%rdx, %rbx
	mulq	%r12
	addq	%rax, %rbx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rsi, %r11
	adcq	%r8, %r13
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r11
	adcq	%rcx, %r13
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r11
	movq	%r11, 160(%rsp)
	movq	%r13, 168(%rsp)
	movq	%rbp, 176(%rsp)
	movq	%rbx, 184(%rsp)
	movq	$18, 408(%rsp)
Lcurve25519_ref4$5:
	movq	160(%rsp), %rcx
	movq	168(%rsp), %rsi
	movq	176(%rsp), %r8
	movq	%rsi, %rax
	mulq	%rcx
	movq	%rax, %r9
	movq	%rdx, %r10
	movq	%r8, %rax
	mulq	%rsi
	movq	%rax, %r11
	movq	%rdx, %rbp
	movq	184(%rsp), %rax
	mulq	%r8
	movq	%rax, %r8
	movq	%rdx, %rbx
	movq	$0, %r12
	movq	176(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	$0, %rbp
	movq	184(%rsp), %rax
	mulq	%rsi
	addq	%rax, %rbp
	adcq	%rdx, %r8
	adcq	$0, %rbx
	movq	184(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %r8
	adcq	$0, %rbx
	adcq	$0, %r12
	addq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%r8, %r8
	adcq	%rbx, %rbx
	adcq	%r12, %r12
	movq	%rcx, %rax
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rdx, %r13
	movq	%rsi, %rax
	mulq	%rsi
	movq	%rax, %rsi
	movq	%rdx, %r14
	movq	176(%rsp), %rax
	mulq	176(%rsp)
	addq	%r13, %r9
	adcq	%rsi, %r10
	adcq	%r14, %r11
	adcq	%rax, %rbp
	adcq	%rdx, %r8
	adcq	$0, %rbx
	adcq	$0, %r12
	movq	184(%rsp), %rax
	mulq	184(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r12
	movq	$38, %rsi
	movq	%rbp, %rax
	mulq	__38(%rip)
	movq	%rax, %rbp
	movq	%rdx, %r13
	movq	%r8, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %r8
	movq	%rbx, %rax
	adcq	%rdx, %r8
	mulq	%rsi
	addq	%rax, %r8
	movq	$0, %rbx
	movq	%r12, %rax
	adcq	%rdx, %rbx
	mulq	%rsi
	addq	%rax, %rbx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %rbp
	adcq	%r9, %r13
	adcq	%r10, %r8
	adcq	%r11, %rbx
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %rbp
	adcq	%rcx, %r13
	adcq	%rcx, %r8
	adcq	%rcx, %rbx
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %rbp
	movq	%rbp, 160(%rsp)
	movq	%r13, 168(%rsp)
	movq	%r8, 176(%rsp)
	movq	%rbx, 184(%rsp)
	movq	408(%rsp), %rax
	subq	$1, %rax
	movq	%rax, 408(%rsp)
	jnb 	Lcurve25519_ref4$5
	movq	$0, %rcx
	movq	$0, %rsi
	movq	$0, %r8
	movq	$0, %r9
	movq	$0, %r10
	movq	$0, %r11
	movq	160(%rsp), %rbp
	movq	288(%rsp), %rax
	mulq	%rbp
	movq	%rax, %rbx
	movq	%rdx, %r12
	movq	296(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r12
	adcq	%rdx, %rcx
	movq	304(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	312(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	%rdx, %r8
	movq	168(%rsp), %rbp
	movq	288(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r12
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	296(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r13, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	304(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	312(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	adcq	%rdx, %r9
	movq	176(%rsp), %rbp
	movq	288(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	296(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	304(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	312(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r13, %r9
	adcq	%rdx, %r10
	movq	184(%rsp), %rbp
	movq	288(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	296(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	304(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r13, %r9
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	312(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r13, %r10
	adcq	%rdx, %r11
	movq	$38, %rbp
	movq	%r8, %rax
	mulq	__38(%rip)
	movq	%rax, %r8
	movq	%rdx, %r13
	movq	%r9, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %r9
	movq	%r10, %rax
	adcq	%rdx, %r9
	mulq	%rbp
	addq	%rax, %r9
	movq	$0, %r10
	movq	%r11, %rax
	adcq	%rdx, %r10
	mulq	%rbp
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rbx, %r8
	adcq	%r12, %r13
	adcq	%rcx, %r9
	adcq	%rsi, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r8
	adcq	%rcx, %r13
	adcq	%rcx, %r9
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r8
	movq	%r8, 160(%rsp)
	movq	%r13, 168(%rsp)
	movq	%r9, 176(%rsp)
	movq	%r10, 184(%rsp)
	movq	$0, %rcx
	movq	$0, %rsi
	movq	168(%rsp), %rax
	mulq	160(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	176(%rsp), %rax
	mulq	168(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	184(%rsp), %rax
	mulq	176(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	176(%rsp), %rax
	mulq	160(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	%rsi, %r11
	movq	184(%rsp), %rax
	mulq	168(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	%rsi, %rbx
	movq	184(%rsp), %rax
	mulq	160(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	%rsi, %rbp
	adcq	%rsi, %rbx
	adcq	%rsi, %rcx
	addq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%rbx, %rbx
	adcq	%rcx, %rcx
	movq	160(%rsp), %rax
	mulq	160(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %r12
	movq	168(%rsp), %rax
	mulq	168(%rsp)
	movq	%rax, %r13
	movq	%rdx, %r14
	movq	176(%rsp), %rax
	mulq	176(%rsp)
	addq	%r12, %r8
	adcq	%r13, %r9
	adcq	%r14, %r10
	adcq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %rbx
	adcq	$0, %rcx
	movq	184(%rsp), %rax
	mulq	184(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %rcx
	movq	$38, %r12
	movq	%r11, %rax
	mulq	__38(%rip)
	movq	%rax, %r11
	movq	%rdx, %r13
	movq	%rbp, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %rbp
	movq	%rbx, %rax
	adcq	%rdx, %rbp
	mulq	%r12
	addq	%rax, %rbp
	movq	$0, %rbx
	movq	%rcx, %rax
	adcq	%rdx, %rbx
	mulq	%r12
	addq	%rax, %rbx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rsi, %r11
	adcq	%r8, %r13
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r11
	adcq	%rcx, %r13
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r11
	movq	%r11, 160(%rsp)
	movq	%r13, 168(%rsp)
	movq	%rbp, 176(%rsp)
	movq	%rbx, 184(%rsp)
	movq	$8, 408(%rsp)
Lcurve25519_ref4$4:
	movq	160(%rsp), %rcx
	movq	168(%rsp), %rsi
	movq	176(%rsp), %r8
	movq	%rsi, %rax
	mulq	%rcx
	movq	%rax, %r9
	movq	%rdx, %r10
	movq	%r8, %rax
	mulq	%rsi
	movq	%rax, %r11
	movq	%rdx, %rbp
	movq	184(%rsp), %rax
	mulq	%r8
	movq	%rax, %r8
	movq	%rdx, %rbx
	movq	$0, %r12
	movq	176(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	$0, %rbp
	movq	184(%rsp), %rax
	mulq	%rsi
	addq	%rax, %rbp
	adcq	%rdx, %r8
	adcq	$0, %rbx
	movq	184(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %r8
	adcq	$0, %rbx
	adcq	$0, %r12
	addq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%r8, %r8
	adcq	%rbx, %rbx
	adcq	%r12, %r12
	movq	%rcx, %rax
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rdx, %r13
	movq	%rsi, %rax
	mulq	%rsi
	movq	%rax, %rsi
	movq	%rdx, %r14
	movq	176(%rsp), %rax
	mulq	176(%rsp)
	addq	%r13, %r9
	adcq	%rsi, %r10
	adcq	%r14, %r11
	adcq	%rax, %rbp
	adcq	%rdx, %r8
	adcq	$0, %rbx
	adcq	$0, %r12
	movq	184(%rsp), %rax
	mulq	184(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r12
	movq	$38, %rsi
	movq	%rbp, %rax
	mulq	__38(%rip)
	movq	%rax, %rbp
	movq	%rdx, %r13
	movq	%r8, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %r8
	movq	%rbx, %rax
	adcq	%rdx, %r8
	mulq	%rsi
	addq	%rax, %r8
	movq	$0, %rbx
	movq	%r12, %rax
	adcq	%rdx, %rbx
	mulq	%rsi
	addq	%rax, %rbx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %rbp
	adcq	%r9, %r13
	adcq	%r10, %r8
	adcq	%r11, %rbx
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %rbp
	adcq	%rcx, %r13
	adcq	%rcx, %r8
	adcq	%rcx, %rbx
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %rbp
	movq	%rbp, 160(%rsp)
	movq	%r13, 168(%rsp)
	movq	%r8, 176(%rsp)
	movq	%rbx, 184(%rsp)
	movq	408(%rsp), %rax
	subq	$1, %rax
	movq	%rax, 408(%rsp)
	jnb 	Lcurve25519_ref4$4
	movq	$0, %rcx
	movq	$0, %rsi
	movq	$0, %r8
	movq	$0, %r9
	movq	$0, %r10
	movq	$0, %r11
	movq	160(%rsp), %rbp
	movq	256(%rsp), %rax
	mulq	%rbp
	movq	%rax, %rbx
	movq	%rdx, %r12
	movq	264(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r12
	adcq	%rdx, %rcx
	movq	272(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	280(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	%rdx, %r8
	movq	168(%rsp), %rbp
	movq	256(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r12
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	264(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r13, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	272(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	280(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	adcq	%rdx, %r9
	movq	176(%rsp), %rbp
	movq	256(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	264(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	272(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	280(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r13, %r9
	adcq	%rdx, %r10
	movq	184(%rsp), %rbp
	movq	256(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	264(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	272(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r13, %r9
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	280(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r13, %r10
	adcq	%rdx, %r11
	movq	$38, %rbp
	movq	%r8, %rax
	mulq	__38(%rip)
	movq	%rax, %r8
	movq	%rdx, %r13
	movq	%r9, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %r9
	movq	%r10, %rax
	adcq	%rdx, %r9
	mulq	%rbp
	addq	%rax, %r9
	movq	$0, %r10
	movq	%r11, %rax
	adcq	%rdx, %r10
	mulq	%rbp
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rbx, %r8
	adcq	%r12, %r13
	adcq	%rcx, %r9
	adcq	%rsi, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r8
	adcq	%rcx, %r13
	adcq	%rcx, %r9
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r8
	movq	%r8, 192(%rsp)
	movq	%r13, 200(%rsp)
	movq	%r9, 208(%rsp)
	movq	%r10, 216(%rsp)
	movq	$0, %rcx
	movq	$0, %rsi
	movq	200(%rsp), %rax
	mulq	192(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	208(%rsp), %rax
	mulq	200(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	216(%rsp), %rax
	mulq	208(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	208(%rsp), %rax
	mulq	192(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	%rsi, %r11
	movq	216(%rsp), %rax
	mulq	200(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	%rsi, %rbx
	movq	216(%rsp), %rax
	mulq	192(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	%rsi, %rbp
	adcq	%rsi, %rbx
	adcq	%rsi, %rcx
	addq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%rbx, %rbx
	adcq	%rcx, %rcx
	movq	192(%rsp), %rax
	mulq	192(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %r12
	movq	200(%rsp), %rax
	mulq	200(%rsp)
	movq	%rax, %r13
	movq	%rdx, %r14
	movq	208(%rsp), %rax
	mulq	208(%rsp)
	addq	%r12, %r8
	adcq	%r13, %r9
	adcq	%r14, %r10
	adcq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %rbx
	adcq	$0, %rcx
	movq	216(%rsp), %rax
	mulq	216(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %rcx
	movq	$38, %r12
	movq	%r11, %rax
	mulq	__38(%rip)
	movq	%rax, %r11
	movq	%rdx, %r13
	movq	%rbp, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %rbp
	movq	%rbx, %rax
	adcq	%rdx, %rbp
	mulq	%r12
	addq	%rax, %rbp
	movq	$0, %rbx
	movq	%rcx, %rax
	adcq	%rdx, %rbx
	mulq	%r12
	addq	%rax, %rbx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rsi, %r11
	adcq	%r8, %r13
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r11
	adcq	%rcx, %r13
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r11
	movq	%r11, 160(%rsp)
	movq	%r13, 168(%rsp)
	movq	%rbp, 176(%rsp)
	movq	%rbx, 184(%rsp)
	movq	$48, 408(%rsp)
Lcurve25519_ref4$3:
	movq	160(%rsp), %rcx
	movq	168(%rsp), %rsi
	movq	176(%rsp), %r8
	movq	%rsi, %rax
	mulq	%rcx
	movq	%rax, %r9
	movq	%rdx, %r10
	movq	%r8, %rax
	mulq	%rsi
	movq	%rax, %r11
	movq	%rdx, %rbp
	movq	184(%rsp), %rax
	mulq	%r8
	movq	%rax, %r8
	movq	%rdx, %rbx
	movq	$0, %r12
	movq	176(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	$0, %rbp
	movq	184(%rsp), %rax
	mulq	%rsi
	addq	%rax, %rbp
	adcq	%rdx, %r8
	adcq	$0, %rbx
	movq	184(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %r8
	adcq	$0, %rbx
	adcq	$0, %r12
	addq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%r8, %r8
	adcq	%rbx, %rbx
	adcq	%r12, %r12
	movq	%rcx, %rax
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rdx, %r13
	movq	%rsi, %rax
	mulq	%rsi
	movq	%rax, %rsi
	movq	%rdx, %r14
	movq	176(%rsp), %rax
	mulq	176(%rsp)
	addq	%r13, %r9
	adcq	%rsi, %r10
	adcq	%r14, %r11
	adcq	%rax, %rbp
	adcq	%rdx, %r8
	adcq	$0, %rbx
	adcq	$0, %r12
	movq	184(%rsp), %rax
	mulq	184(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r12
	movq	$38, %rsi
	movq	%rbp, %rax
	mulq	__38(%rip)
	movq	%rax, %rbp
	movq	%rdx, %r13
	movq	%r8, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %r8
	movq	%rbx, %rax
	adcq	%rdx, %r8
	mulq	%rsi
	addq	%rax, %r8
	movq	$0, %rbx
	movq	%r12, %rax
	adcq	%rdx, %rbx
	mulq	%rsi
	addq	%rax, %rbx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %rbp
	adcq	%r9, %r13
	adcq	%r10, %r8
	adcq	%r11, %rbx
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %rbp
	adcq	%rcx, %r13
	adcq	%rcx, %r8
	adcq	%rcx, %rbx
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %rbp
	movq	%rbp, 160(%rsp)
	movq	%r13, 168(%rsp)
	movq	%r8, 176(%rsp)
	movq	%rbx, 184(%rsp)
	movq	408(%rsp), %rax
	subq	$1, %rax
	movq	%rax, 408(%rsp)
	jnb 	Lcurve25519_ref4$3
	movq	$0, %rcx
	movq	$0, %rsi
	movq	$0, %r8
	movq	$0, %r9
	movq	$0, %r10
	movq	$0, %r11
	movq	160(%rsp), %rbp
	movq	192(%rsp), %rax
	mulq	%rbp
	movq	%rax, %rbx
	movq	%rdx, %r12
	movq	200(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r12
	adcq	%rdx, %rcx
	movq	208(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	216(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	%rdx, %r8
	movq	168(%rsp), %rbp
	movq	192(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r12
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	200(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r13, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	208(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	216(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	adcq	%rdx, %r9
	movq	176(%rsp), %rbp
	movq	192(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	200(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	208(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	216(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r13, %r9
	adcq	%rdx, %r10
	movq	184(%rsp), %rbp
	movq	192(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	200(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	208(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r13, %r9
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	216(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r13, %r10
	adcq	%rdx, %r11
	movq	$38, %rbp
	movq	%r8, %rax
	mulq	__38(%rip)
	movq	%rax, %r8
	movq	%rdx, %r13
	movq	%r9, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %r9
	movq	%r10, %rax
	adcq	%rdx, %r9
	mulq	%rbp
	addq	%rax, %r9
	movq	$0, %r10
	movq	%r11, %rax
	adcq	%rdx, %r10
	mulq	%rbp
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rbx, %r8
	adcq	%r12, %r13
	adcq	%rcx, %r9
	adcq	%rsi, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r8
	adcq	%rcx, %r13
	adcq	%rcx, %r9
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r8
	movq	%r8, 224(%rsp)
	movq	%r13, 232(%rsp)
	movq	%r9, 240(%rsp)
	movq	%r10, 248(%rsp)
	movq	$0, %rcx
	movq	$0, %rsi
	movq	232(%rsp), %rax
	mulq	224(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	240(%rsp), %rax
	mulq	232(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	248(%rsp), %rax
	mulq	240(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	240(%rsp), %rax
	mulq	224(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	%rsi, %r11
	movq	248(%rsp), %rax
	mulq	232(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	%rsi, %rbx
	movq	248(%rsp), %rax
	mulq	224(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	%rsi, %rbp
	adcq	%rsi, %rbx
	adcq	%rsi, %rcx
	addq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%rbx, %rbx
	adcq	%rcx, %rcx
	movq	224(%rsp), %rax
	mulq	224(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %r12
	movq	232(%rsp), %rax
	mulq	232(%rsp)
	movq	%rax, %r13
	movq	%rdx, %r14
	movq	240(%rsp), %rax
	mulq	240(%rsp)
	addq	%r12, %r8
	adcq	%r13, %r9
	adcq	%r14, %r10
	adcq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %rbx
	adcq	$0, %rcx
	movq	248(%rsp), %rax
	mulq	248(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %rcx
	movq	$38, %r12
	movq	%r11, %rax
	mulq	__38(%rip)
	movq	%rax, %r11
	movq	%rdx, %r13
	movq	%rbp, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %rbp
	movq	%rbx, %rax
	adcq	%rdx, %rbp
	mulq	%r12
	addq	%rax, %rbp
	movq	$0, %rbx
	movq	%rcx, %rax
	adcq	%rdx, %rbx
	mulq	%r12
	addq	%rax, %rbx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rsi, %r11
	adcq	%r8, %r13
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r11
	adcq	%rcx, %r13
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r11
	movq	%r11, 160(%rsp)
	movq	%r13, 168(%rsp)
	movq	%rbp, 176(%rsp)
	movq	%rbx, 184(%rsp)
	movq	$98, 408(%rsp)
Lcurve25519_ref4$2:
	movq	160(%rsp), %rcx
	movq	168(%rsp), %rsi
	movq	176(%rsp), %r8
	movq	%rsi, %rax
	mulq	%rcx
	movq	%rax, %r9
	movq	%rdx, %r10
	movq	%r8, %rax
	mulq	%rsi
	movq	%rax, %r11
	movq	%rdx, %rbp
	movq	184(%rsp), %rax
	mulq	%r8
	movq	%rax, %r8
	movq	%rdx, %rbx
	movq	$0, %r12
	movq	176(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	$0, %rbp
	movq	184(%rsp), %rax
	mulq	%rsi
	addq	%rax, %rbp
	adcq	%rdx, %r8
	adcq	$0, %rbx
	movq	184(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %r8
	adcq	$0, %rbx
	adcq	$0, %r12
	addq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%r8, %r8
	adcq	%rbx, %rbx
	adcq	%r12, %r12
	movq	%rcx, %rax
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rdx, %r13
	movq	%rsi, %rax
	mulq	%rsi
	movq	%rax, %rsi
	movq	%rdx, %r14
	movq	176(%rsp), %rax
	mulq	176(%rsp)
	addq	%r13, %r9
	adcq	%rsi, %r10
	adcq	%r14, %r11
	adcq	%rax, %rbp
	adcq	%rdx, %r8
	adcq	$0, %rbx
	adcq	$0, %r12
	movq	184(%rsp), %rax
	mulq	184(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r12
	movq	$38, %rsi
	movq	%rbp, %rax
	mulq	__38(%rip)
	movq	%rax, %rbp
	movq	%rdx, %r13
	movq	%r8, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %r8
	movq	%rbx, %rax
	adcq	%rdx, %r8
	mulq	%rsi
	addq	%rax, %r8
	movq	$0, %rbx
	movq	%r12, %rax
	adcq	%rdx, %rbx
	mulq	%rsi
	addq	%rax, %rbx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %rbp
	adcq	%r9, %r13
	adcq	%r10, %r8
	adcq	%r11, %rbx
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %rbp
	adcq	%rcx, %r13
	adcq	%rcx, %r8
	adcq	%rcx, %rbx
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %rbp
	movq	%rbp, 160(%rsp)
	movq	%r13, 168(%rsp)
	movq	%r8, 176(%rsp)
	movq	%rbx, 184(%rsp)
	movq	408(%rsp), %rax
	subq	$1, %rax
	movq	%rax, 408(%rsp)
	jnb 	Lcurve25519_ref4$2
	movq	$0, %rcx
	movq	$0, %rsi
	movq	$0, %r8
	movq	$0, %r9
	movq	$0, %r10
	movq	$0, %r11
	movq	160(%rsp), %rbp
	movq	224(%rsp), %rax
	mulq	%rbp
	movq	%rax, %rbx
	movq	%rdx, %r12
	movq	232(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r12
	adcq	%rdx, %rcx
	movq	240(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	248(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	%rdx, %r8
	movq	168(%rsp), %rbp
	movq	224(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r12
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	232(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r13, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	240(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	248(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	adcq	%rdx, %r9
	movq	176(%rsp), %rbp
	movq	224(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	232(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	240(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	248(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r13, %r9
	adcq	%rdx, %r10
	movq	184(%rsp), %rbp
	movq	224(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	232(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	240(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r13, %r9
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	248(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r13, %r10
	adcq	%rdx, %r11
	movq	$38, %rbp
	movq	%r8, %rax
	mulq	__38(%rip)
	movq	%rax, %r8
	movq	%rdx, %r13
	movq	%r9, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %r9
	movq	%r10, %rax
	adcq	%rdx, %r9
	mulq	%rbp
	addq	%rax, %r9
	movq	$0, %r10
	movq	%r11, %rax
	adcq	%rdx, %r10
	mulq	%rbp
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rbx, %r8
	adcq	%r12, %r13
	adcq	%rcx, %r9
	adcq	%rsi, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r8
	adcq	%rcx, %r13
	adcq	%rcx, %r9
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r8
	movq	%r8, 160(%rsp)
	movq	%r13, 168(%rsp)
	movq	%r9, 176(%rsp)
	movq	%r10, 184(%rsp)
	movq	$0, %rcx
	movq	$0, %rsi
	movq	168(%rsp), %rax
	mulq	160(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	176(%rsp), %rax
	mulq	168(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	184(%rsp), %rax
	mulq	176(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	176(%rsp), %rax
	mulq	160(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	%rsi, %r11
	movq	184(%rsp), %rax
	mulq	168(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	%rsi, %rbx
	movq	184(%rsp), %rax
	mulq	160(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	%rsi, %rbp
	adcq	%rsi, %rbx
	adcq	%rsi, %rcx
	addq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%rbx, %rbx
	adcq	%rcx, %rcx
	movq	160(%rsp), %rax
	mulq	160(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %r12
	movq	168(%rsp), %rax
	mulq	168(%rsp)
	movq	%rax, %r13
	movq	%rdx, %r14
	movq	176(%rsp), %rax
	mulq	176(%rsp)
	addq	%r12, %r8
	adcq	%r13, %r9
	adcq	%r14, %r10
	adcq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %rbx
	adcq	$0, %rcx
	movq	184(%rsp), %rax
	mulq	184(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %rcx
	movq	$38, %r12
	movq	%r11, %rax
	mulq	__38(%rip)
	movq	%rax, %r11
	movq	%rdx, %r13
	movq	%rbp, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %rbp
	movq	%rbx, %rax
	adcq	%rdx, %rbp
	mulq	%r12
	addq	%rax, %rbp
	movq	$0, %rbx
	movq	%rcx, %rax
	adcq	%rdx, %rbx
	mulq	%r12
	addq	%rax, %rbx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rsi, %r11
	adcq	%r8, %r13
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r11
	adcq	%rcx, %r13
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r11
	movq	%r11, 160(%rsp)
	movq	%r13, 168(%rsp)
	movq	%rbp, 176(%rsp)
	movq	%rbx, 184(%rsp)
	movq	$48, 408(%rsp)
Lcurve25519_ref4$1:
	movq	160(%rsp), %rcx
	movq	168(%rsp), %rsi
	movq	176(%rsp), %r8
	movq	%rsi, %rax
	mulq	%rcx
	movq	%rax, %r9
	movq	%rdx, %r10
	movq	%r8, %rax
	mulq	%rsi
	movq	%rax, %r11
	movq	%rdx, %rbp
	movq	184(%rsp), %rax
	mulq	%r8
	movq	%rax, %r8
	movq	%rdx, %rbx
	movq	$0, %r12
	movq	176(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	$0, %rbp
	movq	184(%rsp), %rax
	mulq	%rsi
	addq	%rax, %rbp
	adcq	%rdx, %r8
	adcq	$0, %rbx
	movq	184(%rsp), %rax
	mulq	%rcx
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %r8
	adcq	$0, %rbx
	adcq	$0, %r12
	addq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%r8, %r8
	adcq	%rbx, %rbx
	adcq	%r12, %r12
	movq	%rcx, %rax
	mulq	%rcx
	movq	%rax, %rcx
	movq	%rdx, %r13
	movq	%rsi, %rax
	mulq	%rsi
	movq	%rax, %rsi
	movq	%rdx, %r14
	movq	176(%rsp), %rax
	mulq	176(%rsp)
	addq	%r13, %r9
	adcq	%rsi, %r10
	adcq	%r14, %r11
	adcq	%rax, %rbp
	adcq	%rdx, %r8
	adcq	$0, %rbx
	adcq	$0, %r12
	movq	184(%rsp), %rax
	mulq	184(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r12
	movq	$38, %rsi
	movq	%rbp, %rax
	mulq	__38(%rip)
	movq	%rax, %rbp
	movq	%rdx, %r13
	movq	%r8, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %r8
	movq	%rbx, %rax
	adcq	%rdx, %r8
	mulq	%rsi
	addq	%rax, %r8
	movq	$0, %rbx
	movq	%r12, %rax
	adcq	%rdx, %rbx
	mulq	%rsi
	addq	%rax, %rbx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rcx, %rbp
	adcq	%r9, %r13
	adcq	%r10, %r8
	adcq	%r11, %rbx
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %rbp
	adcq	%rcx, %r13
	adcq	%rcx, %r8
	adcq	%rcx, %rbx
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %rbp
	movq	%rbp, 160(%rsp)
	movq	%r13, 168(%rsp)
	movq	%r8, 176(%rsp)
	movq	%rbx, 184(%rsp)
	movq	408(%rsp), %rax
	subq	$1, %rax
	movq	%rax, 408(%rsp)
	jnb 	Lcurve25519_ref4$1
	movq	$0, %rcx
	movq	$0, %rsi
	movq	$0, %r8
	movq	$0, %r9
	movq	$0, %r10
	movq	$0, %r11
	movq	160(%rsp), %rbp
	movq	192(%rsp), %rax
	mulq	%rbp
	movq	%rax, %rbx
	movq	%rdx, %r12
	movq	200(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r12
	adcq	%rdx, %rcx
	movq	208(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	216(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	%rdx, %r8
	movq	168(%rsp), %rbp
	movq	192(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r12
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	200(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r13, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	208(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	216(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	adcq	%rdx, %r9
	movq	176(%rsp), %rbp
	movq	192(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	200(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	208(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	216(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r13, %r9
	adcq	%rdx, %r10
	movq	184(%rsp), %rbp
	movq	192(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	200(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	208(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r13, %r9
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	216(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r13, %r10
	adcq	%rdx, %r11
	movq	$38, %rbp
	movq	%r8, %rax
	mulq	__38(%rip)
	movq	%rax, %r8
	movq	%rdx, %r13
	movq	%r9, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %r9
	movq	%r10, %rax
	adcq	%rdx, %r9
	mulq	%rbp
	addq	%rax, %r9
	movq	$0, %r10
	movq	%r11, %rax
	adcq	%rdx, %r10
	mulq	%rbp
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rbx, %r8
	adcq	%r12, %r13
	adcq	%rcx, %r9
	adcq	%rsi, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r8
	adcq	%rcx, %r13
	adcq	%rcx, %r9
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r8
	movq	%r8, 160(%rsp)
	movq	%r13, 168(%rsp)
	movq	%r9, 176(%rsp)
	movq	%r10, 184(%rsp)
	movq	$0, %rcx
	movq	$0, %rsi
	movq	168(%rsp), %rax
	mulq	160(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	176(%rsp), %rax
	mulq	168(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	184(%rsp), %rax
	mulq	176(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	176(%rsp), %rax
	mulq	160(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	%rsi, %r11
	movq	184(%rsp), %rax
	mulq	168(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	%rsi, %rbx
	movq	184(%rsp), %rax
	mulq	160(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	%rsi, %rbp
	adcq	%rsi, %rbx
	adcq	%rsi, %rcx
	addq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%rbx, %rbx
	adcq	%rcx, %rcx
	movq	160(%rsp), %rax
	mulq	160(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %r12
	movq	168(%rsp), %rax
	mulq	168(%rsp)
	movq	%rax, %r13
	movq	%rdx, %r14
	movq	176(%rsp), %rax
	mulq	176(%rsp)
	addq	%r12, %r8
	adcq	%r13, %r9
	adcq	%r14, %r10
	adcq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %rbx
	adcq	$0, %rcx
	movq	184(%rsp), %rax
	mulq	184(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %rcx
	movq	$38, %r12
	movq	%r11, %rax
	mulq	__38(%rip)
	movq	%rax, %r11
	movq	%rdx, %r13
	movq	%rbp, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %rbp
	movq	%rbx, %rax
	adcq	%rdx, %rbp
	mulq	%r12
	addq	%rax, %rbp
	movq	$0, %rbx
	movq	%rcx, %rax
	adcq	%rdx, %rbx
	mulq	%r12
	addq	%rax, %rbx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rsi, %r11
	adcq	%r8, %r13
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r11
	adcq	%rcx, %r13
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r11
	movq	%r11, 160(%rsp)
	movq	%r13, 168(%rsp)
	movq	%rbp, 176(%rsp)
	movq	%rbx, 184(%rsp)
	movq	$0, %rcx
	movq	$0, %rsi
	movq	168(%rsp), %rax
	mulq	160(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	176(%rsp), %rax
	mulq	168(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	184(%rsp), %rax
	mulq	176(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	176(%rsp), %rax
	mulq	160(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	%rsi, %r11
	movq	184(%rsp), %rax
	mulq	168(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	%rsi, %rbx
	movq	184(%rsp), %rax
	mulq	160(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	%rsi, %rbp
	adcq	%rsi, %rbx
	adcq	%rsi, %rcx
	addq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%rbx, %rbx
	adcq	%rcx, %rcx
	movq	160(%rsp), %rax
	mulq	160(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %r12
	movq	168(%rsp), %rax
	mulq	168(%rsp)
	movq	%rax, %r13
	movq	%rdx, %r14
	movq	176(%rsp), %rax
	mulq	176(%rsp)
	addq	%r12, %r8
	adcq	%r13, %r9
	adcq	%r14, %r10
	adcq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %rbx
	adcq	$0, %rcx
	movq	184(%rsp), %rax
	mulq	184(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %rcx
	movq	$38, %r12
	movq	%r11, %rax
	mulq	__38(%rip)
	movq	%rax, %r11
	movq	%rdx, %r13
	movq	%rbp, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %rbp
	movq	%rbx, %rax
	adcq	%rdx, %rbp
	mulq	%r12
	addq	%rax, %rbp
	movq	$0, %rbx
	movq	%rcx, %rax
	adcq	%rdx, %rbx
	mulq	%r12
	addq	%rax, %rbx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rsi, %r11
	adcq	%r8, %r13
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r11
	adcq	%rcx, %r13
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r11
	movq	%r11, 160(%rsp)
	movq	%r13, 168(%rsp)
	movq	%rbp, 176(%rsp)
	movq	%rbx, 184(%rsp)
	movq	$0, %rcx
	movq	$0, %rsi
	movq	168(%rsp), %rax
	mulq	160(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	176(%rsp), %rax
	mulq	168(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	184(%rsp), %rax
	mulq	176(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	176(%rsp), %rax
	mulq	160(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	%rsi, %r11
	movq	184(%rsp), %rax
	mulq	168(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	%rsi, %rbx
	movq	184(%rsp), %rax
	mulq	160(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	%rsi, %rbp
	adcq	%rsi, %rbx
	adcq	%rsi, %rcx
	addq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%rbx, %rbx
	adcq	%rcx, %rcx
	movq	160(%rsp), %rax
	mulq	160(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %r12
	movq	168(%rsp), %rax
	mulq	168(%rsp)
	movq	%rax, %r13
	movq	%rdx, %r14
	movq	176(%rsp), %rax
	mulq	176(%rsp)
	addq	%r12, %r8
	adcq	%r13, %r9
	adcq	%r14, %r10
	adcq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %rbx
	adcq	$0, %rcx
	movq	184(%rsp), %rax
	mulq	184(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %rcx
	movq	$38, %r12
	movq	%r11, %rax
	mulq	__38(%rip)
	movq	%rax, %r11
	movq	%rdx, %r13
	movq	%rbp, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %rbp
	movq	%rbx, %rax
	adcq	%rdx, %rbp
	mulq	%r12
	addq	%rax, %rbp
	movq	$0, %rbx
	movq	%rcx, %rax
	adcq	%rdx, %rbx
	mulq	%r12
	addq	%rax, %rbx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rsi, %r11
	adcq	%r8, %r13
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r11
	adcq	%rcx, %r13
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r11
	movq	%r11, 160(%rsp)
	movq	%r13, 168(%rsp)
	movq	%rbp, 176(%rsp)
	movq	%rbx, 184(%rsp)
	movq	$0, %rcx
	movq	$0, %rsi
	movq	168(%rsp), %rax
	mulq	160(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	176(%rsp), %rax
	mulq	168(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	184(%rsp), %rax
	mulq	176(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	176(%rsp), %rax
	mulq	160(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	%rsi, %r11
	movq	184(%rsp), %rax
	mulq	168(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	%rsi, %rbx
	movq	184(%rsp), %rax
	mulq	160(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	%rsi, %rbp
	adcq	%rsi, %rbx
	adcq	%rsi, %rcx
	addq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%rbx, %rbx
	adcq	%rcx, %rcx
	movq	160(%rsp), %rax
	mulq	160(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %r12
	movq	168(%rsp), %rax
	mulq	168(%rsp)
	movq	%rax, %r13
	movq	%rdx, %r14
	movq	176(%rsp), %rax
	mulq	176(%rsp)
	addq	%r12, %r8
	adcq	%r13, %r9
	adcq	%r14, %r10
	adcq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %rbx
	adcq	$0, %rcx
	movq	184(%rsp), %rax
	mulq	184(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %rcx
	movq	$38, %r12
	movq	%r11, %rax
	mulq	__38(%rip)
	movq	%rax, %r11
	movq	%rdx, %r13
	movq	%rbp, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %rbp
	movq	%rbx, %rax
	adcq	%rdx, %rbp
	mulq	%r12
	addq	%rax, %rbp
	movq	$0, %rbx
	movq	%rcx, %rax
	adcq	%rdx, %rbx
	mulq	%r12
	addq	%rax, %rbx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rsi, %r11
	adcq	%r8, %r13
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r11
	adcq	%rcx, %r13
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r11
	movq	%r11, 160(%rsp)
	movq	%r13, 168(%rsp)
	movq	%rbp, 176(%rsp)
	movq	%rbx, 184(%rsp)
	movq	$0, %rcx
	movq	$0, %rsi
	movq	168(%rsp), %rax
	mulq	160(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	176(%rsp), %rax
	mulq	168(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	184(%rsp), %rax
	mulq	176(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	176(%rsp), %rax
	mulq	160(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r10
	adcq	%rsi, %r11
	movq	184(%rsp), %rax
	mulq	168(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	%rsi, %rbx
	movq	184(%rsp), %rax
	mulq	160(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	adcq	%rsi, %rbp
	adcq	%rsi, %rbx
	adcq	%rsi, %rcx
	addq	%r8, %r8
	adcq	%r9, %r9
	adcq	%r10, %r10
	adcq	%r11, %r11
	adcq	%rbp, %rbp
	adcq	%rbx, %rbx
	adcq	%rcx, %rcx
	movq	160(%rsp), %rax
	mulq	160(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %r12
	movq	168(%rsp), %rax
	mulq	168(%rsp)
	movq	%rax, %r13
	movq	%rdx, %r14
	movq	176(%rsp), %rax
	mulq	176(%rsp)
	addq	%r12, %r8
	adcq	%r13, %r9
	adcq	%r14, %r10
	adcq	%rax, %r11
	adcq	%rdx, %rbp
	adcq	$0, %rbx
	adcq	$0, %rcx
	movq	184(%rsp), %rax
	mulq	184(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %rcx
	movq	$38, %r12
	movq	%r11, %rax
	mulq	__38(%rip)
	movq	%rax, %r11
	movq	%rdx, %r13
	movq	%rbp, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %rbp
	movq	%rbx, %rax
	adcq	%rdx, %rbp
	mulq	%r12
	addq	%rax, %rbp
	movq	$0, %rbx
	movq	%rcx, %rax
	adcq	%rdx, %rbx
	mulq	%r12
	addq	%rax, %rbx
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rsi, %r11
	adcq	%r8, %r13
	adcq	%r9, %rbp
	adcq	%r10, %rbx
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r11
	adcq	%rcx, %r13
	adcq	%rcx, %rbp
	adcq	%rcx, %rbx
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r11
	movq	%r11, 160(%rsp)
	movq	%r13, 168(%rsp)
	movq	%rbp, 176(%rsp)
	movq	%rbx, 184(%rsp)
	movq	$0, %rcx
	movq	$0, %rsi
	movq	$0, %r8
	movq	$0, %r9
	movq	$0, %r10
	movq	$0, %r11
	movq	160(%rsp), %rbp
	movq	128(%rsp), %rax
	mulq	%rbp
	movq	%rax, %rbx
	movq	%rdx, %r12
	movq	136(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r12
	adcq	%rdx, %rcx
	movq	144(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	152(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	%rdx, %r8
	movq	168(%rsp), %rbp
	movq	128(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r12
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	136(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r13, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	144(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	152(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	adcq	%rdx, %r9
	movq	176(%rsp), %rbp
	movq	128(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	136(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	144(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	152(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r13, %r9
	adcq	%rdx, %r10
	movq	184(%rsp), %rbp
	movq	128(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	136(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	144(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r13, %r9
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	152(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r13, %r10
	adcq	%rdx, %r11
	movq	$38, %rbp
	movq	%r8, %rax
	mulq	__38(%rip)
	movq	%rax, %r8
	movq	%rdx, %r13
	movq	%r9, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %r9
	movq	%r10, %rax
	adcq	%rdx, %r9
	mulq	%rbp
	addq	%rax, %r9
	movq	$0, %r10
	movq	%r11, %rax
	adcq	%rdx, %r10
	mulq	%rbp
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rbx, %r8
	adcq	%r12, %r13
	adcq	%rcx, %r9
	adcq	%rsi, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r8
	adcq	%rcx, %r13
	adcq	%rcx, %r9
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r8
	movq	%r8, 64(%rsp)
	movq	%r13, 72(%rsp)
	movq	%r9, 80(%rsp)
	movq	%r10, 88(%rsp)
	movq	$0, %rcx
	movq	$0, %rsi
	movq	$0, %r8
	movq	$0, %r9
	movq	$0, %r10
	movq	$0, %r11
	movq	(%rsp), %rbp
	movq	64(%rsp), %rax
	mulq	%rbp
	movq	%rax, %rbx
	movq	%rdx, %r12
	movq	72(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r12
	adcq	%rdx, %rcx
	movq	80(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	88(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	%rdx, %r8
	movq	8(%rsp), %rbp
	movq	64(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r12
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	72(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	adcq	$0, %rdx
	addq	%r13, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	80(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	88(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	adcq	%rdx, %r9
	movq	16(%rsp), %rbp
	movq	64(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rcx
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	72(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	adcq	$0, %rdx
	addq	%r13, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	80(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	88(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r13, %r9
	adcq	%rdx, %r10
	movq	24(%rsp), %rbp
	movq	64(%rsp), %rax
	mulq	%rbp
	addq	%rax, %rsi
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	72(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r8
	adcq	$0, %rdx
	addq	%r13, %r8
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	80(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r9
	adcq	$0, %rdx
	addq	%r13, %r9
	movq	$0, %r13
	adcq	%rdx, %r13
	movq	88(%rsp), %rax
	mulq	%rbp
	addq	%rax, %r10
	adcq	$0, %rdx
	addq	%r13, %r10
	adcq	%rdx, %r11
	movq	$38, %rbp
	movq	%r8, %rax
	mulq	__38(%rip)
	movq	%rax, %r8
	movq	%rdx, %r13
	movq	%r9, %rax
	mulq	__38(%rip)
	addq	%rax, %r13
	movq	$0, %r9
	movq	%r10, %rax
	adcq	%rdx, %r9
	mulq	%rbp
	addq	%rax, %r9
	movq	$0, %r10
	movq	%r11, %rax
	adcq	%rdx, %r10
	mulq	%rbp
	addq	%rax, %r10
	movq	$0, %rax
	adcq	%rdx, %rax
	addq	%rbx, %r8
	adcq	%r12, %r13
	adcq	%rcx, %r9
	adcq	%rsi, %r10
	adcq	$0, %rax
	imulq	$38, %rax, %rax
	movq	$0, %rcx
	addq	%rax, %r8
	adcq	%rcx, %r13
	adcq	%rcx, %r9
	adcq	%rcx, %r10
	adcq	%rcx, %rcx
	imulq	$38, %rcx, %rax
	addq	%rax, %r8
	movq	%r8, %rax
	movq	%r13, %rcx
	movq	%r9, %rdx
	movq	%r10, %rsi
	movq	%rax, %r8
	movq	%rcx, %r9
	movq	%rdx, %r10
	movq	%rsi, %r11
	movq	$1, %rbp
	shlq	$63, %rbp
	addq	$19, %r8
	adcq	$0, %r9
	adcq	$0, %r10
	adcq	%rbp, %r11
	cmovbq	%r8, %rax
	cmovbq	%r9, %rcx
	cmovbq	%r10, %rdx
	cmovbq	%r11, %rsi
	movq	%rax, %r8
	movq	%rcx, %r9
	movq	%rdx, %r10
	movq	%rsi, %r11
	addq	$19, %r8
	adcq	$0, %r9
	adcq	$0, %r10
	adcq	%rbp, %r11
	cmovbq	%r8, %rax
	cmovbq	%r9, %rcx
	cmovbq	%r10, %rdx
	cmovbq	%r11, %rsi
	movq	%rax, (%rdi)
	movq	%rcx, 8(%rdi)
	movq	%rdx, 16(%rdi)
	movq	%rsi, 24(%rdi)
	movq	448(%rsp), %rax
	movq	456(%rsp), %rcx
	movq	%rcx, (%rax)
	movq	464(%rsp), %rcx
	movq	%rcx, 8(%rax)
	movq	472(%rsp), %rcx
	movq	%rcx, 16(%rax)
	movq	480(%rsp), %rcx
	movq	%rcx, 24(%rax)
	addq	$488, %rsp
	popq	%r15
	popq	%r14
	popq	%r13
	popq	%r12
	popq	%rbx
	popq	%rbp
	ret 
	.data
	.globl	___38
	.globl	__38
	.p2align	3
___38:
__38:
	.quad	38
