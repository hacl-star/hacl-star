	.text
	.p2align	5
	.globl	_poly1305_ref3
	.globl	poly1305_ref3
_poly1305_ref3:
poly1305_ref3:
	pushq	%rbp
	pushq	%rbx
	pushq	%r12
	pushq	%r13
	pushq	%r14
	pushq	%r15
	subq	$16, %rsp
	movq	$0, %r8
	movq	$0, %r9
	movq	$0, %r10
	movq	(%rcx), %r11
	movq	8(%rcx), %rbp
	movq	$1152921487695413247, %rax
	andq	%rax, %r11
	movq	$1152921487695413244, %rax
	andq	%rax, %rbp
	movq	%rbp, %rbx
	shrq	$2, %rbx
	addq	%rbp, %rbx
	addq	$16, %rcx
	movq	%rdx, %r12
	jmp 	Lpoly1305_ref3$4
.p2align 5,,
Lpoly1305_ref3$5:
	addq	(%rsi), %r8
	adcq	8(%rsi), %r9
	adcq	$1, %r10
	movq	%rbx, %r13
	imulq	%r10, %r13
	imulq	%r11, %r10
	movq	%r11, %rax
	mulq	%r8
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	%r11, %rax
	mulq	%r9
	addq	%rax, %r15
	adcq	%rdx, %r10
	movq	%rbx, %rax
	mulq	%r9
	movq	%rdx, %r9
	addq	%r13, %r9
	movq	%rax, %r13
	movq	%rbp, %rax
	mulq	%r8
	addq	%r13, %r14
	adcq	%rax, %r15
	adcq	%rdx, %r10
	movq	$-4, %r8
	movq	%r10, %rax
	shrq	$2, %rax
	andq	%r10, %r8
	addq	%rax, %r8
	andq	$3, %r10
	addq	%r14, %r8
	adcq	%r15, %r9
	adcq	$0, %r10
	addq	$16, %rsi
	addq	$-16, %r12
Lpoly1305_ref3$4:
	cmpq	$16, %r12
	jnb 	Lpoly1305_ref3$5
	cmpq	$0, %r12
	jbe 	Lpoly1305_ref3$1
	movq	$0, (%rsp)
	movq	$0, 8(%rsp)
	movq	$0, %rax
	jmp 	Lpoly1305_ref3$2
Lpoly1305_ref3$3:
	movb	(%rsi,%rax), %dl
	movb	%dl, (%rsp,%rax)
	incq	%rax
Lpoly1305_ref3$2:
	cmpq	%r12, %rax
	jb  	Lpoly1305_ref3$3
	movb	$1, (%rsp,%rax)
	addq	(%rsp), %r8
	adcq	8(%rsp), %r9
	adcq	$0, %r10
	movq	%rbx, %rsi
	imulq	%r10, %rsi
	imulq	%r11, %r10
	movq	%r11, %rax
	mulq	%r8
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	%r11, %rax
	mulq	%r9
	addq	%rax, %r13
	adcq	%rdx, %r10
	movq	%rbx, %rax
	mulq	%r9
	movq	%rdx, %r9
	addq	%rsi, %r9
	movq	%rax, %rsi
	movq	%rbp, %rax
	mulq	%r8
	addq	%rsi, %r12
	adcq	%rax, %r13
	adcq	%rdx, %r10
	movq	$-4, %r8
	movq	%r10, %rax
	shrq	$2, %rax
	andq	%r10, %r8
	addq	%rax, %r8
	andq	$3, %r10
	addq	%r12, %r8
	adcq	%r13, %r9
	adcq	$0, %r10
Lpoly1305_ref3$1:
	movq	%r8, %rax
	movq	%r9, %rdx
	movq	%r10, %rsi
	addq	$5, %rax
	adcq	$0, %rdx
	adcq	$0, %rsi
	shrq	$2, %rsi
	negq	%rsi
	xorq	%r8, %rax
	xorq	%r9, %rdx
	andq	%rsi, %rax
	andq	%rsi, %rdx
	xorq	%r8, %rax
	xorq	%r9, %rdx
	movq	(%rcx), %rsi
	movq	8(%rcx), %rcx
	addq	%rsi, %rax
	adcq	%rcx, %rdx
	movq	%rax, (%rdi)
	movq	%rdx, 8(%rdi)
	addq	$16, %rsp
	popq	%r15
	popq	%r14
	popq	%r13
	popq	%r12
	popq	%rbx
	popq	%rbp
	ret 
