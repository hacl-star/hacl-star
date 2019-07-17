	.text
	.p2align	5
	.globl	_keccak_f1600
	.globl	keccak_f1600
_keccak_f1600:
keccak_f1600:
	pushq	%rbp
Lkeccak_f1600$1:
	leaq	16(%rsi), %rsi
	testb	$-1, %sil
	jne 	Lkeccak_f1600$1
	popq	%rbp
	ret 
