SECTION_TEXT

GLOBAL_HIDDEN_FN poly1305_block_size_x86
movl $16, %eax
ret
FN_END poly1305_block_size_x86

GLOBAL_HIDDEN_FN poly1305_init_ext_x86
poly1305_init_ext_x86_local:
movabsq $17575274610687, %rax
movq (%rsi), %rcx
movq 8(%rsi), %rdx
movq $0, 24(%rdi)
movq $0, 32(%rdi)
movq $0, 40(%rdi)
andq %rcx, %rax
shrq $44, %rcx
movq %rax, (%rdi)
movq %rdx, %rax
salq $20, %rax
orq %rcx, %rax
movabsq $17592181915647, %rcx
andq %rcx, %rax
movq %rax, 8(%rdi)
movq %rdx, %rax
movabsq $68719475727, %rdx
shrq $24, %rax
andq %rdx, %rax
movq %rax, 16(%rdi)
movq 16(%rsi), %rax
movq %rax, 48(%rdi)
movq 24(%rsi), %rax
movq $0, 64(%rdi)
movq %rax, 56(%rdi)
ret
FN_END poly1305_init_ext_x86


GLOBAL_HIDDEN_FN poly1305_blocks_x86
poly1305_blocks_x86_local:
movabsq $1099511627776, %rax
pushq %r15
pushq %r14
pushq %r13
pushq %r12
pushq %rbp
movq %rdx, %rbp
pushq %rbx
cmpq $1, 64(%rdi)
movq %rdi, -16(%rsp)
movq (%rdi), %r14
movq 8(%rdi), %r15
sbbq %rcx, %rcx
andq %rax, %rcx
movq %rdi, %rax
cmpq $15, %rbp
movq %rcx, -40(%rsp)
movq 16(%rdi), %rcx
movq 32(%rax), %r8
movq 24(%rdi), %rdi
movq 40(%rax), %rdx
movq %rcx, -32(%rsp)
jbe poly1305_blocks_x86_5
leaq (%rcx,%rcx,4), %rax
movq %r15, -48(%rsp)
movabsq $17592186044415, %rbx
salq $2, %rax
movq %rax, -56(%rsp)
leaq (%r15,%r15,4), %rax
salq $2, %rax
movq %rax, -24(%rsp)
.p2align 4
poly1305_blocks_x86_6:
movq $0, -80(%rsp)
movq (%rsi), %r9
movq $0, -64(%rsp)
movq 8(%rsi), %rcx
movq %r9, %rax
shrq $44, %r9
movq %rcx, %r10
shrq $24, %rcx
andq %rbx, %rax
orq -40(%rsp), %rcx
addq %rax, %rdi
salq $20, %r10
movq -24(%rsp), %rax
orq %r9, %r10
andq %rbx, %r10
addq %r10, %r8
addq %rdx, %rcx
mulq %rcx
movq %rax, %r9
movq %rdi, %rax
movq %rdx, %r10
mulq %r14
addq %rax, %r9
movq -56(%rsp), %rax
adcq %rdx, %r10
mulq %r8
addq %rax, %r9
movq -56(%rsp), %rax
adcq %rdx, %r10
movq %r9, %r15
andq %rbx, %r15
mulq %rcx
movq %rax, %r11
movq -48(%rsp), %rax
movq %rdx, %r12
mulq %rdi
addq %rax, %r11
movq %r8, %rax
adcq %rdx, %r12
mulq %r14
addq %rax, %r11
movq %rcx, %rax
adcq %rdx, %r12
shrdq $44, %r10, %r9
movq %r9, -88(%rsp)
addq -88(%rsp), %r11
adcq -80(%rsp), %r12
mulq %r14
movq %r11, %r13
andq %rbx, %r13
movq %rax, %r9
movq -32(%rsp), %rax
movq %rdx, %r10
mulq %rdi
addq %rax, %r9
movq -48(%rsp), %rax
adcq %rdx, %r10
mulq %r8
addq %rax, %r9
adcq %rdx, %r10
shrdq $44, %r12, %r11
movabsq $4398046511103, %rdx
movq %r11, -72(%rsp)
addq -72(%rsp), %r9
adcq -64(%rsp), %r10
andq %r9, %rdx
subq $16, %rbp
addq $16, %rsi
shrdq $42, %r10, %r9
leaq (%r9,%r9,4), %r8
addq %r15, %r8
movq %r8, %rdi
shrq $44, %r8
andq %rbx, %rdi
addq %r13, %r8
cmpq $15, %rbp
ja poly1305_blocks_x86_6
poly1305_blocks_x86_5:
movq -16(%rsp), %rcx
movq %rdi, 24(%rcx)
movq %r8, 32(%rcx)
movq %rdx, 40(%rcx)
popq %rbx
popq %rbp
popq %r12
popq %r13
popq %r14
popq %r15
ret
FN_END poly1305_blocks_x86

GLOBAL_HIDDEN_FN poly1305_finish_ext_x86
poly1305_finish_ext_x86_local:
pushq %rbp
movq %rsi, %rax
movq %rcx, %rbp
pushq %rbx
movq %rdi, %rbx
subq $24, %rsp
testq %rdx, %rdx
je poly1305_finish_ext_x86_11
movq %rax, %rdi
movq $0, (%rsp)
movq %rsp, %rcx
movq $0, 8(%rsp)
subq %rsp, %rdi
testb $8, %dl
je poly1305_finish_ext_x86_12
movq (%rax), %rax
leaq 8(%rsp), %rcx
movq %rax, (%rsp)
poly1305_finish_ext_x86_12:
testb $4, %dl
je poly1305_finish_ext_x86_13
movl (%rcx,%rdi), %eax
movl %eax, (%rcx)
addq $4, %rcx
poly1305_finish_ext_x86_13:
testb $2, %dl
je poly1305_finish_ext_x86_14
movzwl (%rcx,%rdi), %eax
movw %ax, (%rcx)
addq $2, %rcx
poly1305_finish_ext_x86_14:
testb $1, %dl
je poly1305_finish_ext_x86_15
movzbl (%rcx,%rdi), %eax
movb %al, (%rcx)
poly1305_finish_ext_x86_15:
movb $1, (%rsp,%rdx)
movq %rsp, %rsi
movl $16, %edx
movq $1, 64(%rbx)
movq %rbx, %rdi
call poly1305_blocks_x86
poly1305_finish_ext_x86_11:
movabsq $17592186044415, %rdx
movq 32(%rbx), %rsi
movabsq $4398046511103, %rax
movabsq $-4398046511104, %r10
movq %rsi, %r9
shrq $44, %rsi
addq 40(%rbx), %rsi
andq %rdx, %r9
movq %rsi, %r8
shrq $42, %rsi
leaq (%rsi,%rsi,4), %rcx
andq %rax, %r8
addq 24(%rbx), %rcx
movq %rcx, %rdi
shrq $44, %rcx
addq %r9, %rcx
andq %rdx, %rdi
movq %rcx, %rsi
shrq $44, %rcx
addq %r8, %rcx
andq %rdx, %rsi
andq %rcx, %rax
shrq $42, %rcx
leaq (%rdi,%rcx,4), %rdi
addq %rax, %r10
addq %rcx, %rdi
movq %rdi, %rcx
shrq $44, %rdi
andq %rdx, %rcx
addq %rsi, %rdi
leaq 5(%rcx), %r9
movq %r9, %r11
andq %rdx, %r9
shrq $44, %r11
addq %rdi, %r11
movq %r11, %rsi
andq %r11, %rdx
shrq $44, %rsi
addq %rsi, %r10
movq %r10, %rsi
shrq $63, %rsi
subq $1, %rsi
movq %rsi, %r8
andq %rsi, %r9
andq %rsi, %rdx
notq %r8
andq %r8, %rcx
andq %r8, %rdi
orq %r9, %rcx
orq %rdx, %rdi
andq %r8, %rax
andq %r10, %rsi
movq %rdi, %rdx
shrq $20, %rdi
orq %rsi, %rax
salq $44, %rdx
movq 56(%rbx), %rsi
salq $24, %rax
orq %rdx, %rcx
movq 48(%rbx), %rdx
orq %rdi, %rax
addq %rdx, %rcx
adcq %rsi, %rax
movq %rcx, 0(%rbp)
movq %rax, 8(%rbp)
movq $0, 24(%rbx)
movq $0, 32(%rbx)
movq $0, 40(%rbx)
movq $0, (%rbx)
movq $0, 8(%rbx)
movq $0, 16(%rbx)
movq $0, 48(%rbx)
movq $0, 56(%rbx)
addq $24, %rsp
popq %rbx
popq %rbp
ret
FN_END poly1305_finish_ext_x86


GLOBAL_HIDDEN_FN poly1305_auth_x86
poly1305_auth_x86_local:
pushq %rbp
movq %rsp, %rbp
movq %rbx, -32(%rbp)
movq %rdx, %rbx
movq %r12, -24(%rbp)
movq %rsi, %r12
movq %rcx, %rsi
movq %r13, -16(%rbp)
movq %rdi, %r13
movq %r14, -8(%rbp)
subq $32, %rsp
movq %rbx, %r14
andq $-64, %rsp
addq $-128, %rsp
movq %rsp, %rdi
call poly1305_init_ext_x86_local
andq $-16, %r14
je poly1305_auth_x86_19
movq %r12, %rsi
movq %r14, %rdx
movq %rsp, %rdi
call poly1305_blocks_x86_local
addq %r14, %r12
subq %r14, %rbx
poly1305_auth_x86_19:
movq %r13, %rcx
movq %rbx, %rdx
movq %r12, %rsi
movq %rsp, %rdi
call poly1305_finish_ext_x86_local
movq -32(%rbp), %rbx
movq -24(%rbp), %r12
movq -16(%rbp), %r13
movq -8(%rbp), %r14
leave
ret
FN_END poly1305_auth_x86

