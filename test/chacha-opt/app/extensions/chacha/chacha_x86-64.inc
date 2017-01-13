SECTION_TEXT

GLOBAL_HIDDEN_FN_EXT chacha_blocks_x86, 4, 0
chacha_blocks_x86_local:
movq %rsp,%r11
andq $31,%r11
addq $256,%r11
subq %r11,%rsp
movq %rdi,%rdi
movq %rsi,%rsi
movq %rdx,%rdx
movq %rcx,%r8
cmpq $0,%r8
jbe chacha_blocks_x86_done
movq %r11,64(%rsp)
movq %r12,72(%rsp)
movq %r13,80(%rsp)
movq %r14,88(%rsp)
movq %r15,96(%rsp)
movq %rbx,104(%rsp)
movq %rbp,112(%rsp)
movq 0(%rdi),%rcx
movq 8(%rdi),%r9
movq 16(%rdi),%rax
movq 24(%rdi),%r10
movq 32(%rdi),%r11
movq 40(%rdi),%r12
movq 48(%rdi),%r13
movq %rcx,120(%rsp)
movq %r9,128(%rsp)
movq %rax,136(%rsp)
movq %r10,144(%rsp)
movq %r11,152(%rsp)
movq %r12,160(%rsp)
movq %r13,168(%rsp)
movq %rdi,176(%rsp)
chacha_blocks_x86_bytesatleast1:
cmpq $64,%r8
jae chacha_blocks_x86_nocopy
movq %rdx,184(%rsp)
cmpq $0,%rsi
jbe chacha_blocks_x86_noinput1
leaq 0(%rsp),%rdi
movq %r8,%rcx
rep movsb
leaq 0(%rsp),%rsi
chacha_blocks_x86_noinput1:
leaq 0(%rsp),%rdx
chacha_blocks_x86_nocopy:
movq %rdx,192(%rsp)
movq %rsi,200(%rsp)
movq %r8,208(%rsp)
movq $0x3320646e61707865,%rdi
movq %rdi,%rcx
shrq $32,%rdi
movq $0x6b20657479622d32,%rsi
movq %rsi,%r8
shrq $32,%rsi
movq 120(%rsp),%rdx
movq %rdx,%r9
shrq $32,%rdx
movq 128(%rsp),%rax
movq %rax,%r10
shrq $32,%rax
movq 136(%rsp),%r11
movq %r11,%r12
shrq $32,%r11
movq %r11,216(%rsp)
movq 144(%rsp),%r11
movq %r11,%r13
shrq $32,%r11
movq %r11,224(%rsp)
movq 152(%rsp),%r11
movq %r11,%r14
shrq $32,%r11
movq 160(%rsp),%r15
movq %r15,%rbx
shrq $32,%r15
movq 168(%rsp),%rbp
chacha_blocks_x86_mainloop:
movq %rbp,232(%rsp)
movq 216(%rsp),%rbp
addq %r9,%rcx
xorq %rcx,%r14
roll $16,%r14d
addq %rdx,%rdi
xorq %rdi,%r11
roll $16,%r11d
addq %r14,%r12
xorq %r12,%r9
roll $12,%r9d
addq %r11,%rbp
xorq %rbp,%rdx
roll $12,%edx
addq %r9,%rcx
xorq %rcx,%r14
roll $8,%r14d
addq %rdx,%rdi
xorq %rdi,%r11
roll $8,%r11d
addq %r14,%r12
xorq %r12,%r9
roll $7,%r9d
addq %r10,%r8
xorq %r8,%rbx
roll $16,%ebx
addq %r11,%rbp
xorq %rbp,%rdx
roll $7,%edx
movq %rbp,216(%rsp)
movq 224(%rsp),%rbp
addq %rax,%rsi
xorq %rsi,%r15
roll $16,%r15d
addq %rbx,%r13
xorq %r13,%r10
roll $12,%r10d
addq %r15,%rbp
xorq %rbp,%rax
roll $12,%eax
addq %r10,%r8
xorq %r8,%rbx
roll $8,%ebx
addq %rax,%rsi
xorq %rsi,%r15
roll $8,%r15d
addq %rbx,%r13
xorq %r13,%r10
roll $7,%r10d
addq %r15,%rbp
xorq %rbp,%rax
roll $7,%eax
addq %rdx,%rcx
xorq %rcx,%r15
roll $16,%r15d
addq %r10,%rdi
xorq %rdi,%r14
roll $16,%r14d
addq %r15,%r13
xorq %r13,%rdx
roll $12,%edx
addq %r14,%rbp
xorq %rbp,%r10
roll $12,%r10d
addq %rdx,%rcx
xorq %rcx,%r15
roll $8,%r15d
addq %r10,%rdi
xorq %rdi,%r14
roll $8,%r14d
addq %r15,%r13
xorq %r13,%rdx
roll $7,%edx
addq %rax,%r8
xorq %r8,%r11
roll $16,%r11d
addq %r14,%rbp
xorq %rbp,%r10
roll $7,%r10d
movq %rbp,224(%rsp)
movq 216(%rsp),%rbp
addq %r9,%rsi
xorq %rsi,%rbx
roll $16,%ebx
addq %r11,%r12
xorq %r12,%rax
roll $12,%eax
addq %rbx,%rbp
xorq %rbp,%r9
roll $12,%r9d
addq %rax,%r8
xorq %r8,%r11
roll $8,%r11d
addq %r9,%rsi
xorq %rsi,%rbx
roll $8,%ebx
addq %r11,%r12
xorq %r12,%rax
roll $7,%eax
addq %rbx,%rbp
xorq %rbp,%r9
roll $7,%r9d
addq %r9,%rcx
xorq %rcx,%r14
roll $16,%r14d
addq %rdx,%rdi
xorq %rdi,%r11
roll $16,%r11d
addq %r14,%r12
xorq %r12,%r9
roll $12,%r9d
addq %r11,%rbp
xorq %rbp,%rdx
roll $12,%edx
addq %r9,%rcx
xorq %rcx,%r14
roll $8,%r14d
addq %rdx,%rdi
xorq %rdi,%r11
roll $8,%r11d
addq %r14,%r12
xorq %r12,%r9
roll $7,%r9d
addq %r10,%r8
xorq %r8,%rbx
roll $16,%ebx
addq %r11,%rbp
xorq %rbp,%rdx
roll $7,%edx
movq %rbp,216(%rsp)
movq 224(%rsp),%rbp
addq %rax,%rsi
xorq %rsi,%r15
roll $16,%r15d
addq %rbx,%r13
xorq %r13,%r10
roll $12,%r10d
addq %r15,%rbp
xorq %rbp,%rax
roll $12,%eax
addq %r10,%r8
xorq %r8,%rbx
roll $8,%ebx
addq %rax,%rsi
xorq %rsi,%r15
roll $8,%r15d
addq %rbx,%r13
xorq %r13,%r10
roll $7,%r10d
addq %r15,%rbp
xorq %rbp,%rax
roll $7,%eax
addq %rdx,%rcx
xorq %rcx,%r15
roll $16,%r15d
addq %r10,%rdi
xorq %rdi,%r14
roll $16,%r14d
addq %r15,%r13
xorq %r13,%rdx
roll $12,%edx
addq %r14,%rbp
xorq %rbp,%r10
roll $12,%r10d
addq %rdx,%rcx
xorq %rcx,%r15
roll $8,%r15d
addq %r10,%rdi
xorq %rdi,%r14
roll $8,%r14d
addq %r15,%r13
xorq %r13,%rdx
roll $7,%edx
addq %rax,%r8
xorq %r8,%r11
roll $16,%r11d
addq %r14,%rbp
xorq %rbp,%r10
roll $7,%r10d
movq %rbp,224(%rsp)
movq 216(%rsp),%rbp
addq %r9,%rsi
xorq %rsi,%rbx
roll $16,%ebx
addq %r11,%r12
xorq %r12,%rax
roll $12,%eax
addq %rbx,%rbp
xorq %rbp,%r9
roll $12,%r9d
addq %rax,%r8
xorq %r8,%r11
roll $8,%r11d
addq %r9,%rsi
xorq %rsi,%rbx
roll $8,%ebx
addq %r11,%r12
xorq %r12,%rax
roll $7,%eax
addq %rbx,%rbp
xorq %rbp,%r9
roll $7,%r9d
movq %rbp,216(%rsp)
movq 232(%rsp),%rbp
subq $4,%rbp
ja chacha_blocks_x86_mainloop
addl $0x79622d32,%r8d
addl $0x6b206574,%esi
shlq $32,%rsi
addq %rsi,%r8
addl 128(%rsp),%r10d
shlq $32,%rax
addq 128(%rsp),%rax
shrq $32,%rax
shlq $32,%rax
addq %rax,%r10
movq 216(%rsp),%rsi
addl 136(%rsp),%r12d
shlq $32,%rsi
addq 136(%rsp),%rsi
shrq $32,%rsi
shlq $32,%rsi
addq %rsi,%r12
addl 152(%rsp),%r14d
shlq $32,%r11
addq 152(%rsp),%r11
shrq $32,%r11
shlq $32,%r11
addq %r11,%r14
addl $0x61707865,%ecx
addl $0x3320646e,%edi
shlq $32,%rdi
addq %rdi,%rcx
addl 120(%rsp),%r9d
shlq $32,%rdx
addq 120(%rsp),%rdx
shrq $32,%rdx
shlq $32,%rdx
addq %rdx,%r9
movq 224(%rsp),%rdi
addl 144(%rsp),%r13d
shlq $32,%rdi
addq 144(%rsp),%rdi
shrq $32,%rdi
shlq $32,%rdi
addq %rdi,%r13
addl 160(%rsp),%ebx
shlq $32,%r15
addq 160(%rsp),%r15
shrq $32,%r15
shlq $32,%r15
addq %r15,%rbx
movq 192(%rsp),%rdx
movq 200(%rsp),%rsi
cmpq $0,%rsi
jbe chacha_blocks_x86_noinput2
xorq 0(%rsi),%rcx
movq %rcx,0(%rdx)
xorq 8(%rsi),%r8
movq %r8,8(%rdx)
xorq 16(%rsi),%r9
movq %r9,16(%rdx)
xorq 24(%rsi),%r10
movq %r10,24(%rdx)
xorq 32(%rsi),%r12
movq %r12,32(%rdx)
xorq 40(%rsi),%r13
movq %r13,40(%rdx)
xorq 48(%rsi),%r14
movq %r14,48(%rdx)
xorq 56(%rsi),%rbx
movq %rbx,56(%rdx)
addq $64,%rsi
jmp chacha_blocks_x86_mainloop_cont
chacha_blocks_x86_noinput2:
movq %rcx,0(%rdx)
movq %r8,8(%rdx)
movq %r9,16(%rdx)
movq %r10,24(%rdx)
movq %r12,32(%rdx)
movq %r13,40(%rdx)
movq %r14,48(%rdx)
movq %rbx,56(%rdx)
chacha_blocks_x86_mainloop_cont:
movq 208(%rsp),%r8
movq 152(%rsp),%rdi
addq $1,%rdi
movq %rdi,152(%rsp)
cmpq $64,%r8
ja chacha_blocks_x86_bytesatleast65
jae chacha_blocks_x86_bytesatleast64
movq %rdx,%rsi
movq 184(%rsp),%rdi
movq %r8,%rcx
rep movsb
chacha_blocks_x86_bytesatleast64:
movq 176(%rsp),%rdi
movq 152(%rsp),%rsi
movq %rsi,32(%rdi)
movq 64(%rsp),%r11
movq 72(%rsp),%r12
movq 80(%rsp),%r13
movq 88(%rsp),%r14
movq 96(%rsp),%r15
movq 104(%rsp),%rbx
movq 112(%rsp),%rbp
chacha_blocks_x86_done:
addq %r11,%rsp
movq %rdi,%rax
movq %rsi,%rdx
ret
chacha_blocks_x86_bytesatleast65:
subq $64,%r8
addq $64,%rdx
jmp chacha_blocks_x86_bytesatleast1
FN_END chacha_blocks_x86

GLOBAL_HIDDEN_FN_EXT hchacha_x86, 4, 0
hchacha_x86_local:
pushq %r12
pushq %r13
pushq %r14
pushq %r15
pushq %rbx
pushq %rbp
subq $56, %rsp
movl $1634760805, %r15d
movl 28(%rdi), %r9d
movl $857760878, %r13d
movq %rcx, 40(%rsp)
movl $2036477234, %r12d
movq %rdx, 0(%rsp)
movl $1797285236, %r11d
movl (%rdi), %r8d
movl 4(%rdi), %ebp
movl 8(%rdi), %ebx
movl 12(%rdi), %ecx
movl 16(%rdi), %edx
movl 20(%rdi), %eax
movl 24(%rdi), %r14d
movl %r9d, 8(%rsp)
movl (%rsi), %r10d
movl 4(%rsi), %r9d
movl 8(%rsi), %edi
movl 12(%rsi), %esi
movl %esi, 16(%rsp)
movl %r14d, 24(%rsp)
movl %r15d, 32(%rsp)
movl 8(%rsp), %esi
hchacha_x86_2:
addl %ebp, %r13d
addl %ecx, %r11d
xorl %r13d, %r9d
addl %ebx, %r12d
roll $16, %r9d
xorl %r12d, %edi
addl %r9d, %eax
xorl %eax, %ebp
roll $12, %ebp
addl %ebp, %r13d
xorl %r13d, %r9d
roll $8, %r9d
addl %r9d, %eax
movl %eax, 8(%rsp)
xorl %eax, %ebp
movl 32(%rsp), %r14d
movl 16(%rsp), %eax
addl %r8d, %r14d
xorl %r11d, %eax
xorl %r14d, %r10d
roll $16, %eax
roll $16, %r10d
addl %eax, %esi
roll $16, %edi
addl %r10d, %edx
movl 24(%rsp), %r15d
xorl %esi, %ecx
addl %edi, %r15d
xorl %edx, %r8d
roll $12, %ecx
xorl %r15d, %ebx
roll $12, %r8d
addl %ecx, %r11d
roll $12, %ebx
addl %r8d, %r14d
roll $7, %ebp
addl %ebx, %r12d
xorl %r11d, %eax
xorl %r14d, %r10d
roll $8, %eax
xorl %r12d, %edi
addl %ebp, %r14d
addl %eax, %esi
roll $8, %edi
xorl %r14d, %eax
roll $16, %eax
addl %edi, %r15d
roll $8, %r10d
xorl %r15d, %ebx
addl %eax, %r15d
addl %r10d, %edx
xorl %r15d, %ebp
xorl %edx, %r8d
xorl %esi, %ecx
roll $12, %ebp
roll $7, %r8d
addl %ebp, %r14d
roll $7, %ebx
addl %r8d, %r11d
roll $7, %ecx
addl %ebx, %r13d
addl %ecx, %r12d
xorl %r14d, %eax
xorl %r13d, %r10d
xorl %r12d, %r9d
xorl %r11d, %edi
roll $8, %eax
roll $16, %r10d
addl %eax, %r15d
roll $16, %r9d
addl %r10d, %esi
roll $16, %edi
addl %r9d, %edx
movl %eax, 16(%rsp)
xorl %esi, %ebx
movl 8(%rsp), %eax
xorl %edx, %ecx
addl %edi, %eax
xorl %r15d, %ebp
xorl %eax, %r8d
roll $12, %ebx
roll $12, %ecx
addl %ebx, %r13d
roll $12, %r8d
addl %ecx, %r12d
addl %r8d, %r11d
xorl %r13d, %r10d
xorl %r12d, %r9d
xorl %r11d, %edi
roll $8, %r10d
roll $8, %r9d
addl %r10d, %esi
roll $8, %edi
addl %r9d, %edx
addl %edi, %eax
xorl %esi, %ebx
xorl %edx, %ecx
xorl %eax, %r8d
movl %r14d, 32(%rsp)
roll $7, %ebp
roll $7, %ebx
roll $7, %ecx
roll $7, %r8d
movq 40(%rsp), %r14
movl %r15d, 24(%rsp)
subq $2, %r14
movq %r14, 40(%rsp)
jne hchacha_x86_2
movq 0(%rsp), %rax
movl 16(%rsp), %esi
movl 32(%rsp), %r15d
movl %r15d, (%rax)
movl %r13d, 4(%rax)
movl %r12d, 8(%rax)
movl %r11d, 12(%rax)
movl %r10d, 16(%rax)
movl %r9d, 20(%rax)
movl %edi, 24(%rax)
movl %esi, 28(%rax)
addq $56, %rsp
popq %rbp
popq %rbx
popq %r15
popq %r14
popq %r13
popq %r12
ret
FN_END hchacha_x86

GLOBAL_HIDDEN_FN_EXT chacha_x86, 6, 2
pushq %rbp
movq %rsp, %rbp
subq $64, %rsp
andq $~63, %rsp
movdqu 0(%rdi), %xmm0
movdqu 16(%rdi), %xmm1
movdqa %xmm0, 0(%rsp)
movdqa %xmm1, 16(%rsp)
xorq %rdi, %rdi
movq %rdi, 32(%rsp)
movq 0(%rsi), %rsi
movq %rsi, 40(%rsp)
movq %r9, 48(%rsp)
movq %rsp, %rdi
movq %rdx, %rsi
movq %rcx, %rdx
movq %r8, %rcx
call chacha_blocks_x86_local
pxor %xmm0, %xmm0
movdqa %xmm0, 0(%rsp)
movdqa %xmm0, 16(%rsp)
movdqa %xmm0, 32(%rsp)
movq %rbp, %rsp
popq %rbp
ret
FN_END chacha_x86

GLOBAL_HIDDEN_FN_EXT xchacha_x86, 6, 0
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
call hchacha_x86_local
movq %rbx, %rdi
popq %rcx
popq %rdx
popq %rsi
call chacha_blocks_x86_local
pxor %xmm0, %xmm0
movdqa %xmm0, 0(%rbx)
movdqa %xmm0, 16(%rbx)
movdqa %xmm0, 32(%rbx)
movq %rbp, %rsp
popq %rbx
popq %rbp
ret
FN_END xchacha_x86

