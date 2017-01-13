SECTION_TEXT

GLOBAL_HIDDEN_FN chacha_blocks_x86
chacha_blocks_x86_local:
pushl %esi
pushl %edi
pushl %ebx
pushl %ebp
subl $204, %esp
movl 232(%esp), %eax
movl 236(%esp), %edi
testl %edi, %edi
movl 228(%esp), %esi
movl %eax, 76(%esp)
movl %eax, (%esp)
jne chacha_blocks_x86_3
addl $204, %esp
popl %ebp
popl %ebx
popl %edi
popl %esi
ret
chacha_blocks_x86_3:
movl 224(%esp), %ebx
movl 24(%ebx), %ebp
movl %ebp, 120(%esp)
movl 28(%ebx), %ebp
movl %ebp, 108(%esp)
movl 32(%ebx), %ebp
movl %ebp, 80(%esp)
movl (%ebx), %eax
movl 4(%ebx), %edx
movl 8(%ebx), %ecx
movl 36(%ebx), %ebp
movl %eax, 112(%esp)
movl %edx, 116(%esp)
movl %ecx, 124(%esp)
movl %ebp, 84(%esp)
movl 12(%ebx), %ecx
movl 16(%ebx), %edx
movl 20(%ebx), %eax
movl 40(%ebx), %ebp
movl 44(%ebx), %ebx
movl %ebp, 104(%esp)
movl %ebx, 100(%esp)
movl %eax, 96(%esp)
movl %edx, 92(%esp)
movl %ecx, 88(%esp)
jmp chacha_blocks_x86_4
chacha_blocks_x86_22:
movl 76(%esp), %eax
addl $-64, %edi
addl $64, %eax
movl %eax, 76(%esp)
chacha_blocks_x86_4:
cmpl $64, %edi
jae chacha_blocks_x86_15
testl %esi, %esi
je chacha_blocks_x86_14
testl %edi, %edi
jbe chacha_blocks_x86_13
movl %edi, %ecx
shrl $1, %ecx
testl %ecx, %ecx
jbe chacha_blocks_x86_23
xorl %ebx, %ebx
chacha_blocks_x86_9:
movzbl (%esi,%ebx,2), %edx
movb %dl, 4(%esp,%ebx,2)
movzbl 1(%esi,%ebx,2), %eax
movb %al, 5(%esp,%ebx,2)
incl %ebx
cmpl %ecx, %ebx
jb chacha_blocks_x86_9
lea 1(%ebx,%ebx), %edx
chacha_blocks_x86_11:
lea -1(%edx), %eax
cmpl %edi, %eax
jae chacha_blocks_x86_13
movzbl (%eax,%esi), %eax
movb %al, 3(%esp,%edx)
chacha_blocks_x86_13:
lea 4(%esp), %esi
chacha_blocks_x86_14:
movl 76(%esp), %eax
lea 4(%esp), %edx
movl %eax, (%esp)
movl %edx, 76(%esp)
chacha_blocks_x86_15:
movl 96(%esp), %ebp
movl %ebp, 168(%esp)
movl 80(%esp), %ebp
movl 124(%esp), %edx
movl 88(%esp), %ebx
movl %ebp, 180(%esp)
movl 224(%esp), %ebp
movl %edx, 148(%esp)
movl %ebx, 152(%esp)
movl 120(%esp), %edx
movl 108(%esp), %ebx
movl %edx, 136(%esp)
movl 116(%esp), %eax
movl 84(%esp), %edx
movl %ebx, 140(%esp)
movl 100(%esp), %ebx
movl 48(%ebp), %ebp
testl %ebp, %ebp
movl %eax, 144(%esp)
movl %edx, 176(%esp)
movl 112(%esp), %ecx
movl 92(%esp), %eax
movl 104(%esp), %edx
movl %ebx, 132(%esp)
movl $1634760805, %ebx
movl $857760878, 160(%esp)
movl $2036477234, 164(%esp)
movl $1797285236, 172(%esp)
jbe chacha_blocks_x86_19
movl %ebx, 156(%esp)
movl %ebp, 128(%esp)
movl %edi, 72(%esp)
movl %esi, 68(%esp)
chacha_blocks_x86_17:
movl 156(%esp), %ebp
addl %ecx, %ebp
movl 180(%esp), %edi
xorl %ebp, %edi
roll $16, %edi
addl %edi, %eax
xorl %eax, %ecx
roll $12, %ecx
addl %ecx, %ebp
xorl %ebp, %edi
roll $8, %edi
addl %edi, %eax
xorl %eax, %ecx
movl %eax, 184(%esp)
movl 144(%esp), %esi
movl 160(%esp), %eax
addl %esi, %eax
roll $7, %ecx
movl %ecx, 188(%esp)
movl 176(%esp), %ecx
xorl %eax, %ecx
roll $16, %ecx
movl 168(%esp), %ebx
addl %ecx, %ebx
xorl %ebx, %esi
roll $12, %esi
addl %esi, %eax
movl %edi, 180(%esp)
xorl %eax, %ecx
movl %eax, 160(%esp)
movl 148(%esp), %edi
movl 164(%esp), %eax
addl %edi, %eax
xorl %eax, %edx
roll $8, %ecx
roll $16, %edx
addl %ecx, %ebx
movl %ecx, 176(%esp)
xorl %ebx, %esi
movl 136(%esp), %ecx
addl %edx, %ecx
xorl %ecx, %edi
roll $12, %edi
addl %edi, %eax
xorl %eax, %edx
roll $8, %edx
addl %edx, %ecx
xorl %ecx, %edi
movl %ebx, 168(%esp)
movl %edx, 192(%esp)
movl 152(%esp), %edx
movl 172(%esp), %ebx
addl %edx, %ebx
roll $7, %edi
movl %edi, 148(%esp)
movl 132(%esp), %edi
xorl %ebx, %edi
roll $16, %edi
movl %eax, 164(%esp)
movl 140(%esp), %eax
addl %edi, %eax
xorl %eax, %edx
roll $12, %edx
addl %edx, %ebx
roll $7, %esi
xorl %ebx, %edi
roll $8, %edi
addl %esi, %ebp
addl %edi, %eax
xorl %ebp, %edi
roll $16, %edi
xorl %eax, %edx
addl %edi, %ecx
xorl %ecx, %esi
roll $12, %esi
addl %esi, %ebp
xorl %ebp, %edi
roll $8, %edi
addl %edi, %ecx
xorl %ecx, %esi
movl %ebp, 156(%esp)
movl %ecx, 136(%esp)
movl 148(%esp), %ecx
movl 160(%esp), %ebp
addl %ecx, %ebp
roll $7, %esi
movl %esi, 144(%esp)
movl 180(%esp), %esi
xorl %ebp, %esi
roll $16, %esi
addl %esi, %eax
xorl %eax, %ecx
roll $12, %ecx
addl %ecx, %ebp
roll $7, %edx
xorl %ebp, %esi
movl %ebp, 160(%esp)
movl 164(%esp), %ebp
addl %edx, %ebp
movl %edi, 132(%esp)
roll $8, %esi
movl 176(%esp), %edi
addl %esi, %eax
xorl %ebp, %edi
xorl %eax, %ecx
roll $16, %edi
movl %eax, 140(%esp)
movl 184(%esp), %eax
addl %edi, %eax
xorl %eax, %edx
roll $12, %edx
addl %edx, %ebp
xorl %ebp, %edi
roll $8, %edi
addl %edi, %eax
roll $7, %ecx
xorl %eax, %edx
movl %ecx, 148(%esp)
movl 188(%esp), %ecx
addl %ecx, %ebx
roll $7, %edx
movl %edx, 152(%esp)
movl 192(%esp), %edx
xorl %ebx, %edx
roll $16, %edx
movl %ebp, 164(%esp)
movl 168(%esp), %ebp
addl %edx, %ebp
xorl %ebp, %ecx
roll $12, %ecx
addl %ecx, %ebx
xorl %ebx, %edx
roll $8, %edx
addl %edx, %ebp
xorl %ebp, %ecx
movl %ebx, 172(%esp)
roll $7, %ecx
movl 128(%esp), %ebx
movl %esi, 180(%esp)
addl $-2, %ebx
movl %edi, 176(%esp)
movl %ebp, 168(%esp)
movl %ebx, 128(%esp)
jne chacha_blocks_x86_17
movl 156(%esp), %ebx
movl 72(%esp), %edi
movl 68(%esp), %esi
chacha_blocks_x86_19:
addl $1634760805, %ebx
testl %esi, %esi
je chacha_blocks_x86_30
movl (%esi), %ebp
xorl %ebx, %ebp
movl 76(%esp), %ebx
addl 112(%esp), %ecx
addl 92(%esp), %eax
movl %ebp, (%ebx)
movl 160(%esp), %ebp
addl $857760878, %ebp
xorl 4(%esi), %ebp
movl %ebp, 4(%ebx)
movl 164(%esp), %ebp
addl $2036477234, %ebp
xorl 8(%esi), %ebp
movl %ebp, 8(%ebx)
movl 172(%esp), %ebp
addl $1797285236, %ebp
xorl 12(%esi), %ebp
movl %ebp, 12(%ebx)
xorl 16(%esi), %ecx
movl %ecx, 16(%ebx)
movl 144(%esp), %ecx
addl 116(%esp), %ecx
movl 148(%esp), %ebp
xorl 20(%esi), %ecx
movl %ecx, 20(%ebx)
addl 124(%esp), %ebp
movl 152(%esp), %ecx
xorl 24(%esi), %ebp
movl %ebp, 24(%ebx)
addl 88(%esp), %ecx
xorl 28(%esi), %ecx
movl %ecx, 28(%ebx)
xorl 32(%esi), %eax
movl %eax, 32(%ebx)
movl 168(%esp), %eax
addl 96(%esp), %eax
movl 136(%esp), %ecx
xorl 36(%esi), %eax
movl %eax, 36(%ebx)
addl 120(%esp), %ecx
movl 140(%esp), %ebp
xorl 40(%esi), %ecx
movl %ecx, 40(%ebx)
addl 108(%esp), %ebp
movl 180(%esp), %eax
xorl 44(%esi), %ebp
movl %ebp, 44(%ebx)
addl 80(%esp), %eax
movl 176(%esp), %ecx
xorl 48(%esi), %eax
movl %eax, 48(%ebx)
addl 84(%esp), %ecx
xorl 52(%esi), %ecx
movl %ecx, 52(%ebx)
addl 104(%esp), %edx
xorl 56(%esi), %edx
movl %edx, 56(%ebx)
movl 132(%esp), %edx
addl 100(%esp), %edx
xorl 60(%esi), %edx
addl $64, %esi
movl %edx, 60(%ebx)
chacha_blocks_x86_21:
movl 84(%esp), %edx
incl 80(%esp)
lea 1(%edx), %eax
jne ..L2
movl %eax, %edx
..L2:
movl %edx, 84(%esp)
cmpl $64, %edi
jbe chacha_blocks_x86_24
jmp chacha_blocks_x86_22
chacha_blocks_x86_23:
movl $1, %edx
jmp chacha_blocks_x86_11
chacha_blocks_x86_24:
jae chacha_blocks_x86_29
testl %edi, %edi
jbe chacha_blocks_x86_29
movl (%esp), %ecx
xorl %edx, %edx
movl 76(%esp), %ebx
chacha_blocks_x86_27:
movzbl (%edx,%ebx), %eax
movb %al, (%edx,%ecx)
incl %edx
cmpl %edi, %edx
jb chacha_blocks_x86_27
chacha_blocks_x86_29:
movl 224(%esp), %ecx
movl 80(%esp), %eax
movl 84(%esp), %edx
movl %eax, 32(%ecx)
movl %edx, 36(%ecx)
addl $204, %esp
popl %ebp
popl %ebx
popl %edi
popl %esi
ret
chacha_blocks_x86_30:
movl 76(%esp), %ebp
addl 112(%esp), %ecx
addl 92(%esp), %eax
movl %ecx, 16(%ebp)
movl 144(%esp), %ecx
addl 116(%esp), %ecx
movl %ecx, 20(%ebp)
movl 152(%esp), %ecx
movl %ebx, (%ebp)
movl 160(%esp), %ebx
addl $857760878, %ebx
movl %ebx, 4(%ebp)
movl 164(%esp), %ebx
addl 88(%esp), %ecx
addl $2036477234, %ebx
movl %ebx, 8(%ebp)
movl 172(%esp), %ebx
addl $1797285236, %ebx
movl %ebx, 12(%ebp)
movl %ecx, 28(%ebp)
movl %eax, 32(%ebp)
movl 148(%esp), %ebx
movl 168(%esp), %eax
movl 136(%esp), %ecx
addl 124(%esp), %ebx
addl 96(%esp), %eax
addl 120(%esp), %ecx
addl 104(%esp), %edx
movl %ebx, 24(%ebp)
movl %eax, 36(%ebp)
movl %ecx, 40(%ebp)
movl %edx, 56(%ebp)
movl 140(%esp), %ebx
movl 180(%esp), %eax
movl 176(%esp), %ecx
movl 132(%esp), %edx
addl 108(%esp), %ebx
addl 80(%esp), %eax
addl 84(%esp), %ecx
addl 100(%esp), %edx
movl %ebx, 44(%ebp)
movl %eax, 48(%ebp)
movl %ecx, 52(%ebp)
movl %edx, 60(%ebp)
jmp chacha_blocks_x86_21
FN_END chacha_blocks_x86

GLOBAL_HIDDEN_FN hchacha_x86
hchacha_x86_local:
pushl %esi
pushl %edi
pushl %ebx
pushl %ebp
subl $76, %esp
movl 96(%esp), %edx
movl 100(%esp), %ebp
movl 108(%esp), %eax
movl 24(%edx), %edi
movl %edi, 44(%esp)
movl 20(%edx), %esi
movl 4(%ebp), %edi
movl %eax, 52(%esp)
movl %esi, 48(%esp)
movl %edi, 36(%esp)
movl (%edx), %ecx
movl 4(%edx), %eax
movl (%ebp), %esi
movl 8(%ebp), %edi
movl 12(%ebp), %ebp
movl %ecx, 56(%esp)
movl %eax, 60(%esp)
movl 8(%edx), %ecx
movl 12(%edx), %ebx
movl 16(%edx), %eax
movl %ebp, (%esp)
movl $1797285236, %ebp
movl 28(%edx), %edx
movl %edi, 40(%esp)
movl %ebp, 16(%esp)
movl %ebx, 12(%esp)
movl $1634760805, 28(%esp)
movl $857760878, 24(%esp)
movl $2036477234, 20(%esp)
movl 48(%esp), %ebp
movl 56(%esp), %ebx
movl %esi, 32(%esp)
movl %edx, 4(%esp)
movl %ecx, 8(%esp)
hchacha_x86_mainloop:
movl 28(%esp), %edx
addl %ebx, %edx
movl 32(%esp), %ecx
xorl %edx, %ecx
roll $16, %ecx
addl %ecx, %eax
xorl %eax, %ebx
roll $12, %ebx
addl %ebx, %edx
xorl %edx, %ecx
roll $8, %ecx
addl %ecx, %eax
xorl %eax, %ebx
movl %eax, 64(%esp)
movl 60(%esp), %esi
movl 24(%esp), %eax
addl %esi, %eax
roll $7, %ebx
movl %ebx, 56(%esp)
movl 36(%esp), %ebx
xorl %eax, %ebx
roll $16, %ebx
addl %ebx, %ebp
xorl %ebp, %esi
roll $12, %esi
addl %esi, %eax
movl 52(%esp), %edi
xorl %eax, %ebx
addl $-2, %edi
movl %edi, 52(%esp)
movl %eax, 24(%esp)
movl 8(%esp), %edi
movl 20(%esp), %eax
addl %edi, %eax
movl %ecx, 32(%esp)
roll $8, %ebx
movl 40(%esp), %ecx
addl %ebx, %ebp
xorl %eax, %ecx
xorl %ebp, %esi
roll $16, %ecx
movl %ebp, 48(%esp)
movl 44(%esp), %ebp
addl %ecx, %ebp
xorl %ebp, %edi
roll $12, %edi
addl %edi, %eax
xorl %eax, %ecx
roll $8, %ecx
addl %ecx, %ebp
xorl %ebp, %edi
movl %ebx, 36(%esp)
movl %ecx, 40(%esp)
movl 12(%esp), %ebx
movl 16(%esp), %ecx
addl %ebx, %ecx
roll $7, %edi
movl %edi, 8(%esp)
movl (%esp), %edi
xorl %ecx, %edi
roll $16, %edi
movl %eax, 20(%esp)
movl 4(%esp), %eax
addl %edi, %eax
xorl %eax, %ebx
roll $12, %ebx
addl %ebx, %ecx
roll $7, %esi
xorl %ecx, %edi
roll $8, %edi
addl %esi, %edx
addl %edi, %eax
xorl %edx, %edi
roll $16, %edi
xorl %eax, %ebx
addl %edi, %ebp
xorl %ebp, %esi
roll $12, %esi
addl %esi, %edx
xorl %edx, %edi
roll $8, %edi
addl %edi, %ebp
xorl %ebp, %esi
roll $7, %esi
movl %ebp, 44(%esp)
movl %esi, 60(%esp)
movl 8(%esp), %esi
movl 24(%esp), %ebp
addl %esi, %ebp
movl %edx, 28(%esp)
movl 32(%esp), %edx
xorl %ebp, %edx
roll $16, %edx
addl %edx, %eax
xorl %eax, %esi
roll $12, %esi
addl %esi, %ebp
xorl %ebp, %edx
roll $7, %ebx
movl %ebp, 24(%esp)
roll $8, %edx
movl 20(%esp), %ebp
addl %edx, %eax
addl %ebx, %ebp
xorl %eax, %esi
movl %edx, 32(%esp)
movl 36(%esp), %edx
xorl %ebp, %edx
roll $16, %edx
movl %eax, 4(%esp)
movl 64(%esp), %eax
addl %edx, %eax
xorl %eax, %ebx
roll $12, %ebx
addl %ebx, %ebp
xorl %ebp, %edx
roll $8, %edx
addl %edx, %eax
xorl %eax, %ebx
roll $7, %ebx
movl %ebx, 12(%esp)
movl 56(%esp), %ebx
addl %ebx, %ecx
movl %edi, (%esp)
movl 40(%esp), %edi
xorl %ecx, %edi
roll $16, %edi
movl %ebp, 20(%esp)
movl 48(%esp), %ebp
addl %edi, %ebp
xorl %ebp, %ebx
roll $12, %ebx
addl %ebx, %ecx
xorl %ecx, %edi
roll $8, %edi
addl %edi, %ebp
xorl %ebp, %ebx
roll $7, %esi
roll $7, %ebx
movl %esi, 8(%esp)
movl %edx, 36(%esp)
movl %ecx, 16(%esp)
movl %edi, 40(%esp)
cmpl $0, 52(%esp)
jne hchacha_x86_mainloop
movl 104(%esp), %eax
movl %ecx, %ebp
movl 32(%esp), %esi
movl %ebp, 12(%eax)
movl %esi, 16(%eax)
movl %edx, %edi
movl 28(%esp), %edx
movl 24(%esp), %ecx
movl 20(%esp), %ebx
movl 40(%esp), %ebp
movl (%esp), %esi
movl %edx, (%eax)
movl %ecx, 4(%eax)
movl %ebx, 8(%eax)
movl %edi, 20(%eax)
movl %ebp, 24(%eax)
movl %esi, 28(%eax)
addl $76, %esp
popl %ebp
popl %ebx
popl %edi
popl %esi
ret
FN_END hchacha_x86

GLOBAL_HIDDEN_FN chacha_x86
pushl %ebp
pushl %ebx
movl %esp, %ebp
subl $64, %esp
andl $~63, %esp
movl %esp, %ebx
movl 12(%ebp), %ecx
xorl %edx, %edx
movl 0(%ecx), %eax
movl %eax, 0(%ebx)
movl 4(%ecx), %eax
movl %eax, 4(%ebx)
movl 8(%ecx), %eax
movl %eax, 8(%ebx)
movl 12(%ecx), %eax
movl %eax, 12(%ebx)
movl 16(%ecx), %eax
movl %eax, 16(%ebx)
movl 20(%ecx), %eax
movl %eax, 20(%ebx)
movl 24(%ecx), %eax
movl %eax, 24(%ebx)
movl 28(%ecx), %eax
movl %eax, 28(%ebx)
movl 16(%ebp), %ecx
movl %edx, 32(%ebx)
movl %edx, 36(%ebx)
movl 0(%ecx), %eax
movl %eax, 40(%ebx)
movl 4(%ecx), %eax
movl %eax, 44(%ebx)
movl 32(%ebp), %eax
movl %eax, 48(%ebx)
pushl 28(%ebp)
pushl 24(%ebp)
pushl 20(%ebp)
pushl %ebx
call chacha_blocks_x86_local
xorl %eax, %eax
movl %eax, 0(%ebx)
movl %eax, 4(%ebx)
movl %eax, 8(%ebx)
movl %eax, 12(%ebx)
movl %eax, 16(%ebx)
movl %eax, 20(%ebx)
movl %eax, 24(%ebx)
movl %eax, 28(%ebx)
movl %eax, 32(%ebx)
movl %eax, 36(%ebx)
movl %eax, 40(%ebx)
movl %eax, 44(%ebx)
movl %ebp, %esp
popl %ebx
popl %ebp
ret
FN_END chacha_x86

GLOBAL_HIDDEN_FN xchacha_x86
pushl %ebp
pushl %ebx
movl %esp, %ebp
subl $64, %esp
andl $~63, %esp
movl %esp, %ebx
pushl 32(%ebp)
pushl %ebx
pushl 16(%ebp)
pushl 12(%ebp)
call hchacha_x86_local
xorl %edx, %edx
movl 16(%ebp), %ecx
movl 32(%ebx), %edx
movl 36(%ebx), %edx
movl 16(%ecx), %eax
movl %eax, 40(%ebx)
movl 20(%ecx), %eax
movl %eax, 44(%ebx)
movl 32(%ebp), %eax
movl %eax, 48(%ebx)
pushl 28(%ebp)
pushl 24(%ebp)
pushl 20(%ebp)
pushl %ebx
call chacha_blocks_x86_local
xorl %eax, %eax
movl %eax, 0(%ebx)
movl %eax, 4(%ebx)
movl %eax, 8(%ebx)
movl %eax, 12(%ebx)
movl %eax, 16(%ebx)
movl %eax, 20(%ebx)
movl %eax, 24(%ebx)
movl %eax, 28(%ebx)
movl %eax, 32(%ebx)
movl %eax, 36(%ebx)
movl %eax, 40(%ebx)
movl %eax, 44(%ebx)
movl %ebp, %esp
popl %ebx
popl %ebp
ret
FN_END xchacha_x86

