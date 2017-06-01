# Author: Samuel Neves
# ChaCha stream cipher 
# Derived from the 'amd64-xmm6' implementation by Daniel Bernstein
# Requires SSSE3 extensions (i.e. Core 2, Core i7, Atom)

.data

.globl R16
.globl R08

.p2align 6

R16: .byte 2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13
R08: .byte 3, 0 ,1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 15, 12, 13, 14

.text
.p2align 5
.globl _ECRYPT_keystream_bytes
.globl ECRYPT_keystream_bytes
_ECRYPT_keystream_bytes:
ECRYPT_keystream_bytes:
mov %rsp,%r11
and $31,%r11
add $384,%r11
sub %r11,%rsp
mov  %rdi,%r8
mov  %rsi,%rsi
mov  %rsi,%rdi
mov  %rdx,%rdx
cmp  $0,%rdx

jbe ._done

mov  $0,%rax

mov  %rdx,%rcx

rep stosb

sub  %rdx,%rdi

jmp ._start

.text
.p2align 5
.globl _ECRYPT_decrypt_bytes
.globl ECRYPT_decrypt_bytes
_ECRYPT_decrypt_bytes:
ECRYPT_decrypt_bytes:
mov %rsp,%r11
and $31,%r11
add $384,%r11
sub %r11,%rsp

mov  %rdi,%r8

mov  %rsi,%rsi

mov  %rdx,%rdi

mov  %rcx,%rdx

cmp  $0,%rdx

jbe ._done

jmp ._start

.text
.p2align 5
.globl _ECRYPT_encrypt_bytes
.globl ECRYPT_encrypt_bytes
_ECRYPT_encrypt_bytes:
ECRYPT_encrypt_bytes:
mov %rsp,%r11
and $31,%r11
add $384,%r11
sub %r11,%rsp

mov  %rdi,%r8

mov  %rsi,%rsi

mov  %rdx,%rdi

mov  %rcx,%rdx

cmp  $0,%rdx

jbe ._done

._start:

cmp  $256,%rdx

jb ._bytesbetween1and255

movdqa 0(%r8),%xmm0

pshufd $0x55,%xmm0,%xmm1

pshufd $0xaa,%xmm0,%xmm2

pshufd $0xff,%xmm0,%xmm3

pshufd $0x00,%xmm0,%xmm0

movdqa %xmm0,0(%rsp)

movdqa %xmm1,16(%rsp)

movdqa %xmm2,32(%rsp)

movdqa %xmm3,48(%rsp)

movdqa 16(%r8),%xmm0

pshufd $0x55,%xmm0,%xmm1

pshufd $0xaa,%xmm0,%xmm2

pshufd $0xff,%xmm0,%xmm3

pshufd $0x00,%xmm0,%xmm0

movdqa %xmm0,64(%rsp)

movdqa %xmm1,80(%rsp)

movdqa %xmm2,96(%rsp)

movdqa %xmm3,112(%rsp)

movdqa 32(%r8),%xmm0

pshufd $0x55,%xmm0,%xmm1

pshufd $0xaa,%xmm0,%xmm2

pshufd $0xff,%xmm0,%xmm3

pshufd $0x00,%xmm0,%xmm0

movdqa %xmm0,128(%rsp)

movdqa %xmm1,144(%rsp)

movdqa %xmm2,160(%rsp)

movdqa %xmm3,176(%rsp)

movdqa 48(%r8),%xmm0

pshufd $0xaa,%xmm0,%xmm1

pshufd $0xff,%xmm0,%xmm0

movdqa %xmm1,192(%rsp)

movdqa %xmm0,208(%rsp)

._bytesatleast256:

movq %rdx,288(%rsp)

movq   48(%r8),%rdx

lea  1(%rdx),%rcx

lea  2(%rdx),%r9

lea  3(%rdx),%rax

lea  4(%rdx),%r10

movl %edx,224(%rsp)

movl %ecx,4+224(%rsp)

movl %r9d,8+224(%rsp)

movl %eax,12+224(%rsp)

shr  $32,%rdx

shr  $32,%rcx

shr  $32,%r9

shr  $32,%rax

movl %edx,240(%rsp)

movl %ecx,4+240(%rsp)

movl %r9d,8+240(%rsp)

movl %eax,12+240(%rsp)

movq   %r10,48(%r8)

mov  $20,%rdx

movdqa 32(%rsp),%xmm0

movdqa 96(%rsp),%xmm1

movdqa 160(%rsp),%xmm2

movdqa 192(%rsp),%xmm3

movdqa 48(%rsp),%xmm4

movdqa 112(%rsp),%xmm5

movdqa 176(%rsp),%xmm6

movdqa 208(%rsp),%xmm7

movdqa 0(%rsp),%xmm8

movdqa 64(%rsp),%xmm9

movdqa 128(%rsp),%xmm10

movdqa 224(%rsp),%xmm11

movdqa 16(%rsp),%xmm12

movdqa 80(%rsp),%xmm13

movdqa 144(%rsp),%xmm14

movdqa 240(%rsp),%xmm15

movdqa %xmm6,256(%rsp)

._mainloop1:

movdqa R16, %xmm6 # load

paddd %xmm9,%xmm8

pxor  %xmm8,%xmm11

paddd %xmm13,%xmm12

pxor  %xmm12,%xmm15

#movdqa %xmm11,%xmm6
#psrld $16,%xmm11
#pslld $16,%xmm6
#pxor  %xmm6,%xmm11
pshufb %xmm6, %xmm11

#movdqa %xmm15,%xmm6
#psrld $16,%xmm15
#pslld $16,%xmm6
#pxor  %xmm6,%xmm15
pshufb %xmm6, %xmm15

paddd %xmm11,%xmm10

pxor  %xmm10,%xmm9

paddd %xmm15,%xmm14

pxor  %xmm14,%xmm13

movdqa %xmm9,%xmm6

psrld $20,%xmm9

pslld $12,%xmm6

pxor  %xmm6,%xmm9

movdqa %xmm13,%xmm6

psrld $20,%xmm13

pslld $12,%xmm6

pxor  %xmm6,%xmm13

movdqa R08, %xmm6 # load

paddd %xmm9,%xmm8

pxor  %xmm8,%xmm11

#movdqa %xmm11,%xmm6
#psrld $24,%xmm11
#pslld $8,%xmm6
#pxor  %xmm6,%xmm11
pshufb %xmm6, %xmm11

paddd %xmm13,%xmm12

pxor  %xmm12,%xmm15

#movdqa %xmm15,%xmm6
#psrld $24,%xmm15
#pslld $8,%xmm6
#pxor  %xmm6,%xmm15
pshufb %xmm6, %xmm15

paddd %xmm11,%xmm10

pxor  %xmm10,%xmm9

movdqa %xmm9,%xmm6

psrld $25,%xmm9

pslld $7,%xmm6

pxor  %xmm6,%xmm9

paddd %xmm15,%xmm14

pxor  %xmm14,%xmm13

movdqa %xmm13,%xmm6

psrld $25,%xmm13

pslld $7,%xmm6

pxor  %xmm6,%xmm13

movdqa %xmm14,272(%rsp)

movdqa 256(%rsp),%xmm6

movdqa R16, %xmm14  # load

paddd %xmm1,%xmm0

pxor  %xmm0,%xmm3

#movdqa %xmm3,%xmm14
#psrld $16,%xmm3
#pslld $16,%xmm14
#pxor  %xmm14,%xmm3
pshufb %xmm14, %xmm3

paddd %xmm5,%xmm4

pxor  %xmm4,%xmm7

#movdqa %xmm7,%xmm14
#psrld $16,%xmm7
#pslld $16,%xmm14
#pxor  %xmm14,%xmm7
pshufb %xmm14, %xmm7

paddd %xmm3,%xmm2

pxor  %xmm2,%xmm1

movdqa %xmm1,%xmm14

psrld $20,%xmm1

pslld $12,%xmm14

pxor  %xmm14,%xmm1

paddd %xmm7,%xmm6

pxor  %xmm6,%xmm5

movdqa %xmm5,%xmm14

psrld $20,%xmm5

pslld $12,%xmm14

pxor  %xmm14,%xmm5

movdqa R08, %xmm14 # load 

paddd %xmm1,%xmm0

pxor  %xmm0,%xmm3

#movdqa %xmm3,%xmm14
#psrld $24,%xmm3
#pslld $8,%xmm14
#pxor  %xmm14,%xmm3
pshufb %xmm14, %xmm3

paddd %xmm5,%xmm4

pxor  %xmm4,%xmm7

#movdqa %xmm7,%xmm14
#psrld $24,%xmm7
#pslld $8,%xmm14
#pxor  %xmm14,%xmm7
pshufb %xmm14, %xmm7

paddd %xmm3,%xmm2

pxor  %xmm2,%xmm1

movdqa %xmm1,%xmm14

psrld $25,%xmm1

pslld $7,%xmm14

pxor  %xmm14,%xmm1

paddd %xmm7,%xmm6

pxor  %xmm6,%xmm5

movdqa %xmm5,%xmm14

psrld $25,%xmm5

pslld $7,%xmm14

pxor  %xmm14,%xmm5

movdqa R16, %xmm14 # load

paddd %xmm13,%xmm8

pxor  %xmm8,%xmm7

#movdqa %xmm7,%xmm14
#psrld $16,%xmm7
#pslld $16,%xmm14
#pxor  %xmm14,%xmm7
pshufb %xmm14, %xmm7

paddd %xmm1,%xmm12

pxor  %xmm12,%xmm11

#movdqa %xmm11,%xmm14
#psrld $16,%xmm11
#pslld $16,%xmm14
#pxor  %xmm14,%xmm11
pshufb %xmm14, %xmm11

paddd %xmm7,%xmm2

pxor  %xmm2,%xmm13

movdqa %xmm13,%xmm14

psrld $20,%xmm13

pslld $12,%xmm14

pxor  %xmm14,%xmm13

paddd %xmm11,%xmm6

pxor  %xmm6,%xmm1

movdqa %xmm1,%xmm14

psrld $20,%xmm1

pslld $12,%xmm14

pxor  %xmm14,%xmm1

movdqa R08, %xmm14 # load

paddd %xmm13,%xmm8

pxor  %xmm8,%xmm7

#movdqa %xmm7,%xmm14
#psrld $24,%xmm7
#pslld $8,%xmm14
#pxor  %xmm14,%xmm7
pshufb %xmm14, %xmm7

paddd %xmm1,%xmm12

pxor  %xmm12,%xmm11

#movdqa %xmm11,%xmm14
#psrld $24,%xmm11
#pslld $8,%xmm14
#pxor  %xmm14,%xmm11
pshufb %xmm14, %xmm11

paddd %xmm7,%xmm2

pxor  %xmm2,%xmm13

movdqa %xmm13,%xmm14

psrld $25,%xmm13

pslld $7,%xmm14

pxor  %xmm14,%xmm13

paddd %xmm11,%xmm6

pxor  %xmm6,%xmm1

movdqa %xmm1,%xmm14

psrld $25,%xmm1

pslld $7,%xmm14

pxor  %xmm14,%xmm1

movdqa %xmm6,256(%rsp)

movdqa 272(%rsp),%xmm14

movdqa R16, %xmm6 # load

paddd %xmm5,%xmm0

pxor  %xmm0,%xmm15

#movdqa %xmm15,%xmm6
#psrld $16,%xmm15
#pslld $16,%xmm6
#pxor  %xmm6,%xmm15
pshufb %xmm6, %xmm15

paddd %xmm9,%xmm4

pxor  %xmm4,%xmm3

#movdqa %xmm3,%xmm6
#psrld $16,%xmm3
#pslld $16,%xmm6
#pxor  %xmm6,%xmm3
pshufb %xmm6, %xmm3

paddd %xmm15,%xmm10

pxor  %xmm10,%xmm5

movdqa %xmm5,%xmm6

psrld $20,%xmm5

pslld $12,%xmm6

pxor  %xmm6,%xmm5

sub  $2,%rdx

paddd %xmm3,%xmm14

pxor  %xmm14,%xmm9

movdqa %xmm9,%xmm6

psrld $20,%xmm9

pslld $12,%xmm6

pxor  %xmm6,%xmm9

movdqa R08, %xmm6 # load

paddd %xmm5,%xmm0

pxor  %xmm0,%xmm15

#movdqa %xmm15,%xmm6
#psrld $24,%xmm15
#pslld $8,%xmm6
#pxor  %xmm6,%xmm15
pshufb %xmm6, %xmm15

paddd %xmm9,%xmm4

pxor  %xmm4,%xmm3

#movdqa %xmm3,%xmm6
#psrld $24,%xmm3
#pslld $8,%xmm6
#pxor  %xmm6,%xmm3
pshufb %xmm6, %xmm3

paddd %xmm15,%xmm10

pxor  %xmm10,%xmm5

movdqa %xmm5,%xmm6

psrld $25,%xmm5

pslld $7,%xmm6

pxor  %xmm6,%xmm5

paddd %xmm3,%xmm14

pxor  %xmm14,%xmm9

movdqa %xmm9,%xmm6

psrld $25,%xmm9

pslld $7,%xmm6

pxor  %xmm6,%xmm9

ja ._mainloop1

movdqa 256(%rsp),%xmm6

paddd 0(%rsp),%xmm8

paddd 16(%rsp),%xmm12

paddd 32(%rsp),%xmm0

paddd 48(%rsp),%xmm4

movd   %xmm8,%rdx

movd   %xmm12,%rcx

movd   %xmm0,%r9

movd   %xmm4,%rax

pshufd $0x39,%xmm8,%xmm8

pshufd $0x39,%xmm12,%xmm12

pshufd $0x39,%xmm0,%xmm0

pshufd $0x39,%xmm4,%xmm4

xorl 0(%rsi),%edx

xorl 4(%rsi),%ecx

xorl 8(%rsi),%r9d

xorl 12(%rsi),%eax

movl   %edx,0(%rdi)

movl   %ecx,4(%rdi)

movl   %r9d,8(%rdi)

movl   %eax,12(%rdi)

movd   %xmm8,%rdx

movd   %xmm12,%rcx

movd   %xmm0,%r9

movd   %xmm4,%rax

pshufd $0x39,%xmm8,%xmm8

pshufd $0x39,%xmm12,%xmm12

pshufd $0x39,%xmm0,%xmm0

pshufd $0x39,%xmm4,%xmm4

xorl 64(%rsi),%edx

xorl 68(%rsi),%ecx

xorl 72(%rsi),%r9d

xorl 76(%rsi),%eax

movl   %edx,64(%rdi)

movl   %ecx,68(%rdi)

movl   %r9d,72(%rdi)

movl   %eax,76(%rdi)

movd   %xmm8,%rdx

movd   %xmm12,%rcx

movd   %xmm0,%r9

movd   %xmm4,%rax

pshufd $0x39,%xmm8,%xmm8

pshufd $0x39,%xmm12,%xmm12

pshufd $0x39,%xmm0,%xmm0

pshufd $0x39,%xmm4,%xmm4

xorl 128(%rsi),%edx

xorl 132(%rsi),%ecx

xorl 136(%rsi),%r9d

xorl 140(%rsi),%eax

movl   %edx,128(%rdi)

movl   %ecx,132(%rdi)

movl   %r9d,136(%rdi)

movl   %eax,140(%rdi)

movd   %xmm8,%rdx

movd   %xmm12,%rcx

movd   %xmm0,%r9

movd   %xmm4,%rax

xorl 192(%rsi),%edx

xorl 196(%rsi),%ecx

xorl 200(%rsi),%r9d

xorl 204(%rsi),%eax

movl   %edx,192(%rdi)

movl   %ecx,196(%rdi)

movl   %r9d,200(%rdi)

movl   %eax,204(%rdi)

paddd 64(%rsp),%xmm9

paddd 80(%rsp),%xmm13

paddd 96(%rsp),%xmm1

paddd 112(%rsp),%xmm5

movd   %xmm9,%rdx

movd   %xmm13,%rcx

movd   %xmm1,%r9

movd   %xmm5,%rax

pshufd $0x39,%xmm9,%xmm9

pshufd $0x39,%xmm13,%xmm13

pshufd $0x39,%xmm1,%xmm1

pshufd $0x39,%xmm5,%xmm5

xorl 16(%rsi),%edx

xorl 20(%rsi),%ecx

xorl 24(%rsi),%r9d

xorl 28(%rsi),%eax

movl   %edx,16(%rdi)

movl   %ecx,20(%rdi)

movl   %r9d,24(%rdi)

movl   %eax,28(%rdi)

movd   %xmm9,%rdx

movd   %xmm13,%rcx

movd   %xmm1,%r9

movd   %xmm5,%rax

pshufd $0x39,%xmm9,%xmm9

pshufd $0x39,%xmm13,%xmm13

pshufd $0x39,%xmm1,%xmm1

pshufd $0x39,%xmm5,%xmm5

xorl 80(%rsi),%edx

xorl 84(%rsi),%ecx

xorl 88(%rsi),%r9d

xorl 92(%rsi),%eax

movl   %edx,80(%rdi)

movl   %ecx,84(%rdi)

movl   %r9d,88(%rdi)

movl   %eax,92(%rdi)

movd   %xmm9,%rdx

movd   %xmm13,%rcx

movd   %xmm1,%r9

movd   %xmm5,%rax

pshufd $0x39,%xmm9,%xmm9

pshufd $0x39,%xmm13,%xmm13

pshufd $0x39,%xmm1,%xmm1

pshufd $0x39,%xmm5,%xmm5

xorl 144(%rsi),%edx

xorl 148(%rsi),%ecx

xorl 152(%rsi),%r9d

xorl 156(%rsi),%eax

movl   %edx,144(%rdi)

movl   %ecx,148(%rdi)

movl   %r9d,152(%rdi)

movl   %eax,156(%rdi)

movd   %xmm9,%rdx

movd   %xmm13,%rcx

movd   %xmm1,%r9

movd   %xmm5,%rax

xorl 208(%rsi),%edx

xorl 212(%rsi),%ecx

xorl 216(%rsi),%r9d

xorl 220(%rsi),%eax

movl   %edx,208(%rdi)

movl   %ecx,212(%rdi)

movl   %r9d,216(%rdi)

movl   %eax,220(%rdi)

paddd 128(%rsp),%xmm10

paddd 144(%rsp),%xmm14

paddd 160(%rsp),%xmm2

paddd 176(%rsp),%xmm6

movd   %xmm10,%rdx

movd   %xmm14,%rcx

movd   %xmm2,%r9

movd   %xmm6,%rax

pshufd $0x39,%xmm10,%xmm10

pshufd $0x39,%xmm14,%xmm14

pshufd $0x39,%xmm2,%xmm2

pshufd $0x39,%xmm6,%xmm6

xorl 32(%rsi),%edx

xorl 36(%rsi),%ecx

xorl 40(%rsi),%r9d

xorl 44(%rsi),%eax

movl   %edx,32(%rdi)

movl   %ecx,36(%rdi)

movl   %r9d,40(%rdi)

movl   %eax,44(%rdi)

movd   %xmm10,%rdx

movd   %xmm14,%rcx

movd   %xmm2,%r9

movd   %xmm6,%rax

pshufd $0x39,%xmm10,%xmm10

pshufd $0x39,%xmm14,%xmm14

pshufd $0x39,%xmm2,%xmm2

pshufd $0x39,%xmm6,%xmm6

xorl 96(%rsi),%edx

xorl 100(%rsi),%ecx

xorl 104(%rsi),%r9d

xorl 108(%rsi),%eax

movl   %edx,96(%rdi)

movl   %ecx,100(%rdi)

movl   %r9d,104(%rdi)

movl   %eax,108(%rdi)

movd   %xmm10,%rdx

movd   %xmm14,%rcx

movd   %xmm2,%r9

movd   %xmm6,%rax

pshufd $0x39,%xmm10,%xmm10

pshufd $0x39,%xmm14,%xmm14

pshufd $0x39,%xmm2,%xmm2

pshufd $0x39,%xmm6,%xmm6

xorl 160(%rsi),%edx

xorl 164(%rsi),%ecx

xorl 168(%rsi),%r9d

xorl 172(%rsi),%eax

movl   %edx,160(%rdi)

movl   %ecx,164(%rdi)

movl   %r9d,168(%rdi)

movl   %eax,172(%rdi)

movd   %xmm10,%rdx

movd   %xmm14,%rcx

movd   %xmm2,%r9

movd   %xmm6,%rax

xorl 224(%rsi),%edx

xorl 228(%rsi),%ecx

xorl 232(%rsi),%r9d

xorl 236(%rsi),%eax

movl   %edx,224(%rdi)

movl   %ecx,228(%rdi)

movl   %r9d,232(%rdi)

movl   %eax,236(%rdi)

paddd 224(%rsp),%xmm11

paddd 240(%rsp),%xmm15

paddd 192(%rsp),%xmm3

paddd 208(%rsp),%xmm7

movd   %xmm11,%rdx

movd   %xmm15,%rcx

movd   %xmm3,%r9

movd   %xmm7,%rax

pshufd $0x39,%xmm11,%xmm11

pshufd $0x39,%xmm15,%xmm15

pshufd $0x39,%xmm3,%xmm3

pshufd $0x39,%xmm7,%xmm7

xorl 48(%rsi),%edx

xorl 52(%rsi),%ecx

xorl 56(%rsi),%r9d

xorl 60(%rsi),%eax

movl   %edx,48(%rdi)

movl   %ecx,52(%rdi)

movl   %r9d,56(%rdi)

movl   %eax,60(%rdi)

movd   %xmm11,%rdx

movd   %xmm15,%rcx

movd   %xmm3,%r9

movd   %xmm7,%rax

pshufd $0x39,%xmm11,%xmm11

pshufd $0x39,%xmm15,%xmm15

pshufd $0x39,%xmm3,%xmm3

pshufd $0x39,%xmm7,%xmm7

xorl 112(%rsi),%edx

xorl 116(%rsi),%ecx

xorl 120(%rsi),%r9d

xorl 124(%rsi),%eax

movl   %edx,112(%rdi)

movl   %ecx,116(%rdi)

movl   %r9d,120(%rdi)

movl   %eax,124(%rdi)

movd   %xmm11,%rdx

movd   %xmm15,%rcx

movd   %xmm3,%r9

movd   %xmm7,%rax

pshufd $0x39,%xmm11,%xmm11

pshufd $0x39,%xmm15,%xmm15

pshufd $0x39,%xmm3,%xmm3

pshufd $0x39,%xmm7,%xmm7

xorl 176(%rsi),%edx

xorl 180(%rsi),%ecx

xorl 184(%rsi),%r9d

xorl 188(%rsi),%eax

movl   %edx,176(%rdi)

movl   %ecx,180(%rdi)

movl   %r9d,184(%rdi)

movl   %eax,188(%rdi)

movd   %xmm11,%rdx

movd   %xmm15,%rcx

movd   %xmm3,%r9

movd   %xmm7,%rax

xorl 240(%rsi),%edx

xorl 244(%rsi),%ecx

xorl 248(%rsi),%r9d

xorl 252(%rsi),%eax

movl   %edx,240(%rdi)

movl   %ecx,244(%rdi)

movl   %r9d,248(%rdi)

movl   %eax,252(%rdi)

movq 288(%rsp),%rdx

sub  $256,%rdx

add  $256,%rsi

add  $256,%rdi

cmp  $256,%rdx

jae ._bytesatleast256

cmp  $0,%rdx

jbe ._done

._bytesbetween1and255:

cmp  $64,%rdx

jae ._nocopy

mov  %rdi,%r9

leaq 320(%rsp),%rdi

mov  %rdx,%rcx

rep movsb

leaq 320(%rsp),%rdi

leaq 320(%rsp),%rsi

._nocopy:

movq %rdx,288(%rsp)

movdqa 0(%r8),%xmm0

movdqa 16(%r8),%xmm1

movdqa 32(%r8),%xmm2

movdqa 48(%r8),%xmm3

mov  $20,%rdx

._mainloop2:

paddd %xmm1,%xmm0

pxor  %xmm0,%xmm3

#movdqa %xmm3,%xmm4
#pslld $16,%xmm3
#psrld $16,%xmm4
#pxor  %xmm4,%xmm3
pshufb (R16), %xmm3

paddd %xmm3,%xmm2

pxor  %xmm2,%xmm1

movdqa %xmm1,%xmm4

pslld $12,%xmm1

psrld $20,%xmm4

pxor  %xmm4,%xmm1

paddd %xmm1,%xmm0

pxor  %xmm0,%xmm3

#movdqa %xmm3,%xmm4
#pslld $8,%xmm3
#psrld $24,%xmm4

pshufd $0x93,%xmm0,%xmm0

#pxor  %xmm4,%xmm3
pshufb (R08), %xmm3

paddd %xmm3,%xmm2

pshufd $0x4e,%xmm3,%xmm3

pxor  %xmm2,%xmm1

pshufd $0x39,%xmm2,%xmm2

movdqa %xmm1,%xmm4

pslld $7,%xmm1

psrld $25,%xmm4

pxor  %xmm4,%xmm1

sub  $2,%rdx

paddd %xmm1,%xmm0

pxor  %xmm0,%xmm3

#movdqa %xmm3,%xmm4
#pslld $16,%xmm3
#psrld $16,%xmm4
#pxor  %xmm4,%xmm3
pshufb (R16), %xmm3

paddd %xmm3,%xmm2

pxor  %xmm2,%xmm1

movdqa %xmm1,%xmm4

pslld $12,%xmm1

psrld $20,%xmm4

pxor  %xmm4,%xmm1

paddd %xmm1,%xmm0

pxor  %xmm0,%xmm3

#movdqa %xmm3,%xmm4
#pslld $8,%xmm3
#psrld $24,%xmm4

pshufd $0x39,%xmm0,%xmm0

#pxor  %xmm4,%xmm3
pshufb (R08), %xmm3

paddd %xmm3,%xmm2

pshufd $0x4e,%xmm3,%xmm3

pxor  %xmm2,%xmm1

pshufd $0x93,%xmm2,%xmm2

movdqa %xmm1,%xmm4

pslld $7,%xmm1

psrld $25,%xmm4

pxor  %xmm4,%xmm1

ja ._mainloop2

paddd 0(%r8),%xmm0

paddd 16(%r8),%xmm1

paddd 32(%r8),%xmm2

paddd 48(%r8),%xmm3

pxor 0(%rsi),%xmm0

pxor 16(%rsi),%xmm1

pxor 32(%rsi),%xmm2

pxor 48(%rsi),%xmm3

movdqa %xmm0,0(%rdi)

movdqa %xmm1,16(%rdi)

movdqa %xmm2,32(%rdi)

movdqa %xmm3,48(%rdi)

movq 288(%rsp),%rdx

movl   48(%r8),%ecx

movl   52(%r8),%eax

add  $1,%rcx

shl  $32,%rax

add  %rax,%rcx

mov  %rcx,%rax

shr  $32,%rax

movl   %ecx,48(%r8)

movl   %eax,52(%r8)

cmp  $64,%rdx

ja ._bytesatleast65

jae ._bytesatleast64

mov  %rdi,%rsi

mov  %r9,%rdi

mov  %rdx,%rcx

rep movsb

._bytesatleast64:

._done:

add %r11,%rsp
mov %rdi,%rax
mov %rsi,%rdx
ret

._bytesatleast65:

sub  $64,%rdx

add  $64,%rdi

add  $64,%rsi

jmp ._bytesbetween1and255

.text
.p2align 5
.globl _ECRYPT_init
.globl ECRYPT_init
_ECRYPT_init:
ECRYPT_init:
mov %rsp,%r11
and $31,%r11
add $384,%r11
sub %r11,%rsp

add %r11,%rsp
mov %rdi,%rax
mov %rsi,%rdx
ret

.text
.p2align 5
.globl _ECRYPT_keysetup
.globl ECRYPT_keysetup
_ECRYPT_keysetup:
ECRYPT_keysetup:
mov %rsp,%r11
and $31,%r11
add $384,%r11
sub %r11,%rsp

mov  %rsi,%rsi

mov  %rdx,%rdx

mov  %rdi,%rdi

movl   0(%rsi),%r8d

movl   4(%rsi),%r9d

movl   8(%rsi),%eax

movl   12(%rsi),%r10d

movl   %r8d,16(%rdi)

movl   %r9d,20(%rdi)

movl   %eax,24(%rdi)

movl   %r10d,28(%rdi)

cmp  $256,%rdx

jb ._kbits128

._kbits256:

movl   16(%rsi),%edx

movl   20(%rsi),%ecx

movl   24(%rsi),%r8d

movl   28(%rsi),%esi

movl   %edx,32(%rdi)

movl   %ecx,36(%rdi)

movl   %r8d,40(%rdi)

movl   %esi,44(%rdi)

mov  $1634760805,%rsi

mov  $857760878,%rdx

mov  $2036477234,%rcx

mov  $1797285236,%r8

movl   %esi,0(%rdi)

movl   %edx,4(%rdi)

movl   %ecx,8(%rdi)

movl   %r8d,12(%rdi)

jmp ._keysetupdone

._kbits128:

movl   0(%rsi),%edx

movl   4(%rsi),%ecx

movl   8(%rsi),%r8d

movl   12(%rsi),%esi

movl   %edx,32(%rdi)

movl   %ecx,36(%rdi)

movl   %r8d,40(%rdi)

movl   %esi,44(%rdi)

mov  $1634760805,%rsi

mov  $824206446,%rdx

mov  $2036477238,%rcx

mov  $1797285236,%r8

movl   %esi,0(%rdi)

movl   %edx,4(%rdi)

movl   %ecx,8(%rdi)

movl   %r8d,12(%rdi)

._keysetupdone:

add %r11,%rsp
mov %rdi,%rax
mov %rsi,%rdx
ret

.text
.p2align 5
.globl _ECRYPT_ivsetup
.globl ECRYPT_ivsetup
_ECRYPT_ivsetup:
ECRYPT_ivsetup:
mov %rsp,%r11
and $31,%r11
add $384,%r11
sub %r11,%rsp

mov  %rsi,%rsi

mov  %rdi,%rdi

mov  $0,%r8

mov  $0,%r9

movl   0(%rsi),%eax

movl   4(%rsi),%esi

movl   %r8d,48(%rdi)

movl   %r9d,52(%rdi)

movl   %eax,56(%rdi)

movl   %esi,60(%rdi)

add %r11,%rsp
mov %rdi,%rax
mov %rsi,%rdx
ret


