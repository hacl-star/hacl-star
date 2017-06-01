
# qhasm: int32 a

# qhasm: stack32 arg1

# qhasm: stack32 arg2

# qhasm: stack32 arg3

# qhasm: stack32 arg4

# qhasm: input arg1

# qhasm: input arg2

# qhasm: input arg3

# qhasm: input arg4

# qhasm: int32 eax

# qhasm: int32 ebx

# qhasm: int32 esi

# qhasm: int32 edi

# qhasm: int32 ebp

# qhasm: caller eax

# qhasm: caller ebx

# qhasm: caller esi

# qhasm: caller edi

# qhasm: caller ebp

# qhasm: int32 k

# qhasm: int32 kbits

# qhasm: int32 iv

# qhasm: int32 i

# qhasm: int32 x

# qhasm: int32 m

# qhasm: int32 out

# qhasm: stack32 bytes_backup

# qhasm: int32 bytes

# qhasm: stack32 eax_stack

# qhasm: stack32 ebx_stack

# qhasm: stack32 esi_stack

# qhasm: stack32 edi_stack

# qhasm: stack32 ebp_stack

# qhasm: int6464 diag0

# qhasm: int6464 diag1

# qhasm: int6464 diag2

# qhasm: int6464 diag3

# qhasm: int6464 a0

# qhasm: int6464 a1

# qhasm: int6464 a2

# qhasm: int6464 a3

# qhasm: int6464 a4

# qhasm: int6464 a5

# qhasm: int6464 a6

# qhasm: int6464 a7

# qhasm: int6464 b0

# qhasm: int6464 b1

# qhasm: int6464 b2

# qhasm: int6464 b3

# qhasm: int6464 b4

# qhasm: int6464 b5

# qhasm: int6464 b6

# qhasm: int6464 b7

# qhasm: int32 in0

# qhasm: int32 in1

# qhasm: int32 in2

# qhasm: int32 in3

# qhasm: int32 in4

# qhasm: int32 in5

# qhasm: int32 in6

# qhasm: int32 in7

# qhasm: int32 in8

# qhasm: int32 in9

# qhasm: int32 in10

# qhasm: int32 in11

# qhasm: int32 in12

# qhasm: int32 in13

# qhasm: int32 in14

# qhasm: int32 in15

# qhasm: stack512 tmp

# qhasm: stack32 ctarget

# qhasm: enter ECRYPT_keystream_bytes
.text
.p2align 5
.globl _ECRYPT_keystream_bytes
.globl ECRYPT_keystream_bytes
_ECRYPT_keystream_bytes:
ECRYPT_keystream_bytes:
mov %esp,%eax
and $31,%eax
add $96,%eax
sub %eax,%esp

# qhasm: eax_stack = eax
# asm 1: movl <eax=int32#1,>eax_stack=stack32#1
# asm 2: movl <eax=%eax,>eax_stack=0(%esp)
movl %eax,0(%esp)

# qhasm: ebx_stack = ebx
# asm 1: movl <ebx=int32#4,>ebx_stack=stack32#2
# asm 2: movl <ebx=%ebx,>ebx_stack=4(%esp)
movl %ebx,4(%esp)

# qhasm: esi_stack = esi
# asm 1: movl <esi=int32#5,>esi_stack=stack32#3
# asm 2: movl <esi=%esi,>esi_stack=8(%esp)
movl %esi,8(%esp)

# qhasm: edi_stack = edi
# asm 1: movl <edi=int32#6,>edi_stack=stack32#4
# asm 2: movl <edi=%edi,>edi_stack=12(%esp)
movl %edi,12(%esp)

# qhasm: ebp_stack = ebp
# asm 1: movl <ebp=int32#7,>ebp_stack=stack32#5
# asm 2: movl <ebp=%ebp,>ebp_stack=16(%esp)
movl %ebp,16(%esp)

# qhasm: x = arg1
# asm 1: movl <arg1=stack32#-1,>x=int32#3
# asm 2: movl <arg1=4(%esp,%eax),>x=%edx
movl 4(%esp,%eax),%edx

# qhasm: m = arg2
# asm 1: movl <arg2=stack32#-2,>m=int32#5
# asm 2: movl <arg2=8(%esp,%eax),>m=%esi
movl 8(%esp,%eax),%esi

# qhasm: out = m
# asm 1: mov  <m=int32#5,>out=int32#6
# asm 2: mov  <m=%esi,>out=%edi
mov  %esi,%edi

# qhasm: bytes = arg3
# asm 1: movl <arg3=stack32#-3,>bytes=int32#4
# asm 2: movl <arg3=12(%esp,%eax),>bytes=%ebx
movl 12(%esp,%eax),%ebx

# qhasm:               unsigned>? bytes - 0
# asm 1: cmp  $0,<bytes=int32#4
# asm 2: cmp  $0,<bytes=%ebx
cmp  $0,%ebx
# comment:fp stack unchanged by jump

# qhasm: goto done if !unsigned>
jbe ._done

# qhasm: a = 0
# asm 1: mov  $0,>a=int32#1
# asm 2: mov  $0,>a=%eax
mov  $0,%eax

# qhasm: i = bytes
# asm 1: mov  <bytes=int32#4,>i=int32#2
# asm 2: mov  <bytes=%ebx,>i=%ecx
mov  %ebx,%ecx

# qhasm: while (i) { *out++ = a; --i }
rep stosb

# qhasm: out -= bytes
# asm 1: subl <bytes=int32#4,<out=int32#6
# asm 2: subl <bytes=%ebx,<out=%edi
subl %ebx,%edi
# comment:fp stack unchanged by jump

# qhasm: goto start
jmp ._start

# qhasm: enter ECRYPT_decrypt_bytes
.text
.p2align 5
.globl _ECRYPT_decrypt_bytes
.globl ECRYPT_decrypt_bytes
_ECRYPT_decrypt_bytes:
ECRYPT_decrypt_bytes:
mov %esp,%eax
and $31,%eax
add $96,%eax
sub %eax,%esp

# qhasm: eax_stack = eax
# asm 1: movl <eax=int32#1,>eax_stack=stack32#1
# asm 2: movl <eax=%eax,>eax_stack=0(%esp)
movl %eax,0(%esp)

# qhasm: ebx_stack = ebx
# asm 1: movl <ebx=int32#4,>ebx_stack=stack32#2
# asm 2: movl <ebx=%ebx,>ebx_stack=4(%esp)
movl %ebx,4(%esp)

# qhasm: esi_stack = esi
# asm 1: movl <esi=int32#5,>esi_stack=stack32#3
# asm 2: movl <esi=%esi,>esi_stack=8(%esp)
movl %esi,8(%esp)

# qhasm: edi_stack = edi
# asm 1: movl <edi=int32#6,>edi_stack=stack32#4
# asm 2: movl <edi=%edi,>edi_stack=12(%esp)
movl %edi,12(%esp)

# qhasm: ebp_stack = ebp
# asm 1: movl <ebp=int32#7,>ebp_stack=stack32#5
# asm 2: movl <ebp=%ebp,>ebp_stack=16(%esp)
movl %ebp,16(%esp)

# qhasm: x = arg1
# asm 1: movl <arg1=stack32#-1,>x=int32#3
# asm 2: movl <arg1=4(%esp,%eax),>x=%edx
movl 4(%esp,%eax),%edx

# qhasm: m = arg2
# asm 1: movl <arg2=stack32#-2,>m=int32#5
# asm 2: movl <arg2=8(%esp,%eax),>m=%esi
movl 8(%esp,%eax),%esi

# qhasm: out = arg3
# asm 1: movl <arg3=stack32#-3,>out=int32#6
# asm 2: movl <arg3=12(%esp,%eax),>out=%edi
movl 12(%esp,%eax),%edi

# qhasm: bytes = arg4
# asm 1: movl <arg4=stack32#-4,>bytes=int32#4
# asm 2: movl <arg4=16(%esp,%eax),>bytes=%ebx
movl 16(%esp,%eax),%ebx

# qhasm:               unsigned>? bytes - 0
# asm 1: cmp  $0,<bytes=int32#4
# asm 2: cmp  $0,<bytes=%ebx
cmp  $0,%ebx
# comment:fp stack unchanged by jump

# qhasm: goto done if !unsigned>
jbe ._done
# comment:fp stack unchanged by jump

# qhasm: goto start
jmp ._start

# qhasm: enter ECRYPT_encrypt_bytes
.text
.p2align 5
.globl _ECRYPT_encrypt_bytes
.globl ECRYPT_encrypt_bytes
_ECRYPT_encrypt_bytes:
ECRYPT_encrypt_bytes:
mov %esp,%eax
and $31,%eax
add $96,%eax
sub %eax,%esp

# qhasm: eax_stack = eax
# asm 1: movl <eax=int32#1,>eax_stack=stack32#1
# asm 2: movl <eax=%eax,>eax_stack=0(%esp)
movl %eax,0(%esp)

# qhasm: ebx_stack = ebx
# asm 1: movl <ebx=int32#4,>ebx_stack=stack32#2
# asm 2: movl <ebx=%ebx,>ebx_stack=4(%esp)
movl %ebx,4(%esp)

# qhasm: esi_stack = esi
# asm 1: movl <esi=int32#5,>esi_stack=stack32#3
# asm 2: movl <esi=%esi,>esi_stack=8(%esp)
movl %esi,8(%esp)

# qhasm: edi_stack = edi
# asm 1: movl <edi=int32#6,>edi_stack=stack32#4
# asm 2: movl <edi=%edi,>edi_stack=12(%esp)
movl %edi,12(%esp)

# qhasm: ebp_stack = ebp
# asm 1: movl <ebp=int32#7,>ebp_stack=stack32#5
# asm 2: movl <ebp=%ebp,>ebp_stack=16(%esp)
movl %ebp,16(%esp)

# qhasm: x = arg1
# asm 1: movl <arg1=stack32#-1,>x=int32#3
# asm 2: movl <arg1=4(%esp,%eax),>x=%edx
movl 4(%esp,%eax),%edx

# qhasm: m = arg2
# asm 1: movl <arg2=stack32#-2,>m=int32#5
# asm 2: movl <arg2=8(%esp,%eax),>m=%esi
movl 8(%esp,%eax),%esi

# qhasm: out = arg3
# asm 1: movl <arg3=stack32#-3,>out=int32#6
# asm 2: movl <arg3=12(%esp,%eax),>out=%edi
movl 12(%esp,%eax),%edi

# qhasm: bytes = arg4
# asm 1: movl <arg4=stack32#-4,>bytes=int32#4
# asm 2: movl <arg4=16(%esp,%eax),>bytes=%ebx
movl 16(%esp,%eax),%ebx

# qhasm:               unsigned>? bytes - 0
# asm 1: cmp  $0,<bytes=int32#4
# asm 2: cmp  $0,<bytes=%ebx
cmp  $0,%ebx
# comment:fp stack unchanged by jump

# qhasm: goto done if !unsigned>
jbe ._done
# comment:fp stack unchanged by fallthrough

# qhasm: start:
._start:

# qhasm: bytesatleast1:
._bytesatleast1:

# qhasm:                   unsigned<? bytes - 64
# asm 1: cmp  $64,<bytes=int32#4
# asm 2: cmp  $64,<bytes=%ebx
cmp  $64,%ebx
# comment:fp stack unchanged by jump

# qhasm:   goto nocopy if !unsigned<
jae ._nocopy

# qhasm:     ctarget = out
# asm 1: movl <out=int32#6,>ctarget=stack32#6
# asm 2: movl <out=%edi,>ctarget=20(%esp)
movl %edi,20(%esp)

# qhasm:     out = &tmp
# asm 1: leal <tmp=stack512#1,>out=int32#6
# asm 2: leal <tmp=32(%esp),>out=%edi
leal 32(%esp),%edi

# qhasm:     i = bytes
# asm 1: mov  <bytes=int32#4,>i=int32#2
# asm 2: mov  <bytes=%ebx,>i=%ecx
mov  %ebx,%ecx

# qhasm:     while (i) { *out++ = *m++; --i }
rep movsb

# qhasm:     out = &tmp
# asm 1: leal <tmp=stack512#1,>out=int32#6
# asm 2: leal <tmp=32(%esp),>out=%edi
leal 32(%esp),%edi

# qhasm:     m = &tmp
# asm 1: leal <tmp=stack512#1,>m=int32#5
# asm 2: leal <tmp=32(%esp),>m=%esi
leal 32(%esp),%esi
# comment:fp stack unchanged by fallthrough

# qhasm:   nocopy:
._nocopy:

# qhasm:   bytes_backup = bytes
# asm 1: movl <bytes=int32#4,>bytes_backup=stack32#7
# asm 2: movl <bytes=%ebx,>bytes_backup=24(%esp)
movl %ebx,24(%esp)

# qhasm: diag0 = *(int128 *) (x + 0)
# asm 1: movdqa 0(<x=int32#3),>diag0=int6464#1
# asm 2: movdqa 0(<x=%edx),>diag0=%xmm0
movdqa 0(%edx),%xmm0

# qhasm: diag1 = *(int128 *) (x + 16)
# asm 1: movdqa 16(<x=int32#3),>diag1=int6464#2
# asm 2: movdqa 16(<x=%edx),>diag1=%xmm1
movdqa 16(%edx),%xmm1

# qhasm: diag2 = *(int128 *) (x + 32)
# asm 1: movdqa 32(<x=int32#3),>diag2=int6464#3
# asm 2: movdqa 32(<x=%edx),>diag2=%xmm2
movdqa 32(%edx),%xmm2

# qhasm: diag3 = *(int128 *) (x + 48)
# asm 1: movdqa 48(<x=int32#3),>diag3=int6464#4
# asm 2: movdqa 48(<x=%edx),>diag3=%xmm3
movdqa 48(%edx),%xmm3

# qhasm: i = 20
# asm 1: mov  $20,>i=int32#1
# asm 2: mov  $20,>i=%eax
mov  $20,%eax

# qhasm: mainloop:
._mainloop:

# qhasm: uint32323232	diag0 += diag1
# asm 1: paddd <diag1=int6464#2,<diag0=int6464#1
# asm 2: paddd <diag1=%xmm1,<diag0=%xmm0
paddd %xmm1,%xmm0

# qhasm: 		diag3 ^= diag0
# asm 1: pxor  <diag0=int6464#1,<diag3=int6464#4
# asm 2: pxor  <diag0=%xmm0,<diag3=%xmm3
pxor  %xmm0,%xmm3

# qhasm: 		b3 = diag3
# asm 1: movdqa <diag3=int6464#4,>b3=int6464#5
# asm 2: movdqa <diag3=%xmm3,>b3=%xmm4
movdqa %xmm3,%xmm4

# qhasm: uint32323232	diag3 <<= 16
# asm 1: pslld $16,<diag3=int6464#4
# asm 2: pslld $16,<diag3=%xmm3
pslld $16,%xmm3

# qhasm: uint32323232	b3 >>= 16
# asm 1: psrld $16,<b3=int6464#5
# asm 2: psrld $16,<b3=%xmm4
psrld $16,%xmm4

# qhasm: 		diag3 ^= b3
# asm 1: pxor  <b3=int6464#5,<diag3=int6464#4
# asm 2: pxor  <b3=%xmm4,<diag3=%xmm3
pxor  %xmm4,%xmm3

# qhasm: uint32323232			diag2 += diag3
# asm 1: paddd <diag3=int6464#4,<diag2=int6464#3
# asm 2: paddd <diag3=%xmm3,<diag2=%xmm2
paddd %xmm3,%xmm2

# qhasm: 				diag1 ^= diag2
# asm 1: pxor  <diag2=int6464#3,<diag1=int6464#2
# asm 2: pxor  <diag2=%xmm2,<diag1=%xmm1
pxor  %xmm2,%xmm1

# qhasm: 				b1 = diag1
# asm 1: movdqa <diag1=int6464#2,>b1=int6464#5
# asm 2: movdqa <diag1=%xmm1,>b1=%xmm4
movdqa %xmm1,%xmm4

# qhasm: uint32323232			diag1 <<= 12
# asm 1: pslld $12,<diag1=int6464#2
# asm 2: pslld $12,<diag1=%xmm1
pslld $12,%xmm1

# qhasm: uint32323232			b1 >>= 20
# asm 1: psrld $20,<b1=int6464#5
# asm 2: psrld $20,<b1=%xmm4
psrld $20,%xmm4

# qhasm: 				diag1 ^= b1
# asm 1: pxor  <b1=int6464#5,<diag1=int6464#2
# asm 2: pxor  <b1=%xmm4,<diag1=%xmm1
pxor  %xmm4,%xmm1

# qhasm: uint32323232					diag0 += diag1
# asm 1: paddd <diag1=int6464#2,<diag0=int6464#1
# asm 2: paddd <diag1=%xmm1,<diag0=%xmm0
paddd %xmm1,%xmm0

# qhasm: 						diag3 ^= diag0
# asm 1: pxor  <diag0=int6464#1,<diag3=int6464#4
# asm 2: pxor  <diag0=%xmm0,<diag3=%xmm3
pxor  %xmm0,%xmm3

# qhasm: 						b3 = diag3
# asm 1: movdqa <diag3=int6464#4,>b3=int6464#5
# asm 2: movdqa <diag3=%xmm3,>b3=%xmm4
movdqa %xmm3,%xmm4

# qhasm: uint32323232					diag3 <<= 8
# asm 1: pslld $8,<diag3=int6464#4
# asm 2: pslld $8,<diag3=%xmm3
pslld $8,%xmm3

# qhasm: uint32323232					b3 >>= 24
# asm 1: psrld $24,<b3=int6464#5
# asm 2: psrld $24,<b3=%xmm4
psrld $24,%xmm4

# qhasm: 		diag0 <<<= 32
# asm 1: pshufd $0x93,<diag0=int6464#1,<diag0=int6464#1
# asm 2: pshufd $0x93,<diag0=%xmm0,<diag0=%xmm0
pshufd $0x93,%xmm0,%xmm0

# qhasm: 						diag3 ^= b3
# asm 1: pxor  <b3=int6464#5,<diag3=int6464#4
# asm 2: pxor  <b3=%xmm4,<diag3=%xmm3
pxor  %xmm4,%xmm3

# qhasm: uint32323232							diag2 += diag3
# asm 1: paddd <diag3=int6464#4,<diag2=int6464#3
# asm 2: paddd <diag3=%xmm3,<diag2=%xmm2
paddd %xmm3,%xmm2

# qhasm: 		diag3 <<<= 64
# asm 1: pshufd $0x4e,<diag3=int6464#4,<diag3=int6464#4
# asm 2: pshufd $0x4e,<diag3=%xmm3,<diag3=%xmm3
pshufd $0x4e,%xmm3,%xmm3

# qhasm: 								diag1 ^= diag2
# asm 1: pxor  <diag2=int6464#3,<diag1=int6464#2
# asm 2: pxor  <diag2=%xmm2,<diag1=%xmm1
pxor  %xmm2,%xmm1

# qhasm: 		diag2 <<<= 96
# asm 1: pshufd $0x39,<diag2=int6464#3,<diag2=int6464#3
# asm 2: pshufd $0x39,<diag2=%xmm2,<diag2=%xmm2
pshufd $0x39,%xmm2,%xmm2

# qhasm: 								b1 = diag1
# asm 1: movdqa <diag1=int6464#2,>b1=int6464#5
# asm 2: movdqa <diag1=%xmm1,>b1=%xmm4
movdqa %xmm1,%xmm4

# qhasm: uint32323232							diag1 <<= 7
# asm 1: pslld $7,<diag1=int6464#2
# asm 2: pslld $7,<diag1=%xmm1
pslld $7,%xmm1

# qhasm: uint32323232							b1 >>= 25
# asm 1: psrld $25,<b1=int6464#5
# asm 2: psrld $25,<b1=%xmm4
psrld $25,%xmm4

# qhasm: 								diag1 ^= b1
# asm 1: pxor  <b1=int6464#5,<diag1=int6464#2
# asm 2: pxor  <b1=%xmm4,<diag1=%xmm1
pxor  %xmm4,%xmm1

# qhasm: 		 unsigned>? i -= 2
# asm 1: sub  $2,<i=int32#1
# asm 2: sub  $2,<i=%eax
sub  $2,%eax

# qhasm: uint32323232	diag0 += diag1
# asm 1: paddd <diag1=int6464#2,<diag0=int6464#1
# asm 2: paddd <diag1=%xmm1,<diag0=%xmm0
paddd %xmm1,%xmm0

# qhasm: 		diag3 ^= diag0
# asm 1: pxor  <diag0=int6464#1,<diag3=int6464#4
# asm 2: pxor  <diag0=%xmm0,<diag3=%xmm3
pxor  %xmm0,%xmm3

# qhasm: 		b3 = diag3
# asm 1: movdqa <diag3=int6464#4,>b3=int6464#5
# asm 2: movdqa <diag3=%xmm3,>b3=%xmm4
movdqa %xmm3,%xmm4

# qhasm: uint32323232	diag3 <<= 16
# asm 1: pslld $16,<diag3=int6464#4
# asm 2: pslld $16,<diag3=%xmm3
pslld $16,%xmm3

# qhasm: uint32323232	b3 >>= 16
# asm 1: psrld $16,<b3=int6464#5
# asm 2: psrld $16,<b3=%xmm4
psrld $16,%xmm4

# qhasm: 		diag3 ^= b3
# asm 1: pxor  <b3=int6464#5,<diag3=int6464#4
# asm 2: pxor  <b3=%xmm4,<diag3=%xmm3
pxor  %xmm4,%xmm3

# qhasm: uint32323232			diag2 += diag3
# asm 1: paddd <diag3=int6464#4,<diag2=int6464#3
# asm 2: paddd <diag3=%xmm3,<diag2=%xmm2
paddd %xmm3,%xmm2

# qhasm: 				diag1 ^= diag2
# asm 1: pxor  <diag2=int6464#3,<diag1=int6464#2
# asm 2: pxor  <diag2=%xmm2,<diag1=%xmm1
pxor  %xmm2,%xmm1

# qhasm: 				b1 = diag1
# asm 1: movdqa <diag1=int6464#2,>b1=int6464#5
# asm 2: movdqa <diag1=%xmm1,>b1=%xmm4
movdqa %xmm1,%xmm4

# qhasm: uint32323232			diag1 <<= 12
# asm 1: pslld $12,<diag1=int6464#2
# asm 2: pslld $12,<diag1=%xmm1
pslld $12,%xmm1

# qhasm: uint32323232			b1 >>= 20
# asm 1: psrld $20,<b1=int6464#5
# asm 2: psrld $20,<b1=%xmm4
psrld $20,%xmm4

# qhasm: 				diag1 ^= b1
# asm 1: pxor  <b1=int6464#5,<diag1=int6464#2
# asm 2: pxor  <b1=%xmm4,<diag1=%xmm1
pxor  %xmm4,%xmm1

# qhasm: uint32323232					diag0 += diag1
# asm 1: paddd <diag1=int6464#2,<diag0=int6464#1
# asm 2: paddd <diag1=%xmm1,<diag0=%xmm0
paddd %xmm1,%xmm0

# qhasm: 						diag3 ^= diag0
# asm 1: pxor  <diag0=int6464#1,<diag3=int6464#4
# asm 2: pxor  <diag0=%xmm0,<diag3=%xmm3
pxor  %xmm0,%xmm3

# qhasm: 						b3 = diag3
# asm 1: movdqa <diag3=int6464#4,>b3=int6464#5
# asm 2: movdqa <diag3=%xmm3,>b3=%xmm4
movdqa %xmm3,%xmm4

# qhasm: uint32323232					diag3 <<= 8
# asm 1: pslld $8,<diag3=int6464#4
# asm 2: pslld $8,<diag3=%xmm3
pslld $8,%xmm3

# qhasm: uint32323232					b3 >>= 24
# asm 1: psrld $24,<b3=int6464#5
# asm 2: psrld $24,<b3=%xmm4
psrld $24,%xmm4

# qhasm: 		diag0 <<<= 96
# asm 1: pshufd $0x39,<diag0=int6464#1,<diag0=int6464#1
# asm 2: pshufd $0x39,<diag0=%xmm0,<diag0=%xmm0
pshufd $0x39,%xmm0,%xmm0

# qhasm: 						diag3 ^= b3
# asm 1: pxor  <b3=int6464#5,<diag3=int6464#4
# asm 2: pxor  <b3=%xmm4,<diag3=%xmm3
pxor  %xmm4,%xmm3

# qhasm: uint32323232							diag2 += diag3
# asm 1: paddd <diag3=int6464#4,<diag2=int6464#3
# asm 2: paddd <diag3=%xmm3,<diag2=%xmm2
paddd %xmm3,%xmm2

# qhasm: 		diag3 <<<= 64
# asm 1: pshufd $0x4e,<diag3=int6464#4,<diag3=int6464#4
# asm 2: pshufd $0x4e,<diag3=%xmm3,<diag3=%xmm3
pshufd $0x4e,%xmm3,%xmm3

# qhasm: 								diag1 ^= diag2
# asm 1: pxor  <diag2=int6464#3,<diag1=int6464#2
# asm 2: pxor  <diag2=%xmm2,<diag1=%xmm1
pxor  %xmm2,%xmm1

# qhasm: 		diag2 <<<= 32
# asm 1: pshufd $0x93,<diag2=int6464#3,<diag2=int6464#3
# asm 2: pshufd $0x93,<diag2=%xmm2,<diag2=%xmm2
pshufd $0x93,%xmm2,%xmm2

# qhasm: 								b1 = diag1
# asm 1: movdqa <diag1=int6464#2,>b1=int6464#5
# asm 2: movdqa <diag1=%xmm1,>b1=%xmm4
movdqa %xmm1,%xmm4

# qhasm: uint32323232							diag1 <<= 7
# asm 1: pslld $7,<diag1=int6464#2
# asm 2: pslld $7,<diag1=%xmm1
pslld $7,%xmm1

# qhasm: uint32323232							b1 >>= 25
# asm 1: psrld $25,<b1=int6464#5
# asm 2: psrld $25,<b1=%xmm4
psrld $25,%xmm4

# qhasm: 								diag1 ^= b1
# asm 1: pxor  <b1=int6464#5,<diag1=int6464#2
# asm 2: pxor  <b1=%xmm4,<diag1=%xmm1
pxor  %xmm4,%xmm1
# comment:fp stack unchanged by jump

# qhasm: goto mainloop if unsigned>
ja ._mainloop

# qhasm: uint32323232 diag0 += *(int128 *) (x + 0)
# asm 1: paddd 0(<x=int32#3),<diag0=int6464#1
# asm 2: paddd 0(<x=%edx),<diag0=%xmm0
paddd 0(%edx),%xmm0

# qhasm: uint32323232 diag1 += *(int128 *) (x + 16)
# asm 1: paddd 16(<x=int32#3),<diag1=int6464#2
# asm 2: paddd 16(<x=%edx),<diag1=%xmm1
paddd 16(%edx),%xmm1

# qhasm: uint32323232 diag2 += *(int128 *) (x + 32)
# asm 1: paddd 32(<x=int32#3),<diag2=int6464#3
# asm 2: paddd 32(<x=%edx),<diag2=%xmm2
paddd 32(%edx),%xmm2

# qhasm: uint32323232 diag3 += *(int128 *) (x + 48)
# asm 1: paddd 48(<x=int32#3),<diag3=int6464#4
# asm 2: paddd 48(<x=%edx),<diag3=%xmm3
paddd 48(%edx),%xmm3

# qhasm: uint32323232 diag0 ^= *(int128 *) (m + 0)
# asm 1: pxor 0(<m=int32#5),<diag0=int6464#1
# asm 2: pxor 0(<m=%esi),<diag0=%xmm0
pxor 0(%esi),%xmm0

# qhasm: uint32323232 diag1 ^= *(int128 *) (m + 16)
# asm 1: pxor 16(<m=int32#5),<diag1=int6464#2
# asm 2: pxor 16(<m=%esi),<diag1=%xmm1
pxor 16(%esi),%xmm1

# qhasm: uint32323232 diag2 ^= *(int128 *) (m + 32)
# asm 1: pxor 32(<m=int32#5),<diag2=int6464#3
# asm 2: pxor 32(<m=%esi),<diag2=%xmm2
pxor 32(%esi),%xmm2

# qhasm: uint32323232 diag3 ^= *(int128 *) (m + 48)
# asm 1: pxor 48(<m=int32#5),<diag3=int6464#4
# asm 2: pxor 48(<m=%esi),<diag3=%xmm3
pxor 48(%esi),%xmm3

# qhasm: *(int128 *) (out + 0) = diag0
# asm 1: movdqa <diag0=int6464#1,0(<out=int32#6)
# asm 2: movdqa <diag0=%xmm0,0(<out=%edi)
movdqa %xmm0,0(%edi)

# qhasm: *(int128 *) (out + 16) = diag1
# asm 1: movdqa <diag1=int6464#2,16(<out=int32#6)
# asm 2: movdqa <diag1=%xmm1,16(<out=%edi)
movdqa %xmm1,16(%edi)

# qhasm: *(int128 *) (out + 32) = diag2
# asm 1: movdqa <diag2=int6464#3,32(<out=int32#6)
# asm 2: movdqa <diag2=%xmm2,32(<out=%edi)
movdqa %xmm2,32(%edi)

# qhasm: *(int128 *) (out + 48) = diag3
# asm 1: movdqa <diag3=int6464#4,48(<out=int32#6)
# asm 2: movdqa <diag3=%xmm3,48(<out=%edi)
movdqa %xmm3,48(%edi)

# qhasm:   bytes = bytes_backup
# asm 1: movl <bytes_backup=stack32#7,>bytes=int32#4
# asm 2: movl <bytes_backup=24(%esp),>bytes=%ebx
movl 24(%esp),%ebx

# qhasm:   in12 = *(uint32 *) (x + 48)
# asm 1: movl 48(<x=int32#3),>in12=int32#1
# asm 2: movl 48(<x=%edx),>in12=%eax
movl 48(%edx),%eax

# qhasm:   in13 = *(uint32 *) (x + 52)
# asm 1: movl 52(<x=int32#3),>in13=int32#2
# asm 2: movl 52(<x=%edx),>in13=%ecx
movl 52(%edx),%ecx

# qhasm:   carry? in12 += 1
# asm 1: add  $1,<in12=int32#1
# asm 2: add  $1,<in12=%eax
add  $1,%eax

# qhasm:   in13 += 0 + carry
# asm 1: adc $0,<in13=int32#2
# asm 2: adc $0,<in13=%ecx
adc $0,%ecx

# qhasm:   *(uint32 *) (x + 48) = in12
# asm 1: movl <in12=int32#1,48(<x=int32#3)
# asm 2: movl <in12=%eax,48(<x=%edx)
movl %eax,48(%edx)

# qhasm:   *(uint32 *) (x + 52) = in13
# asm 1: movl <in13=int32#2,52(<x=int32#3)
# asm 2: movl <in13=%ecx,52(<x=%edx)
movl %ecx,52(%edx)

# qhasm:                          unsigned>? unsigned<? bytes - 64
# asm 1: cmp  $64,<bytes=int32#4
# asm 2: cmp  $64,<bytes=%ebx
cmp  $64,%ebx
# comment:fp stack unchanged by jump

# qhasm:   goto bytesatleast65 if unsigned>
ja ._bytesatleast65
# comment:fp stack unchanged by jump

# qhasm:     goto bytesatleast64 if !unsigned<
jae ._bytesatleast64

# qhasm:       m = out
# asm 1: mov  <out=int32#6,>m=int32#5
# asm 2: mov  <out=%edi,>m=%esi
mov  %edi,%esi

# qhasm:       out = ctarget
# asm 1: movl <ctarget=stack32#6,>out=int32#6
# asm 2: movl <ctarget=20(%esp),>out=%edi
movl 20(%esp),%edi

# qhasm:       i = bytes
# asm 1: mov  <bytes=int32#4,>i=int32#2
# asm 2: mov  <bytes=%ebx,>i=%ecx
mov  %ebx,%ecx

# qhasm:       while (i) { *out++ = *m++; --i }
rep movsb
# comment:fp stack unchanged by fallthrough

# qhasm:     bytesatleast64:
._bytesatleast64:
# comment:fp stack unchanged by fallthrough

# qhasm:     done:
._done:

# qhasm:     eax = eax_stack
# asm 1: movl <eax_stack=stack32#1,>eax=int32#1
# asm 2: movl <eax_stack=0(%esp),>eax=%eax
movl 0(%esp),%eax

# qhasm:     ebx = ebx_stack
# asm 1: movl <ebx_stack=stack32#2,>ebx=int32#4
# asm 2: movl <ebx_stack=4(%esp),>ebx=%ebx
movl 4(%esp),%ebx

# qhasm:     esi = esi_stack
# asm 1: movl <esi_stack=stack32#3,>esi=int32#5
# asm 2: movl <esi_stack=8(%esp),>esi=%esi
movl 8(%esp),%esi

# qhasm:     edi = edi_stack
# asm 1: movl <edi_stack=stack32#4,>edi=int32#6
# asm 2: movl <edi_stack=12(%esp),>edi=%edi
movl 12(%esp),%edi

# qhasm:     ebp = ebp_stack
# asm 1: movl <ebp_stack=stack32#5,>ebp=int32#7
# asm 2: movl <ebp_stack=16(%esp),>ebp=%ebp
movl 16(%esp),%ebp

# qhasm:     leave
add %eax,%esp
ret

# qhasm:   bytesatleast65:
._bytesatleast65:

# qhasm:   bytes -= 64
# asm 1: sub  $64,<bytes=int32#4
# asm 2: sub  $64,<bytes=%ebx
sub  $64,%ebx

# qhasm:   out += 64
# asm 1: add  $64,<out=int32#6
# asm 2: add  $64,<out=%edi
add  $64,%edi

# qhasm:   m += 64
# asm 1: add  $64,<m=int32#5
# asm 2: add  $64,<m=%esi
add  $64,%esi
# comment:fp stack unchanged by jump

# qhasm: goto bytesatleast1
jmp ._bytesatleast1

# qhasm: enter ECRYPT_init
.text
.p2align 5
.globl _ECRYPT_init
.globl ECRYPT_init
_ECRYPT_init:
ECRYPT_init:
mov %esp,%eax
and $31,%eax
add $96,%eax
sub %eax,%esp

# qhasm: leave
add %eax,%esp
ret

# qhasm: enter ECRYPT_keysetup
.text
.p2align 5
.globl _ECRYPT_keysetup
.globl ECRYPT_keysetup
_ECRYPT_keysetup:
ECRYPT_keysetup:
mov %esp,%eax
and $31,%eax
add $96,%eax
sub %eax,%esp

# qhasm:   eax_stack = eax
# asm 1: movl <eax=int32#1,>eax_stack=stack32#1
# asm 2: movl <eax=%eax,>eax_stack=0(%esp)
movl %eax,0(%esp)

# qhasm:   ebx_stack = ebx
# asm 1: movl <ebx=int32#4,>ebx_stack=stack32#2
# asm 2: movl <ebx=%ebx,>ebx_stack=4(%esp)
movl %ebx,4(%esp)

# qhasm:   esi_stack = esi
# asm 1: movl <esi=int32#5,>esi_stack=stack32#3
# asm 2: movl <esi=%esi,>esi_stack=8(%esp)
movl %esi,8(%esp)

# qhasm:   edi_stack = edi
# asm 1: movl <edi=int32#6,>edi_stack=stack32#4
# asm 2: movl <edi=%edi,>edi_stack=12(%esp)
movl %edi,12(%esp)

# qhasm:   ebp_stack = ebp
# asm 1: movl <ebp=int32#7,>ebp_stack=stack32#5
# asm 2: movl <ebp=%ebp,>ebp_stack=16(%esp)
movl %ebp,16(%esp)

# qhasm:   k = arg2
# asm 1: movl <arg2=stack32#-2,>k=int32#2
# asm 2: movl <arg2=8(%esp,%eax),>k=%ecx
movl 8(%esp,%eax),%ecx

# qhasm:   kbits = arg3
# asm 1: movl <arg3=stack32#-3,>kbits=int32#3
# asm 2: movl <arg3=12(%esp,%eax),>kbits=%edx
movl 12(%esp,%eax),%edx

# qhasm:   x = arg1
# asm 1: movl <arg1=stack32#-1,>x=int32#1
# asm 2: movl <arg1=4(%esp,%eax),>x=%eax
movl 4(%esp,%eax),%eax

# qhasm:   in4 = *(uint32 *) (k + 0)
# asm 1: movl 0(<k=int32#2),>in4=int32#4
# asm 2: movl 0(<k=%ecx),>in4=%ebx
movl 0(%ecx),%ebx

# qhasm:   in5 = *(uint32 *) (k + 4)
# asm 1: movl 4(<k=int32#2),>in5=int32#5
# asm 2: movl 4(<k=%ecx),>in5=%esi
movl 4(%ecx),%esi

# qhasm:   in6 = *(uint32 *) (k + 8)
# asm 1: movl 8(<k=int32#2),>in6=int32#6
# asm 2: movl 8(<k=%ecx),>in6=%edi
movl 8(%ecx),%edi

# qhasm:   in7 = *(uint32 *) (k + 12)
# asm 1: movl 12(<k=int32#2),>in7=int32#7
# asm 2: movl 12(<k=%ecx),>in7=%ebp
movl 12(%ecx),%ebp

# qhasm:   *(uint32 *) (x + 16) = in4
# asm 1: movl <in4=int32#4,16(<x=int32#1)
# asm 2: movl <in4=%ebx,16(<x=%eax)
movl %ebx,16(%eax)

# qhasm:   *(uint32 *) (x + 20) = in5
# asm 1: movl <in5=int32#5,20(<x=int32#1)
# asm 2: movl <in5=%esi,20(<x=%eax)
movl %esi,20(%eax)

# qhasm:   *(uint32 *) (x + 24) = in6
# asm 1: movl <in6=int32#6,24(<x=int32#1)
# asm 2: movl <in6=%edi,24(<x=%eax)
movl %edi,24(%eax)

# qhasm:   *(uint32 *) (x + 28) = in7
# asm 1: movl <in7=int32#7,28(<x=int32#1)
# asm 2: movl <in7=%ebp,28(<x=%eax)
movl %ebp,28(%eax)

# qhasm:                    unsigned<? kbits - 256
# asm 1: cmp  $256,<kbits=int32#3
# asm 2: cmp  $256,<kbits=%edx
cmp  $256,%edx
# comment:fp stack unchanged by jump

# qhasm:   goto kbits128 if unsigned<
jb ._kbits128

# qhasm:   kbits256:
._kbits256:

# qhasm:     in8 = *(uint32 *) (k + 16)
# asm 1: movl 16(<k=int32#2),>in8=int32#3
# asm 2: movl 16(<k=%ecx),>in8=%edx
movl 16(%ecx),%edx

# qhasm:     in9 = *(uint32 *) (k + 20)
# asm 1: movl 20(<k=int32#2),>in9=int32#4
# asm 2: movl 20(<k=%ecx),>in9=%ebx
movl 20(%ecx),%ebx

# qhasm:     in10 = *(uint32 *) (k + 24)
# asm 1: movl 24(<k=int32#2),>in10=int32#5
# asm 2: movl 24(<k=%ecx),>in10=%esi
movl 24(%ecx),%esi

# qhasm:     in11 = *(uint32 *) (k + 28)
# asm 1: movl 28(<k=int32#2),>in11=int32#2
# asm 2: movl 28(<k=%ecx),>in11=%ecx
movl 28(%ecx),%ecx

# qhasm:     *(uint32 *) (x + 32) = in8
# asm 1: movl <in8=int32#3,32(<x=int32#1)
# asm 2: movl <in8=%edx,32(<x=%eax)
movl %edx,32(%eax)

# qhasm:     *(uint32 *) (x + 36) = in9
# asm 1: movl <in9=int32#4,36(<x=int32#1)
# asm 2: movl <in9=%ebx,36(<x=%eax)
movl %ebx,36(%eax)

# qhasm:     *(uint32 *) (x + 40) = in10
# asm 1: movl <in10=int32#5,40(<x=int32#1)
# asm 2: movl <in10=%esi,40(<x=%eax)
movl %esi,40(%eax)

# qhasm:     *(uint32 *) (x + 44) = in11
# asm 1: movl <in11=int32#2,44(<x=int32#1)
# asm 2: movl <in11=%ecx,44(<x=%eax)
movl %ecx,44(%eax)

# qhasm:     in0 = 1634760805
# asm 1: mov  $1634760805,>in0=int32#2
# asm 2: mov  $1634760805,>in0=%ecx
mov  $1634760805,%ecx

# qhasm:     in1 = 857760878
# asm 1: mov  $857760878,>in1=int32#3
# asm 2: mov  $857760878,>in1=%edx
mov  $857760878,%edx

# qhasm:     in2 = 2036477234
# asm 1: mov  $2036477234,>in2=int32#4
# asm 2: mov  $2036477234,>in2=%ebx
mov  $2036477234,%ebx

# qhasm:     in3 = 1797285236
# asm 1: mov  $1797285236,>in3=int32#5
# asm 2: mov  $1797285236,>in3=%esi
mov  $1797285236,%esi

# qhasm:     *(uint32 *) (x + 0) = in0
# asm 1: movl <in0=int32#2,0(<x=int32#1)
# asm 2: movl <in0=%ecx,0(<x=%eax)
movl %ecx,0(%eax)

# qhasm:     *(uint32 *) (x + 4) = in1
# asm 1: movl <in1=int32#3,4(<x=int32#1)
# asm 2: movl <in1=%edx,4(<x=%eax)
movl %edx,4(%eax)

# qhasm:     *(uint32 *) (x + 8) = in2
# asm 1: movl <in2=int32#4,8(<x=int32#1)
# asm 2: movl <in2=%ebx,8(<x=%eax)
movl %ebx,8(%eax)

# qhasm:     *(uint32 *) (x + 12) = in3
# asm 1: movl <in3=int32#5,12(<x=int32#1)
# asm 2: movl <in3=%esi,12(<x=%eax)
movl %esi,12(%eax)
# comment:fp stack unchanged by jump

# qhasm:   goto keysetupdone
jmp ._keysetupdone

# qhasm:   kbits128:
._kbits128:

# qhasm:     in8 = *(uint32 *) (k + 0)
# asm 1: movl 0(<k=int32#2),>in8=int32#3
# asm 2: movl 0(<k=%ecx),>in8=%edx
movl 0(%ecx),%edx

# qhasm:     in9 = *(uint32 *) (k + 4)
# asm 1: movl 4(<k=int32#2),>in9=int32#4
# asm 2: movl 4(<k=%ecx),>in9=%ebx
movl 4(%ecx),%ebx

# qhasm:     in10 = *(uint32 *) (k + 8)
# asm 1: movl 8(<k=int32#2),>in10=int32#5
# asm 2: movl 8(<k=%ecx),>in10=%esi
movl 8(%ecx),%esi

# qhasm:     in11 = *(uint32 *) (k + 12)
# asm 1: movl 12(<k=int32#2),>in11=int32#2
# asm 2: movl 12(<k=%ecx),>in11=%ecx
movl 12(%ecx),%ecx

# qhasm:     *(uint32 *) (x + 32) = in8
# asm 1: movl <in8=int32#3,32(<x=int32#1)
# asm 2: movl <in8=%edx,32(<x=%eax)
movl %edx,32(%eax)

# qhasm:     *(uint32 *) (x + 36) = in9
# asm 1: movl <in9=int32#4,36(<x=int32#1)
# asm 2: movl <in9=%ebx,36(<x=%eax)
movl %ebx,36(%eax)

# qhasm:     *(uint32 *) (x + 40) = in10
# asm 1: movl <in10=int32#5,40(<x=int32#1)
# asm 2: movl <in10=%esi,40(<x=%eax)
movl %esi,40(%eax)

# qhasm:     *(uint32 *) (x + 44) = in11
# asm 1: movl <in11=int32#2,44(<x=int32#1)
# asm 2: movl <in11=%ecx,44(<x=%eax)
movl %ecx,44(%eax)

# qhasm:     in0 = 1634760805
# asm 1: mov  $1634760805,>in0=int32#2
# asm 2: mov  $1634760805,>in0=%ecx
mov  $1634760805,%ecx

# qhasm:     in1 = 824206446
# asm 1: mov  $824206446,>in1=int32#3
# asm 2: mov  $824206446,>in1=%edx
mov  $824206446,%edx

# qhasm:     in2 = 2036477238
# asm 1: mov  $2036477238,>in2=int32#4
# asm 2: mov  $2036477238,>in2=%ebx
mov  $2036477238,%ebx

# qhasm:     in3 = 1797285236
# asm 1: mov  $1797285236,>in3=int32#5
# asm 2: mov  $1797285236,>in3=%esi
mov  $1797285236,%esi

# qhasm:     *(uint32 *) (x + 0) = in0
# asm 1: movl <in0=int32#2,0(<x=int32#1)
# asm 2: movl <in0=%ecx,0(<x=%eax)
movl %ecx,0(%eax)

# qhasm:     *(uint32 *) (x + 4) = in1
# asm 1: movl <in1=int32#3,4(<x=int32#1)
# asm 2: movl <in1=%edx,4(<x=%eax)
movl %edx,4(%eax)

# qhasm:     *(uint32 *) (x + 8) = in2
# asm 1: movl <in2=int32#4,8(<x=int32#1)
# asm 2: movl <in2=%ebx,8(<x=%eax)
movl %ebx,8(%eax)

# qhasm:     *(uint32 *) (x + 12) = in3
# asm 1: movl <in3=int32#5,12(<x=int32#1)
# asm 2: movl <in3=%esi,12(<x=%eax)
movl %esi,12(%eax)

# qhasm:   keysetupdone:
._keysetupdone:

# qhasm:   eax = eax_stack
# asm 1: movl <eax_stack=stack32#1,>eax=int32#1
# asm 2: movl <eax_stack=0(%esp),>eax=%eax
movl 0(%esp),%eax

# qhasm:   ebx = ebx_stack
# asm 1: movl <ebx_stack=stack32#2,>ebx=int32#4
# asm 2: movl <ebx_stack=4(%esp),>ebx=%ebx
movl 4(%esp),%ebx

# qhasm:   esi = esi_stack
# asm 1: movl <esi_stack=stack32#3,>esi=int32#5
# asm 2: movl <esi_stack=8(%esp),>esi=%esi
movl 8(%esp),%esi

# qhasm:   edi = edi_stack
# asm 1: movl <edi_stack=stack32#4,>edi=int32#6
# asm 2: movl <edi_stack=12(%esp),>edi=%edi
movl 12(%esp),%edi

# qhasm:   ebp = ebp_stack
# asm 1: movl <ebp_stack=stack32#5,>ebp=int32#7
# asm 2: movl <ebp_stack=16(%esp),>ebp=%ebp
movl 16(%esp),%ebp

# qhasm: leave
add %eax,%esp
ret

# qhasm: enter ECRYPT_ivsetup
.text
.p2align 5
.globl _ECRYPT_ivsetup
.globl ECRYPT_ivsetup
_ECRYPT_ivsetup:
ECRYPT_ivsetup:
mov %esp,%eax
and $31,%eax
add $96,%eax
sub %eax,%esp

# qhasm:   eax_stack = eax
# asm 1: movl <eax=int32#1,>eax_stack=stack32#1
# asm 2: movl <eax=%eax,>eax_stack=0(%esp)
movl %eax,0(%esp)

# qhasm:   ebx_stack = ebx
# asm 1: movl <ebx=int32#4,>ebx_stack=stack32#2
# asm 2: movl <ebx=%ebx,>ebx_stack=4(%esp)
movl %ebx,4(%esp)

# qhasm:   esi_stack = esi
# asm 1: movl <esi=int32#5,>esi_stack=stack32#3
# asm 2: movl <esi=%esi,>esi_stack=8(%esp)
movl %esi,8(%esp)

# qhasm:   edi_stack = edi
# asm 1: movl <edi=int32#6,>edi_stack=stack32#4
# asm 2: movl <edi=%edi,>edi_stack=12(%esp)
movl %edi,12(%esp)

# qhasm:   ebp_stack = ebp
# asm 1: movl <ebp=int32#7,>ebp_stack=stack32#5
# asm 2: movl <ebp=%ebp,>ebp_stack=16(%esp)
movl %ebp,16(%esp)

# qhasm:   iv = arg2
# asm 1: movl <arg2=stack32#-2,>iv=int32#2
# asm 2: movl <arg2=8(%esp,%eax),>iv=%ecx
movl 8(%esp,%eax),%ecx

# qhasm:   x = arg1
# asm 1: movl <arg1=stack32#-1,>x=int32#1
# asm 2: movl <arg1=4(%esp,%eax),>x=%eax
movl 4(%esp,%eax),%eax

# qhasm:   in12 = 0
# asm 1: mov  $0,>in12=int32#3
# asm 2: mov  $0,>in12=%edx
mov  $0,%edx

# qhasm:   in13 = 0
# asm 1: mov  $0,>in13=int32#4
# asm 2: mov  $0,>in13=%ebx
mov  $0,%ebx

# qhasm:   in14 = *(uint32 *) (iv + 0)
# asm 1: movl 0(<iv=int32#2),>in14=int32#5
# asm 2: movl 0(<iv=%ecx),>in14=%esi
movl 0(%ecx),%esi

# qhasm:   in15 = *(uint32 *) (iv + 4)
# asm 1: movl 4(<iv=int32#2),>in15=int32#2
# asm 2: movl 4(<iv=%ecx),>in15=%ecx
movl 4(%ecx),%ecx

# qhasm:   *(uint32 *) (x + 48) = in12
# asm 1: movl <in12=int32#3,48(<x=int32#1)
# asm 2: movl <in12=%edx,48(<x=%eax)
movl %edx,48(%eax)

# qhasm:   *(uint32 *) (x + 52) = in13
# asm 1: movl <in13=int32#4,52(<x=int32#1)
# asm 2: movl <in13=%ebx,52(<x=%eax)
movl %ebx,52(%eax)

# qhasm:   *(uint32 *) (x + 56) = in14
# asm 1: movl <in14=int32#5,56(<x=int32#1)
# asm 2: movl <in14=%esi,56(<x=%eax)
movl %esi,56(%eax)

# qhasm:   *(uint32 *) (x + 60) = in15
# asm 1: movl <in15=int32#2,60(<x=int32#1)
# asm 2: movl <in15=%ecx,60(<x=%eax)
movl %ecx,60(%eax)

# qhasm:   eax = eax_stack
# asm 1: movl <eax_stack=stack32#1,>eax=int32#1
# asm 2: movl <eax_stack=0(%esp),>eax=%eax
movl 0(%esp),%eax

# qhasm:   ebx = ebx_stack
# asm 1: movl <ebx_stack=stack32#2,>ebx=int32#4
# asm 2: movl <ebx_stack=4(%esp),>ebx=%ebx
movl 4(%esp),%ebx

# qhasm:   esi = esi_stack
# asm 1: movl <esi_stack=stack32#3,>esi=int32#5
# asm 2: movl <esi_stack=8(%esp),>esi=%esi
movl 8(%esp),%esi

# qhasm:   edi = edi_stack
# asm 1: movl <edi_stack=stack32#4,>edi=int32#6
# asm 2: movl <edi_stack=12(%esp),>edi=%edi
movl 12(%esp),%edi

# qhasm:   ebp = ebp_stack
# asm 1: movl <ebp_stack=stack32#5,>ebp=int32#7
# asm 2: movl <ebp_stack=16(%esp),>ebp=%ebp
movl 16(%esp),%ebp

# qhasm: leave
add %eax,%esp
ret
