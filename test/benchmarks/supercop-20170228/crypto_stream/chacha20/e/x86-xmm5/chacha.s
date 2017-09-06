
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

# qhasm: int6464 p

# qhasm: int6464 q

# qhasm: int6464 r

# qhasm: int6464 s

# qhasm: int6464 t

# qhasm: int6464 u

# qhasm: int6464 v

# qhasm: int6464 w

# qhasm: int6464 mp

# qhasm: int6464 mq

# qhasm: int6464 mr

# qhasm: int6464 ms

# qhasm: int6464 mt

# qhasm: int6464 mu

# qhasm: int6464 mv

# qhasm: int6464 mw

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

# qhasm: int6464 z0

# qhasm: int6464 z1

# qhasm: int6464 z2

# qhasm: int6464 z3

# qhasm: int6464 z4

# qhasm: int6464 z5

# qhasm: int6464 z6

# qhasm: int6464 z7

# qhasm: int6464 z8

# qhasm: int6464 z9

# qhasm: int6464 z10

# qhasm: int6464 z11

# qhasm: int6464 z12

# qhasm: int6464 z13

# qhasm: int6464 z14

# qhasm: int6464 z15

# qhasm: stack128 z0_stack

# qhasm: stack128 z1_stack

# qhasm: stack128 z2_stack

# qhasm: stack128 z3_stack

# qhasm: stack128 z4_stack

# qhasm: stack128 z5_stack

# qhasm: stack128 z6_stack

# qhasm: stack128 z7_stack

# qhasm: stack128 z8_stack

# qhasm: stack128 z9_stack

# qhasm: stack128 z10_stack

# qhasm: stack128 z11_stack

# qhasm: stack128 z12_stack

# qhasm: stack128 z13_stack

# qhasm: stack128 z14_stack

# qhasm: stack128 z15_stack

# qhasm: stack128 orig0

# qhasm: stack128 orig1

# qhasm: stack128 orig2

# qhasm: stack128 orig3

# qhasm: stack128 orig4

# qhasm: stack128 orig5

# qhasm: stack128 orig6

# qhasm: stack128 orig7

# qhasm: stack128 orig8

# qhasm: stack128 orig9

# qhasm: stack128 orig10

# qhasm: stack128 orig11

# qhasm: stack128 orig12

# qhasm: stack128 orig13

# qhasm: stack128 orig14

# qhasm: stack128 orig15

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
add $640,%eax
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
add $640,%eax
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
add $640,%eax
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

# qhasm:                               unsigned<? bytes - 256
# asm 1: cmp  $256,<bytes=int32#4
# asm 2: cmp  $256,<bytes=%ebx
cmp  $256,%ebx
# comment:fp stack unchanged by jump

# qhasm:   goto bytesbetween1and255 if unsigned<
jb ._bytesbetween1and255

# qhasm:   z0 = *(int128 *) (x + 0)
# asm 1: movdqa 0(<x=int32#3),>z0=int6464#1
# asm 2: movdqa 0(<x=%edx),>z0=%xmm0
movdqa 0(%edx),%xmm0

# qhasm:   z1 = z0[1,1,1,1]
# asm 1: pshufd $0x55,<z0=int6464#1,>z1=int6464#2
# asm 2: pshufd $0x55,<z0=%xmm0,>z1=%xmm1
pshufd $0x55,%xmm0,%xmm1

# qhasm:   z2 = z0[2,2,2,2]
# asm 1: pshufd $0xaa,<z0=int6464#1,>z2=int6464#3
# asm 2: pshufd $0xaa,<z0=%xmm0,>z2=%xmm2
pshufd $0xaa,%xmm0,%xmm2

# qhasm:   z3 = z0[3,3,3,3]
# asm 1: pshufd $0xff,<z0=int6464#1,>z3=int6464#4
# asm 2: pshufd $0xff,<z0=%xmm0,>z3=%xmm3
pshufd $0xff,%xmm0,%xmm3

# qhasm:   z0 = z0[0,0,0,0]
# asm 1: pshufd $0x00,<z0=int6464#1,>z0=int6464#1
# asm 2: pshufd $0x00,<z0=%xmm0,>z0=%xmm0
pshufd $0x00,%xmm0,%xmm0

# qhasm:   orig0 = z0
# asm 1: movdqa <z0=int6464#1,>orig0=stack128#1
# asm 2: movdqa <z0=%xmm0,>orig0=32(%esp)
movdqa %xmm0,32(%esp)

# qhasm:   orig1 = z1
# asm 1: movdqa <z1=int6464#2,>orig1=stack128#2
# asm 2: movdqa <z1=%xmm1,>orig1=48(%esp)
movdqa %xmm1,48(%esp)

# qhasm:   orig2 = z2
# asm 1: movdqa <z2=int6464#3,>orig2=stack128#3
# asm 2: movdqa <z2=%xmm2,>orig2=64(%esp)
movdqa %xmm2,64(%esp)

# qhasm:   orig3 = z3
# asm 1: movdqa <z3=int6464#4,>orig3=stack128#4
# asm 2: movdqa <z3=%xmm3,>orig3=80(%esp)
movdqa %xmm3,80(%esp)

# qhasm:   z4 = *(int128 *) (x + 16)
# asm 1: movdqa 16(<x=int32#3),>z4=int6464#1
# asm 2: movdqa 16(<x=%edx),>z4=%xmm0
movdqa 16(%edx),%xmm0

# qhasm:   z5 = z4[1,1,1,1]
# asm 1: pshufd $0x55,<z4=int6464#1,>z5=int6464#2
# asm 2: pshufd $0x55,<z4=%xmm0,>z5=%xmm1
pshufd $0x55,%xmm0,%xmm1

# qhasm:   z6 = z4[2,2,2,2]
# asm 1: pshufd $0xaa,<z4=int6464#1,>z6=int6464#3
# asm 2: pshufd $0xaa,<z4=%xmm0,>z6=%xmm2
pshufd $0xaa,%xmm0,%xmm2

# qhasm:   z7 = z4[3,3,3,3]
# asm 1: pshufd $0xff,<z4=int6464#1,>z7=int6464#4
# asm 2: pshufd $0xff,<z4=%xmm0,>z7=%xmm3
pshufd $0xff,%xmm0,%xmm3

# qhasm:   z4 = z4[0,0,0,0]
# asm 1: pshufd $0x00,<z4=int6464#1,>z4=int6464#1
# asm 2: pshufd $0x00,<z4=%xmm0,>z4=%xmm0
pshufd $0x00,%xmm0,%xmm0

# qhasm:   orig4 = z4
# asm 1: movdqa <z4=int6464#1,>orig4=stack128#5
# asm 2: movdqa <z4=%xmm0,>orig4=96(%esp)
movdqa %xmm0,96(%esp)

# qhasm:   orig5 = z5
# asm 1: movdqa <z5=int6464#2,>orig5=stack128#6
# asm 2: movdqa <z5=%xmm1,>orig5=112(%esp)
movdqa %xmm1,112(%esp)

# qhasm:   orig6 = z6
# asm 1: movdqa <z6=int6464#3,>orig6=stack128#7
# asm 2: movdqa <z6=%xmm2,>orig6=128(%esp)
movdqa %xmm2,128(%esp)

# qhasm:   orig7 = z7
# asm 1: movdqa <z7=int6464#4,>orig7=stack128#8
# asm 2: movdqa <z7=%xmm3,>orig7=144(%esp)
movdqa %xmm3,144(%esp)

# qhasm:   z8 = *(int128 *) (x + 32)
# asm 1: movdqa 32(<x=int32#3),>z8=int6464#1
# asm 2: movdqa 32(<x=%edx),>z8=%xmm0
movdqa 32(%edx),%xmm0

# qhasm:   z9 = z8[1,1,1,1]
# asm 1: pshufd $0x55,<z8=int6464#1,>z9=int6464#2
# asm 2: pshufd $0x55,<z8=%xmm0,>z9=%xmm1
pshufd $0x55,%xmm0,%xmm1

# qhasm:   z10 = z8[2,2,2,2]
# asm 1: pshufd $0xaa,<z8=int6464#1,>z10=int6464#3
# asm 2: pshufd $0xaa,<z8=%xmm0,>z10=%xmm2
pshufd $0xaa,%xmm0,%xmm2

# qhasm:   z11 = z8[3,3,3,3]
# asm 1: pshufd $0xff,<z8=int6464#1,>z11=int6464#4
# asm 2: pshufd $0xff,<z8=%xmm0,>z11=%xmm3
pshufd $0xff,%xmm0,%xmm3

# qhasm:   z8 = z8[0,0,0,0]
# asm 1: pshufd $0x00,<z8=int6464#1,>z8=int6464#1
# asm 2: pshufd $0x00,<z8=%xmm0,>z8=%xmm0
pshufd $0x00,%xmm0,%xmm0

# qhasm:   orig8 = z8
# asm 1: movdqa <z8=int6464#1,>orig8=stack128#9
# asm 2: movdqa <z8=%xmm0,>orig8=160(%esp)
movdqa %xmm0,160(%esp)

# qhasm:   orig9 = z9
# asm 1: movdqa <z9=int6464#2,>orig9=stack128#10
# asm 2: movdqa <z9=%xmm1,>orig9=176(%esp)
movdqa %xmm1,176(%esp)

# qhasm:   orig10 = z10
# asm 1: movdqa <z10=int6464#3,>orig10=stack128#11
# asm 2: movdqa <z10=%xmm2,>orig10=192(%esp)
movdqa %xmm2,192(%esp)

# qhasm:   orig11 = z11
# asm 1: movdqa <z11=int6464#4,>orig11=stack128#12
# asm 2: movdqa <z11=%xmm3,>orig11=208(%esp)
movdqa %xmm3,208(%esp)

# qhasm:   z12 = *(int128 *) (x + 48)
# asm 1: movdqa 48(<x=int32#3),>z12=int6464#1
# asm 2: movdqa 48(<x=%edx),>z12=%xmm0
movdqa 48(%edx),%xmm0

# qhasm:   z14 = z12[2,2,2,2]
# asm 1: pshufd $0xaa,<z12=int6464#1,>z14=int6464#2
# asm 2: pshufd $0xaa,<z12=%xmm0,>z14=%xmm1
pshufd $0xaa,%xmm0,%xmm1

# qhasm:   z15 = z12[3,3,3,3]
# asm 1: pshufd $0xff,<z12=int6464#1,>z15=int6464#1
# asm 2: pshufd $0xff,<z12=%xmm0,>z15=%xmm0
pshufd $0xff,%xmm0,%xmm0

# qhasm:   orig14 = z14
# asm 1: movdqa <z14=int6464#2,>orig14=stack128#13
# asm 2: movdqa <z14=%xmm1,>orig14=224(%esp)
movdqa %xmm1,224(%esp)

# qhasm:   orig15 = z15
# asm 1: movdqa <z15=int6464#1,>orig15=stack128#14
# asm 2: movdqa <z15=%xmm0,>orig15=240(%esp)
movdqa %xmm0,240(%esp)

# qhasm: bytesatleast256:
._bytesatleast256:

# qhasm:   in12 = *(uint32 *) (x + 48)
# asm 1: movl 48(<x=int32#3),>in12=int32#1
# asm 2: movl 48(<x=%edx),>in12=%eax
movl 48(%edx),%eax

# qhasm:   in13 = *(uint32 *) (x + 52)
# asm 1: movl 52(<x=int32#3),>in13=int32#2
# asm 2: movl 52(<x=%edx),>in13=%ecx
movl 52(%edx),%ecx

# qhasm:   ((uint32 *) &orig12)[0] = in12
# asm 1: movl <in12=int32#1,>orig12=stack128#15
# asm 2: movl <in12=%eax,>orig12=256(%esp)
movl %eax,256(%esp)

# qhasm:   ((uint32 *) &orig13)[0] = in13
# asm 1: movl <in13=int32#2,>orig13=stack128#16
# asm 2: movl <in13=%ecx,>orig13=272(%esp)
movl %ecx,272(%esp)

# qhasm:   carry? in12 += 1
# asm 1: add  $1,<in12=int32#1
# asm 2: add  $1,<in12=%eax
add  $1,%eax

# qhasm:   in13 += 0 + carry
# asm 1: adc $0,<in13=int32#2
# asm 2: adc $0,<in13=%ecx
adc $0,%ecx

# qhasm:   ((uint32 *) &orig12)[1] = in12
# asm 1: movl <in12=int32#1,4+<orig12=stack128#15
# asm 2: movl <in12=%eax,4+<orig12=256(%esp)
movl %eax,4+256(%esp)

# qhasm:   ((uint32 *) &orig13)[1] = in13
# asm 1: movl <in13=int32#2,4+<orig13=stack128#16
# asm 2: movl <in13=%ecx,4+<orig13=272(%esp)
movl %ecx,4+272(%esp)

# qhasm:   carry? in12 += 1
# asm 1: add  $1,<in12=int32#1
# asm 2: add  $1,<in12=%eax
add  $1,%eax

# qhasm:   in13 += 0 + carry
# asm 1: adc $0,<in13=int32#2
# asm 2: adc $0,<in13=%ecx
adc $0,%ecx

# qhasm:   ((uint32 *) &orig12)[2] = in12
# asm 1: movl <in12=int32#1,8+<orig12=stack128#15
# asm 2: movl <in12=%eax,8+<orig12=256(%esp)
movl %eax,8+256(%esp)

# qhasm:   ((uint32 *) &orig13)[2] = in13
# asm 1: movl <in13=int32#2,8+<orig13=stack128#16
# asm 2: movl <in13=%ecx,8+<orig13=272(%esp)
movl %ecx,8+272(%esp)

# qhasm:   carry? in12 += 1
# asm 1: add  $1,<in12=int32#1
# asm 2: add  $1,<in12=%eax
add  $1,%eax

# qhasm:   in13 += 0 + carry
# asm 1: adc $0,<in13=int32#2
# asm 2: adc $0,<in13=%ecx
adc $0,%ecx

# qhasm:   ((uint32 *) &orig12)[3] = in12
# asm 1: movl <in12=int32#1,12+<orig12=stack128#15
# asm 2: movl <in12=%eax,12+<orig12=256(%esp)
movl %eax,12+256(%esp)

# qhasm:   ((uint32 *) &orig13)[3] = in13
# asm 1: movl <in13=int32#2,12+<orig13=stack128#16
# asm 2: movl <in13=%ecx,12+<orig13=272(%esp)
movl %ecx,12+272(%esp)

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

# qhasm:   bytes_backup = bytes
# asm 1: movl <bytes=int32#4,>bytes_backup=stack32#6
# asm 2: movl <bytes=%ebx,>bytes_backup=20(%esp)
movl %ebx,20(%esp)

# qhasm: i = 20
# asm 1: mov  $20,>i=int32#1
# asm 2: mov  $20,>i=%eax
mov  $20,%eax

# qhasm:   z5 = orig5
# asm 1: movdqa <orig5=stack128#6,>z5=int6464#1
# asm 2: movdqa <orig5=112(%esp),>z5=%xmm0
movdqa 112(%esp),%xmm0

# qhasm:   z10 = orig10
# asm 1: movdqa <orig10=stack128#11,>z10=int6464#2
# asm 2: movdqa <orig10=192(%esp),>z10=%xmm1
movdqa 192(%esp),%xmm1

# qhasm:   z15 = orig15
# asm 1: movdqa <orig15=stack128#14,>z15=int6464#3
# asm 2: movdqa <orig15=240(%esp),>z15=%xmm2
movdqa 240(%esp),%xmm2

# qhasm:   z14 = orig14
# asm 1: movdqa <orig14=stack128#13,>z14=int6464#4
# asm 2: movdqa <orig14=224(%esp),>z14=%xmm3
movdqa 224(%esp),%xmm3

# qhasm:   z3 = orig3
# asm 1: movdqa <orig3=stack128#4,>z3=int6464#5
# asm 2: movdqa <orig3=80(%esp),>z3=%xmm4
movdqa 80(%esp),%xmm4

# qhasm:   z6 = orig6
# asm 1: movdqa <orig6=stack128#7,>z6=int6464#6
# asm 2: movdqa <orig6=128(%esp),>z6=%xmm5
movdqa 128(%esp),%xmm5

# qhasm:   z11 = orig11
# asm 1: movdqa <orig11=stack128#12,>z11=int6464#7
# asm 2: movdqa <orig11=208(%esp),>z11=%xmm6
movdqa 208(%esp),%xmm6

# qhasm:   z1 = orig1
# asm 1: movdqa <orig1=stack128#2,>z1=int6464#8
# asm 2: movdqa <orig1=48(%esp),>z1=%xmm7
movdqa 48(%esp),%xmm7

# qhasm:   z5_stack = z5
# asm 1: movdqa <z5=int6464#1,>z5_stack=stack128#17
# asm 2: movdqa <z5=%xmm0,>z5_stack=288(%esp)
movdqa %xmm0,288(%esp)

# qhasm:   z10_stack = z10
# asm 1: movdqa <z10=int6464#2,>z10_stack=stack128#18
# asm 2: movdqa <z10=%xmm1,>z10_stack=304(%esp)
movdqa %xmm1,304(%esp)

# qhasm:   z15_stack = z15
# asm 1: movdqa <z15=int6464#3,>z15_stack=stack128#19
# asm 2: movdqa <z15=%xmm2,>z15_stack=320(%esp)
movdqa %xmm2,320(%esp)

# qhasm:   z14_stack = z14
# asm 1: movdqa <z14=int6464#4,>z14_stack=stack128#20
# asm 2: movdqa <z14=%xmm3,>z14_stack=336(%esp)
movdqa %xmm3,336(%esp)

# qhasm:   z3_stack = z3
# asm 1: movdqa <z3=int6464#5,>z3_stack=stack128#21
# asm 2: movdqa <z3=%xmm4,>z3_stack=352(%esp)
movdqa %xmm4,352(%esp)

# qhasm:   z6_stack = z6
# asm 1: movdqa <z6=int6464#6,>z6_stack=stack128#22
# asm 2: movdqa <z6=%xmm5,>z6_stack=368(%esp)
movdqa %xmm5,368(%esp)

# qhasm:   z11_stack = z11
# asm 1: movdqa <z11=int6464#7,>z11_stack=stack128#23
# asm 2: movdqa <z11=%xmm6,>z11_stack=384(%esp)
movdqa %xmm6,384(%esp)

# qhasm:   z1_stack = z1
# asm 1: movdqa <z1=int6464#8,>z1_stack=stack128#24
# asm 2: movdqa <z1=%xmm7,>z1_stack=400(%esp)
movdqa %xmm7,400(%esp)

# qhasm:   z7 = orig7
# asm 1: movdqa <orig7=stack128#8,>z7=int6464#5
# asm 2: movdqa <orig7=144(%esp),>z7=%xmm4
movdqa 144(%esp),%xmm4

# qhasm:   z13 = orig13
# asm 1: movdqa <orig13=stack128#16,>z13=int6464#6
# asm 2: movdqa <orig13=272(%esp),>z13=%xmm5
movdqa 272(%esp),%xmm5

# qhasm:   z2 = orig2
# asm 1: movdqa <orig2=stack128#3,>z2=int6464#7
# asm 2: movdqa <orig2=64(%esp),>z2=%xmm6
movdqa 64(%esp),%xmm6

# qhasm:   z9 = orig9
# asm 1: movdqa <orig9=stack128#10,>z9=int6464#8
# asm 2: movdqa <orig9=176(%esp),>z9=%xmm7
movdqa 176(%esp),%xmm7

# qhasm:                 p = orig0
# asm 1: movdqa <orig0=stack128#1,>p=int6464#1
# asm 2: movdqa <orig0=32(%esp),>p=%xmm0
movdqa 32(%esp),%xmm0

# qhasm:                 t = orig12
# asm 1: movdqa <orig12=stack128#15,>t=int6464#3
# asm 2: movdqa <orig12=256(%esp),>t=%xmm2
movdqa 256(%esp),%xmm2

# qhasm:                 q = orig4
# asm 1: movdqa <orig4=stack128#5,>q=int6464#4
# asm 2: movdqa <orig4=96(%esp),>q=%xmm3
movdqa 96(%esp),%xmm3

# qhasm:                 r = orig8
# asm 1: movdqa <orig8=stack128#9,>r=int6464#2
# asm 2: movdqa <orig8=160(%esp),>r=%xmm1
movdqa 160(%esp),%xmm1

# qhasm:   z7_stack = z7
# asm 1: movdqa <z7=int6464#5,>z7_stack=stack128#25
# asm 2: movdqa <z7=%xmm4,>z7_stack=416(%esp)
movdqa %xmm4,416(%esp)

# qhasm:   z13_stack = z13
# asm 1: movdqa <z13=int6464#6,>z13_stack=stack128#26
# asm 2: movdqa <z13=%xmm5,>z13_stack=432(%esp)
movdqa %xmm5,432(%esp)

# qhasm:   z2_stack = z2
# asm 1: movdqa <z2=int6464#7,>z2_stack=stack128#27
# asm 2: movdqa <z2=%xmm6,>z2_stack=448(%esp)
movdqa %xmm6,448(%esp)

# qhasm:   z9_stack = z9
# asm 1: movdqa <z9=int6464#8,>z9_stack=stack128#28
# asm 2: movdqa <z9=%xmm7,>z9_stack=464(%esp)
movdqa %xmm7,464(%esp)

# qhasm:   z0_stack = p
# asm 1: movdqa <p=int6464#1,>z0_stack=stack128#29
# asm 2: movdqa <p=%xmm0,>z0_stack=480(%esp)
movdqa %xmm0,480(%esp)

# qhasm:   z12_stack = t
# asm 1: movdqa <t=int6464#3,>z12_stack=stack128#30
# asm 2: movdqa <t=%xmm2,>z12_stack=496(%esp)
movdqa %xmm2,496(%esp)

# qhasm:   z4_stack = q
# asm 1: movdqa <q=int6464#4,>z4_stack=stack128#31
# asm 2: movdqa <q=%xmm3,>z4_stack=512(%esp)
movdqa %xmm3,512(%esp)

# qhasm:   z8_stack = r
# asm 1: movdqa <r=int6464#2,>z8_stack=stack128#32
# asm 2: movdqa <r=%xmm1,>z8_stack=528(%esp)
movdqa %xmm1,528(%esp)

# qhasm: mainloop1:
._mainloop1:

# qhasm: 		assign xmm0 to p

# qhasm: 		assign xmm1 to r

# qhasm: 		assign xmm2 to t

# qhasm: 		assign xmm3 to q

# qhasm:                   		mp = z1_stack
# asm 1: movdqa <z1_stack=stack128#24,>mp=int6464#5
# asm 2: movdqa <z1_stack=400(%esp),>mp=%xmm4
movdqa 400(%esp),%xmm4

# qhasm:                   		mq = z5_stack
# asm 1: movdqa <z5_stack=stack128#17,>mq=int6464#6
# asm 2: movdqa <z5_stack=288(%esp),>mq=%xmm5
movdqa 288(%esp),%xmm5

# qhasm:                   		mt = z13_stack
# asm 1: movdqa <z13_stack=stack128#26,>mt=int6464#7
# asm 2: movdqa <z13_stack=432(%esp),>mt=%xmm6
movdqa 432(%esp),%xmm6

# qhasm: uint32323232	p += q
# asm 1: paddd <q=int6464#4,<p=int6464#1
# asm 2: paddd <q=%xmm3,<p=%xmm0
paddd %xmm3,%xmm0

# qhasm: 		t ^= p
# asm 1: pxor  <p=int6464#1,<t=int6464#3
# asm 2: pxor  <p=%xmm0,<t=%xmm2
pxor  %xmm0,%xmm2

# qhasm: 		u = t
# asm 1: movdqa <t=int6464#3,>u=int6464#8
# asm 2: movdqa <t=%xmm2,>u=%xmm7
movdqa %xmm2,%xmm7

# qhasm: uint32323232	u >>= 16
# asm 1: psrld $16,<u=int6464#8
# asm 2: psrld $16,<u=%xmm7
psrld $16,%xmm7

# qhasm: uint32323232	t <<= 16
# asm 1: pslld $16,<t=int6464#3
# asm 2: pslld $16,<t=%xmm2
pslld $16,%xmm2

# qhasm: 		t ^= u
# asm 1: pxor  <u=int6464#8,<t=int6464#3
# asm 2: pxor  <u=%xmm7,<t=%xmm2
pxor  %xmm7,%xmm2

# qhasm: uint32323232	r += t
# asm 1: paddd <t=int6464#3,<r=int6464#2
# asm 2: paddd <t=%xmm2,<r=%xmm1
paddd %xmm2,%xmm1

# qhasm: 		q ^= r
# asm 1: pxor  <r=int6464#2,<q=int6464#4
# asm 2: pxor  <r=%xmm1,<q=%xmm3
pxor  %xmm1,%xmm3

# qhasm: 		u = q
# asm 1: movdqa <q=int6464#4,>u=int6464#8
# asm 2: movdqa <q=%xmm3,>u=%xmm7
movdqa %xmm3,%xmm7

# qhasm: uint32323232	u >>= 20
# asm 1: psrld $20,<u=int6464#8
# asm 2: psrld $20,<u=%xmm7
psrld $20,%xmm7

# qhasm: uint32323232	q <<= 12
# asm 1: pslld $12,<q=int6464#4
# asm 2: pslld $12,<q=%xmm3
pslld $12,%xmm3

# qhasm: 		q ^= u
# asm 1: pxor  <u=int6464#8,<q=int6464#4
# asm 2: pxor  <u=%xmm7,<q=%xmm3
pxor  %xmm7,%xmm3

# qhasm:                   		mr = z9_stack
# asm 1: movdqa <z9_stack=stack128#28,>mr=int6464#8
# asm 2: movdqa <z9_stack=464(%esp),>mr=%xmm7
movdqa 464(%esp),%xmm7

# qhasm: uint32323232	p += q
# asm 1: paddd <q=int6464#4,<p=int6464#1
# asm 2: paddd <q=%xmm3,<p=%xmm0
paddd %xmm3,%xmm0

# qhasm: 		z0_stack = p
# asm 1: movdqa <p=int6464#1,>z0_stack=stack128#17
# asm 2: movdqa <p=%xmm0,>z0_stack=288(%esp)
movdqa %xmm0,288(%esp)

# qhasm: 		t ^= p
# asm 1: pxor  <p=int6464#1,<t=int6464#3
# asm 2: pxor  <p=%xmm0,<t=%xmm2
pxor  %xmm0,%xmm2

# qhasm: 		u = t
# asm 1: movdqa <t=int6464#3,>u=int6464#1
# asm 2: movdqa <t=%xmm2,>u=%xmm0
movdqa %xmm2,%xmm0

# qhasm: uint32323232	u >>= 24
# asm 1: psrld $24,<u=int6464#1
# asm 2: psrld $24,<u=%xmm0
psrld $24,%xmm0

# qhasm: uint32323232	t <<= 8
# asm 1: pslld $8,<t=int6464#3
# asm 2: pslld $8,<t=%xmm2
pslld $8,%xmm2

# qhasm: 		t ^= u
# asm 1: pxor  <u=int6464#1,<t=int6464#3
# asm 2: pxor  <u=%xmm0,<t=%xmm2
pxor  %xmm0,%xmm2

# qhasm: 		z12_stack = t
# asm 1: movdqa <t=int6464#3,>z12_stack=stack128#24
# asm 2: movdqa <t=%xmm2,>z12_stack=400(%esp)
movdqa %xmm2,400(%esp)

# qhasm: uint32323232	r += t
# asm 1: paddd <t=int6464#3,<r=int6464#2
# asm 2: paddd <t=%xmm2,<r=%xmm1
paddd %xmm2,%xmm1

# qhasm: 		z8_stack = r
# asm 1: movdqa <r=int6464#2,>z8_stack=stack128#26
# asm 2: movdqa <r=%xmm1,>z8_stack=432(%esp)
movdqa %xmm1,432(%esp)

# qhasm: 		q ^= r
# asm 1: pxor  <r=int6464#2,<q=int6464#4
# asm 2: pxor  <r=%xmm1,<q=%xmm3
pxor  %xmm1,%xmm3

# qhasm: 		u = q
# asm 1: movdqa <q=int6464#4,>u=int6464#1
# asm 2: movdqa <q=%xmm3,>u=%xmm0
movdqa %xmm3,%xmm0

# qhasm: uint32323232	u >>= 25
# asm 1: psrld $25,<u=int6464#1
# asm 2: psrld $25,<u=%xmm0
psrld $25,%xmm0

# qhasm: uint32323232	q <<= 7
# asm 1: pslld $7,<q=int6464#4
# asm 2: pslld $7,<q=%xmm3
pslld $7,%xmm3

# qhasm: 		q ^= u
# asm 1: pxor  <u=int6464#1,<q=int6464#4
# asm 2: pxor  <u=%xmm0,<q=%xmm3
pxor  %xmm0,%xmm3

# qhasm: 		z4_stack = q
# asm 1: movdqa <q=int6464#4,>z4_stack=stack128#28
# asm 2: movdqa <q=%xmm3,>z4_stack=464(%esp)
movdqa %xmm3,464(%esp)

# qhasm:                 				p = z2_stack
# asm 1: movdqa <z2_stack=stack128#27,>p=int6464#1
# asm 2: movdqa <z2_stack=448(%esp),>p=%xmm0
movdqa 448(%esp),%xmm0

# qhasm:                 				q = z6_stack
# asm 1: movdqa <z6_stack=stack128#22,>q=int6464#4
# asm 2: movdqa <z6_stack=368(%esp),>q=%xmm3
movdqa 368(%esp),%xmm3

# qhasm:                 				r = z10_stack
# asm 1: movdqa <z10_stack=stack128#18,>r=int6464#2
# asm 2: movdqa <z10_stack=304(%esp),>r=%xmm1
movdqa 304(%esp),%xmm1

# qhasm: uint32323232	  		mp += mq
# asm 1: paddd <mq=int6464#6,<mp=int6464#5
# asm 2: paddd <mq=%xmm5,<mp=%xmm4
paddd %xmm5,%xmm4

# qhasm: 		  		mt ^= mp
# asm 1: pxor  <mp=int6464#5,<mt=int6464#7
# asm 2: pxor  <mp=%xmm4,<mt=%xmm6
pxor  %xmm4,%xmm6

# qhasm: 		  		mu = mt
# asm 1: movdqa <mt=int6464#7,>mu=int6464#3
# asm 2: movdqa <mt=%xmm6,>mu=%xmm2
movdqa %xmm6,%xmm2

# qhasm: uint32323232	  		mu >>= 16
# asm 1: psrld $16,<mu=int6464#3
# asm 2: psrld $16,<mu=%xmm2
psrld $16,%xmm2

# qhasm: uint32323232	  		mt <<= 16
# asm 1: pslld $16,<mt=int6464#7
# asm 2: pslld $16,<mt=%xmm6
pslld $16,%xmm6

# qhasm: 		  		mt ^= mu
# asm 1: pxor  <mu=int6464#3,<mt=int6464#7
# asm 2: pxor  <mu=%xmm2,<mt=%xmm6
pxor  %xmm2,%xmm6

# qhasm: uint32323232	  		mr += mt
# asm 1: paddd <mt=int6464#7,<mr=int6464#8
# asm 2: paddd <mt=%xmm6,<mr=%xmm7
paddd %xmm6,%xmm7

# qhasm: 		  		mq ^= mr
# asm 1: pxor  <mr=int6464#8,<mq=int6464#6
# asm 2: pxor  <mr=%xmm7,<mq=%xmm5
pxor  %xmm7,%xmm5

# qhasm: 		  		mu = mq
# asm 1: movdqa <mq=int6464#6,>mu=int6464#3
# asm 2: movdqa <mq=%xmm5,>mu=%xmm2
movdqa %xmm5,%xmm2

# qhasm: uint32323232	  		mu >>= 20
# asm 1: psrld $20,<mu=int6464#3
# asm 2: psrld $20,<mu=%xmm2
psrld $20,%xmm2

# qhasm: uint32323232	  		mq <<= 12
# asm 1: pslld $12,<mq=int6464#6
# asm 2: pslld $12,<mq=%xmm5
pslld $12,%xmm5

# qhasm: 		  		mq ^= mu
# asm 1: pxor  <mu=int6464#3,<mq=int6464#6
# asm 2: pxor  <mu=%xmm2,<mq=%xmm5
pxor  %xmm2,%xmm5

# qhasm:                 				t = z14_stack
# asm 1: movdqa <z14_stack=stack128#20,>t=int6464#3
# asm 2: movdqa <z14_stack=336(%esp),>t=%xmm2
movdqa 336(%esp),%xmm2

# qhasm: uint32323232	  		mp += mq
# asm 1: paddd <mq=int6464#6,<mp=int6464#5
# asm 2: paddd <mq=%xmm5,<mp=%xmm4
paddd %xmm5,%xmm4

# qhasm: 		  		z1_stack = mp
# asm 1: movdqa <mp=int6464#5,>z1_stack=stack128#18
# asm 2: movdqa <mp=%xmm4,>z1_stack=304(%esp)
movdqa %xmm4,304(%esp)

# qhasm: 		  		mt ^= mp
# asm 1: pxor  <mp=int6464#5,<mt=int6464#7
# asm 2: pxor  <mp=%xmm4,<mt=%xmm6
pxor  %xmm4,%xmm6

# qhasm: 		  		mu = mt
# asm 1: movdqa <mt=int6464#7,>mu=int6464#5
# asm 2: movdqa <mt=%xmm6,>mu=%xmm4
movdqa %xmm6,%xmm4

# qhasm: uint32323232	  		mu >>= 24
# asm 1: psrld $24,<mu=int6464#5
# asm 2: psrld $24,<mu=%xmm4
psrld $24,%xmm4

# qhasm: uint32323232	  		mt <<= 8
# asm 1: pslld $8,<mt=int6464#7
# asm 2: pslld $8,<mt=%xmm6
pslld $8,%xmm6

# qhasm: 		  		mt ^= mu
# asm 1: pxor  <mu=int6464#5,<mt=int6464#7
# asm 2: pxor  <mu=%xmm4,<mt=%xmm6
pxor  %xmm4,%xmm6

# qhasm: 		  		z13_stack = mt
# asm 1: movdqa <mt=int6464#7,>z13_stack=stack128#20
# asm 2: movdqa <mt=%xmm6,>z13_stack=336(%esp)
movdqa %xmm6,336(%esp)

# qhasm: uint32323232	  		mr += mt
# asm 1: paddd <mt=int6464#7,<mr=int6464#8
# asm 2: paddd <mt=%xmm6,<mr=%xmm7
paddd %xmm6,%xmm7

# qhasm: 		  		z9_stack = mr
# asm 1: movdqa <mr=int6464#8,>z9_stack=stack128#27
# asm 2: movdqa <mr=%xmm7,>z9_stack=448(%esp)
movdqa %xmm7,448(%esp)

# qhasm: 		  		mq ^= mr
# asm 1: pxor  <mr=int6464#8,<mq=int6464#6
# asm 2: pxor  <mr=%xmm7,<mq=%xmm5
pxor  %xmm7,%xmm5

# qhasm: 		  		mu = mq
# asm 1: movdqa <mq=int6464#6,>mu=int6464#5
# asm 2: movdqa <mq=%xmm5,>mu=%xmm4
movdqa %xmm5,%xmm4

# qhasm: uint32323232	  		mu >>= 25
# asm 1: psrld $25,<mu=int6464#5
# asm 2: psrld $25,<mu=%xmm4
psrld $25,%xmm4

# qhasm: uint32323232	  		mq <<= 7
# asm 1: pslld $7,<mq=int6464#6
# asm 2: pslld $7,<mq=%xmm5
pslld $7,%xmm5

# qhasm: 		  		mq ^= mu
# asm 1: pxor  <mu=int6464#5,<mq=int6464#6
# asm 2: pxor  <mu=%xmm4,<mq=%xmm5
pxor  %xmm4,%xmm5

# qhasm: 		  		z5_stack = mq
# asm 1: movdqa <mq=int6464#6,>z5_stack=stack128#22
# asm 2: movdqa <mq=%xmm5,>z5_stack=368(%esp)
movdqa %xmm5,368(%esp)

# qhasm: 						assign xmm0 to p

# qhasm: 						assign xmm1 to r

# qhasm: 						assign xmm2 to t

# qhasm: 						assign xmm3 to q

# qhasm:                   						mp = z3_stack
# asm 1: movdqa <z3_stack=stack128#21,>mp=int6464#5
# asm 2: movdqa <z3_stack=352(%esp),>mp=%xmm4
movdqa 352(%esp),%xmm4

# qhasm:                   						mq = z7_stack
# asm 1: movdqa <z7_stack=stack128#25,>mq=int6464#6
# asm 2: movdqa <z7_stack=416(%esp),>mq=%xmm5
movdqa 416(%esp),%xmm5

# qhasm:                   						mt = z15_stack
# asm 1: movdqa <z15_stack=stack128#19,>mt=int6464#7
# asm 2: movdqa <z15_stack=320(%esp),>mt=%xmm6
movdqa 320(%esp),%xmm6

# qhasm: uint32323232					p += q
# asm 1: paddd <q=int6464#4,<p=int6464#1
# asm 2: paddd <q=%xmm3,<p=%xmm0
paddd %xmm3,%xmm0

# qhasm: 						t ^= p
# asm 1: pxor  <p=int6464#1,<t=int6464#3
# asm 2: pxor  <p=%xmm0,<t=%xmm2
pxor  %xmm0,%xmm2

# qhasm: 						u = t
# asm 1: movdqa <t=int6464#3,>u=int6464#8
# asm 2: movdqa <t=%xmm2,>u=%xmm7
movdqa %xmm2,%xmm7

# qhasm: uint32323232					u >>= 16
# asm 1: psrld $16,<u=int6464#8
# asm 2: psrld $16,<u=%xmm7
psrld $16,%xmm7

# qhasm: uint32323232					t <<= 16
# asm 1: pslld $16,<t=int6464#3
# asm 2: pslld $16,<t=%xmm2
pslld $16,%xmm2

# qhasm: 						t ^= u
# asm 1: pxor  <u=int6464#8,<t=int6464#3
# asm 2: pxor  <u=%xmm7,<t=%xmm2
pxor  %xmm7,%xmm2

# qhasm: uint32323232					r += t
# asm 1: paddd <t=int6464#3,<r=int6464#2
# asm 2: paddd <t=%xmm2,<r=%xmm1
paddd %xmm2,%xmm1

# qhasm: 						q ^= r
# asm 1: pxor  <r=int6464#2,<q=int6464#4
# asm 2: pxor  <r=%xmm1,<q=%xmm3
pxor  %xmm1,%xmm3

# qhasm: 						u = q
# asm 1: movdqa <q=int6464#4,>u=int6464#8
# asm 2: movdqa <q=%xmm3,>u=%xmm7
movdqa %xmm3,%xmm7

# qhasm: uint32323232					u >>= 20
# asm 1: psrld $20,<u=int6464#8
# asm 2: psrld $20,<u=%xmm7
psrld $20,%xmm7

# qhasm: uint32323232					q <<= 12
# asm 1: pslld $12,<q=int6464#4
# asm 2: pslld $12,<q=%xmm3
pslld $12,%xmm3

# qhasm: 						q ^= u
# asm 1: pxor  <u=int6464#8,<q=int6464#4
# asm 2: pxor  <u=%xmm7,<q=%xmm3
pxor  %xmm7,%xmm3

# qhasm:                   						mr = z11_stack
# asm 1: movdqa <z11_stack=stack128#23,>mr=int6464#8
# asm 2: movdqa <z11_stack=384(%esp),>mr=%xmm7
movdqa 384(%esp),%xmm7

# qhasm: uint32323232					p += q
# asm 1: paddd <q=int6464#4,<p=int6464#1
# asm 2: paddd <q=%xmm3,<p=%xmm0
paddd %xmm3,%xmm0

# qhasm: 						z2_stack = p
# asm 1: movdqa <p=int6464#1,>z2_stack=stack128#21
# asm 2: movdqa <p=%xmm0,>z2_stack=352(%esp)
movdqa %xmm0,352(%esp)

# qhasm: 						t ^= p
# asm 1: pxor  <p=int6464#1,<t=int6464#3
# asm 2: pxor  <p=%xmm0,<t=%xmm2
pxor  %xmm0,%xmm2

# qhasm: 						u = t
# asm 1: movdqa <t=int6464#3,>u=int6464#1
# asm 2: movdqa <t=%xmm2,>u=%xmm0
movdqa %xmm2,%xmm0

# qhasm: uint32323232					u >>= 24
# asm 1: psrld $24,<u=int6464#1
# asm 2: psrld $24,<u=%xmm0
psrld $24,%xmm0

# qhasm: uint32323232					t <<= 8
# asm 1: pslld $8,<t=int6464#3
# asm 2: pslld $8,<t=%xmm2
pslld $8,%xmm2

# qhasm: 						t ^= u
# asm 1: pxor  <u=int6464#1,<t=int6464#3
# asm 2: pxor  <u=%xmm0,<t=%xmm2
pxor  %xmm0,%xmm2

# qhasm: 						z14_stack = t
# asm 1: movdqa <t=int6464#3,>z14_stack=stack128#25
# asm 2: movdqa <t=%xmm2,>z14_stack=416(%esp)
movdqa %xmm2,416(%esp)

# qhasm: uint32323232					r += t
# asm 1: paddd <t=int6464#3,<r=int6464#2
# asm 2: paddd <t=%xmm2,<r=%xmm1
paddd %xmm2,%xmm1

# qhasm: 						z10_stack = r
# asm 1: movdqa <r=int6464#2,>z10_stack=stack128#19
# asm 2: movdqa <r=%xmm1,>z10_stack=320(%esp)
movdqa %xmm1,320(%esp)

# qhasm: 						q ^= r
# asm 1: pxor  <r=int6464#2,<q=int6464#4
# asm 2: pxor  <r=%xmm1,<q=%xmm3
pxor  %xmm1,%xmm3

# qhasm: 						u = q
# asm 1: movdqa <q=int6464#4,>u=int6464#1
# asm 2: movdqa <q=%xmm3,>u=%xmm0
movdqa %xmm3,%xmm0

# qhasm: uint32323232					u >>= 25
# asm 1: psrld $25,<u=int6464#1
# asm 2: psrld $25,<u=%xmm0
psrld $25,%xmm0

# qhasm: uint32323232					q <<= 7
# asm 1: pslld $7,<q=int6464#4
# asm 2: pslld $7,<q=%xmm3
pslld $7,%xmm3

# qhasm: 						q ^= u
# asm 1: pxor  <u=int6464#1,<q=int6464#4
# asm 2: pxor  <u=%xmm0,<q=%xmm3
pxor  %xmm0,%xmm3

# qhasm: 						z6_stack = q
# asm 1: movdqa <q=int6464#4,>z6_stack=stack128#23
# asm 2: movdqa <q=%xmm3,>z6_stack=384(%esp)
movdqa %xmm3,384(%esp)

# qhasm:                 p = z0_stack
# asm 1: movdqa <z0_stack=stack128#17,>p=int6464#1
# asm 2: movdqa <z0_stack=288(%esp),>p=%xmm0
movdqa 288(%esp),%xmm0

# qhasm:                 q = z5_stack
# asm 1: movdqa <z5_stack=stack128#22,>q=int6464#4
# asm 2: movdqa <z5_stack=368(%esp),>q=%xmm3
movdqa 368(%esp),%xmm3

# qhasm:                 r = z10_stack
# asm 1: movdqa <z10_stack=stack128#19,>r=int6464#2
# asm 2: movdqa <z10_stack=320(%esp),>r=%xmm1
movdqa 320(%esp),%xmm1

# qhasm: uint32323232					  		mp += mq
# asm 1: paddd <mq=int6464#6,<mp=int6464#5
# asm 2: paddd <mq=%xmm5,<mp=%xmm4
paddd %xmm5,%xmm4

# qhasm: 		  						mt ^= mp
# asm 1: pxor  <mp=int6464#5,<mt=int6464#7
# asm 2: pxor  <mp=%xmm4,<mt=%xmm6
pxor  %xmm4,%xmm6

# qhasm: 						  		mu = mt
# asm 1: movdqa <mt=int6464#7,>mu=int6464#3
# asm 2: movdqa <mt=%xmm6,>mu=%xmm2
movdqa %xmm6,%xmm2

# qhasm: uint32323232	  						mu >>= 16
# asm 1: psrld $16,<mu=int6464#3
# asm 2: psrld $16,<mu=%xmm2
psrld $16,%xmm2

# qhasm: uint32323232	  						mt <<= 16
# asm 1: pslld $16,<mt=int6464#7
# asm 2: pslld $16,<mt=%xmm6
pslld $16,%xmm6

# qhasm: 		  						mt ^= mu
# asm 1: pxor  <mu=int6464#3,<mt=int6464#7
# asm 2: pxor  <mu=%xmm2,<mt=%xmm6
pxor  %xmm2,%xmm6

# qhasm: uint32323232	  						mr += mt
# asm 1: paddd <mt=int6464#7,<mr=int6464#8
# asm 2: paddd <mt=%xmm6,<mr=%xmm7
paddd %xmm6,%xmm7

# qhasm: 		  						mq ^= mr
# asm 1: pxor  <mr=int6464#8,<mq=int6464#6
# asm 2: pxor  <mr=%xmm7,<mq=%xmm5
pxor  %xmm7,%xmm5

# qhasm: 		  						mu = mq
# asm 1: movdqa <mq=int6464#6,>mu=int6464#3
# asm 2: movdqa <mq=%xmm5,>mu=%xmm2
movdqa %xmm5,%xmm2

# qhasm: uint32323232	  						mu >>= 20
# asm 1: psrld $20,<mu=int6464#3
# asm 2: psrld $20,<mu=%xmm2
psrld $20,%xmm2

# qhasm: uint32323232	  						mq <<= 12
# asm 1: pslld $12,<mq=int6464#6
# asm 2: pslld $12,<mq=%xmm5
pslld $12,%xmm5

# qhasm: 		  						mq ^= mu
# asm 1: pxor  <mu=int6464#3,<mq=int6464#6
# asm 2: pxor  <mu=%xmm2,<mq=%xmm5
pxor  %xmm2,%xmm5

# qhasm: uint32323232	  						mp += mq
# asm 1: paddd <mq=int6464#6,<mp=int6464#5
# asm 2: paddd <mq=%xmm5,<mp=%xmm4
paddd %xmm5,%xmm4

# qhasm: 		  						z3_stack = mp
# asm 1: movdqa <mp=int6464#5,>z3_stack=stack128#29
# asm 2: movdqa <mp=%xmm4,>z3_stack=480(%esp)
movdqa %xmm4,480(%esp)

# qhasm: 		  						mt ^= mp
# asm 1: pxor  <mp=int6464#5,<mt=int6464#7
# asm 2: pxor  <mp=%xmm4,<mt=%xmm6
pxor  %xmm4,%xmm6

# qhasm: 		  						mu = mt
# asm 1: movdqa <mt=int6464#7,>mu=int6464#3
# asm 2: movdqa <mt=%xmm6,>mu=%xmm2
movdqa %xmm6,%xmm2

# qhasm: uint32323232	  						mu >>= 24
# asm 1: psrld $24,<mu=int6464#3
# asm 2: psrld $24,<mu=%xmm2
psrld $24,%xmm2

# qhasm: uint32323232	  						mt <<= 8
# asm 1: pslld $8,<mt=int6464#7
# asm 2: pslld $8,<mt=%xmm6
pslld $8,%xmm6

# qhasm: 		  						mt ^= mu
# asm 1: pxor  <mu=int6464#3,<mt=int6464#7
# asm 2: pxor  <mu=%xmm2,<mt=%xmm6
pxor  %xmm2,%xmm6

# qhasm: 		  						z15_stack = mt
# asm 1: movdqa <mt=int6464#7,>z15_stack=stack128#30
# asm 2: movdqa <mt=%xmm6,>z15_stack=496(%esp)
movdqa %xmm6,496(%esp)

# qhasm:                 t = mt
# asm 1: movdqa <mt=int6464#7,>t=int6464#3
# asm 2: movdqa <mt=%xmm6,>t=%xmm2
movdqa %xmm6,%xmm2

# qhasm: uint32323232	  						mr += mt
# asm 1: paddd <mt=int6464#7,<mr=int6464#8
# asm 2: paddd <mt=%xmm6,<mr=%xmm7
paddd %xmm6,%xmm7

# qhasm: 		  						z11_stack = mr
# asm 1: movdqa <mr=int6464#8,>z11_stack=stack128#17
# asm 2: movdqa <mr=%xmm7,>z11_stack=288(%esp)
movdqa %xmm7,288(%esp)

# qhasm: 		  						mq ^= mr
# asm 1: pxor  <mr=int6464#8,<mq=int6464#6
# asm 2: pxor  <mr=%xmm7,<mq=%xmm5
pxor  %xmm7,%xmm5

# qhasm: 		  						mu = mq
# asm 1: movdqa <mq=int6464#6,>mu=int6464#5
# asm 2: movdqa <mq=%xmm5,>mu=%xmm4
movdqa %xmm5,%xmm4

# qhasm: uint32323232	  						mu >>= 25
# asm 1: psrld $25,<mu=int6464#5
# asm 2: psrld $25,<mu=%xmm4
psrld $25,%xmm4

# qhasm: uint32323232	  						mq <<= 7
# asm 1: pslld $7,<mq=int6464#6
# asm 2: pslld $7,<mq=%xmm5
pslld $7,%xmm5

# qhasm: 		  						mq ^= mu
# asm 1: pxor  <mu=int6464#5,<mq=int6464#6
# asm 2: pxor  <mu=%xmm4,<mq=%xmm5
pxor  %xmm4,%xmm5

# qhasm: 		  						z7_stack = mq
# asm 1: movdqa <mq=int6464#6,>z7_stack=stack128#22
# asm 2: movdqa <mq=%xmm5,>z7_stack=368(%esp)
movdqa %xmm5,368(%esp)

# qhasm: 		assign xmm0 to p

# qhasm: 		assign xmm1 to r

# qhasm: 		assign xmm2 to t

# qhasm: 		assign xmm3 to q

# qhasm:                   		mp = z1_stack
# asm 1: movdqa <z1_stack=stack128#18,>mp=int6464#5
# asm 2: movdqa <z1_stack=304(%esp),>mp=%xmm4
movdqa 304(%esp),%xmm4

# qhasm:                   		mq = z6_stack
# asm 1: movdqa <z6_stack=stack128#23,>mq=int6464#6
# asm 2: movdqa <z6_stack=384(%esp),>mq=%xmm5
movdqa 384(%esp),%xmm5

# qhasm:                   		mt = z12_stack
# asm 1: movdqa <z12_stack=stack128#24,>mt=int6464#7
# asm 2: movdqa <z12_stack=400(%esp),>mt=%xmm6
movdqa 400(%esp),%xmm6

# qhasm: uint32323232	p += q
# asm 1: paddd <q=int6464#4,<p=int6464#1
# asm 2: paddd <q=%xmm3,<p=%xmm0
paddd %xmm3,%xmm0

# qhasm: 		t ^= p
# asm 1: pxor  <p=int6464#1,<t=int6464#3
# asm 2: pxor  <p=%xmm0,<t=%xmm2
pxor  %xmm0,%xmm2

# qhasm: 		u = t
# asm 1: movdqa <t=int6464#3,>u=int6464#8
# asm 2: movdqa <t=%xmm2,>u=%xmm7
movdqa %xmm2,%xmm7

# qhasm: uint32323232	u >>= 16
# asm 1: psrld $16,<u=int6464#8
# asm 2: psrld $16,<u=%xmm7
psrld $16,%xmm7

# qhasm: uint32323232	t <<= 16
# asm 1: pslld $16,<t=int6464#3
# asm 2: pslld $16,<t=%xmm2
pslld $16,%xmm2

# qhasm: 		t ^= u
# asm 1: pxor  <u=int6464#8,<t=int6464#3
# asm 2: pxor  <u=%xmm7,<t=%xmm2
pxor  %xmm7,%xmm2

# qhasm: uint32323232	r += t
# asm 1: paddd <t=int6464#3,<r=int6464#2
# asm 2: paddd <t=%xmm2,<r=%xmm1
paddd %xmm2,%xmm1

# qhasm: 		q ^= r
# asm 1: pxor  <r=int6464#2,<q=int6464#4
# asm 2: pxor  <r=%xmm1,<q=%xmm3
pxor  %xmm1,%xmm3

# qhasm: 		u = q
# asm 1: movdqa <q=int6464#4,>u=int6464#8
# asm 2: movdqa <q=%xmm3,>u=%xmm7
movdqa %xmm3,%xmm7

# qhasm: uint32323232	u >>= 20
# asm 1: psrld $20,<u=int6464#8
# asm 2: psrld $20,<u=%xmm7
psrld $20,%xmm7

# qhasm: uint32323232	q <<= 12
# asm 1: pslld $12,<q=int6464#4
# asm 2: pslld $12,<q=%xmm3
pslld $12,%xmm3

# qhasm: 		q ^= u
# asm 1: pxor  <u=int6464#8,<q=int6464#4
# asm 2: pxor  <u=%xmm7,<q=%xmm3
pxor  %xmm7,%xmm3

# qhasm:                   		mr = z11_stack
# asm 1: movdqa <z11_stack=stack128#17,>mr=int6464#8
# asm 2: movdqa <z11_stack=288(%esp),>mr=%xmm7
movdqa 288(%esp),%xmm7

# qhasm: uint32323232	p += q
# asm 1: paddd <q=int6464#4,<p=int6464#1
# asm 2: paddd <q=%xmm3,<p=%xmm0
paddd %xmm3,%xmm0

# qhasm: 		z0_stack = p
# asm 1: movdqa <p=int6464#1,>z0_stack=stack128#31
# asm 2: movdqa <p=%xmm0,>z0_stack=512(%esp)
movdqa %xmm0,512(%esp)

# qhasm: 		t ^= p
# asm 1: pxor  <p=int6464#1,<t=int6464#3
# asm 2: pxor  <p=%xmm0,<t=%xmm2
pxor  %xmm0,%xmm2

# qhasm: 		u = t
# asm 1: movdqa <t=int6464#3,>u=int6464#1
# asm 2: movdqa <t=%xmm2,>u=%xmm0
movdqa %xmm2,%xmm0

# qhasm: uint32323232	u >>= 24
# asm 1: psrld $24,<u=int6464#1
# asm 2: psrld $24,<u=%xmm0
psrld $24,%xmm0

# qhasm: uint32323232	t <<= 8
# asm 1: pslld $8,<t=int6464#3
# asm 2: pslld $8,<t=%xmm2
pslld $8,%xmm2

# qhasm: 		t ^= u
# asm 1: pxor  <u=int6464#1,<t=int6464#3
# asm 2: pxor  <u=%xmm0,<t=%xmm2
pxor  %xmm0,%xmm2

# qhasm: 		z15_stack = t
# asm 1: movdqa <t=int6464#3,>z15_stack=stack128#19
# asm 2: movdqa <t=%xmm2,>z15_stack=320(%esp)
movdqa %xmm2,320(%esp)

# qhasm: uint32323232	r += t
# asm 1: paddd <t=int6464#3,<r=int6464#2
# asm 2: paddd <t=%xmm2,<r=%xmm1
paddd %xmm2,%xmm1

# qhasm: 		z10_stack = r
# asm 1: movdqa <r=int6464#2,>z10_stack=stack128#18
# asm 2: movdqa <r=%xmm1,>z10_stack=304(%esp)
movdqa %xmm1,304(%esp)

# qhasm: 		q ^= r
# asm 1: pxor  <r=int6464#2,<q=int6464#4
# asm 2: pxor  <r=%xmm1,<q=%xmm3
pxor  %xmm1,%xmm3

# qhasm: 		u = q
# asm 1: movdqa <q=int6464#4,>u=int6464#1
# asm 2: movdqa <q=%xmm3,>u=%xmm0
movdqa %xmm3,%xmm0

# qhasm: uint32323232	u >>= 25
# asm 1: psrld $25,<u=int6464#1
# asm 2: psrld $25,<u=%xmm0
psrld $25,%xmm0

# qhasm: uint32323232	q <<= 7
# asm 1: pslld $7,<q=int6464#4
# asm 2: pslld $7,<q=%xmm3
pslld $7,%xmm3

# qhasm: 		q ^= u
# asm 1: pxor  <u=int6464#1,<q=int6464#4
# asm 2: pxor  <u=%xmm0,<q=%xmm3
pxor  %xmm0,%xmm3

# qhasm: 		z5_stack = q
# asm 1: movdqa <q=int6464#4,>z5_stack=stack128#17
# asm 2: movdqa <q=%xmm3,>z5_stack=288(%esp)
movdqa %xmm3,288(%esp)

# qhasm:                 				p = z2_stack
# asm 1: movdqa <z2_stack=stack128#21,>p=int6464#1
# asm 2: movdqa <z2_stack=352(%esp),>p=%xmm0
movdqa 352(%esp),%xmm0

# qhasm:                 				q = z7_stack
# asm 1: movdqa <z7_stack=stack128#22,>q=int6464#4
# asm 2: movdqa <z7_stack=368(%esp),>q=%xmm3
movdqa 368(%esp),%xmm3

# qhasm:                 				r = z8_stack
# asm 1: movdqa <z8_stack=stack128#26,>r=int6464#2
# asm 2: movdqa <z8_stack=432(%esp),>r=%xmm1
movdqa 432(%esp),%xmm1

# qhasm: uint32323232	  		mp += mq
# asm 1: paddd <mq=int6464#6,<mp=int6464#5
# asm 2: paddd <mq=%xmm5,<mp=%xmm4
paddd %xmm5,%xmm4

# qhasm: 		  		mt ^= mp
# asm 1: pxor  <mp=int6464#5,<mt=int6464#7
# asm 2: pxor  <mp=%xmm4,<mt=%xmm6
pxor  %xmm4,%xmm6

# qhasm: 		  		mu = mt
# asm 1: movdqa <mt=int6464#7,>mu=int6464#3
# asm 2: movdqa <mt=%xmm6,>mu=%xmm2
movdqa %xmm6,%xmm2

# qhasm: uint32323232	  		mu >>= 16
# asm 1: psrld $16,<mu=int6464#3
# asm 2: psrld $16,<mu=%xmm2
psrld $16,%xmm2

# qhasm: uint32323232	  		mt <<= 16
# asm 1: pslld $16,<mt=int6464#7
# asm 2: pslld $16,<mt=%xmm6
pslld $16,%xmm6

# qhasm: 		  		mt ^= mu
# asm 1: pxor  <mu=int6464#3,<mt=int6464#7
# asm 2: pxor  <mu=%xmm2,<mt=%xmm6
pxor  %xmm2,%xmm6

# qhasm: uint32323232	  		mr += mt
# asm 1: paddd <mt=int6464#7,<mr=int6464#8
# asm 2: paddd <mt=%xmm6,<mr=%xmm7
paddd %xmm6,%xmm7

# qhasm: 		  		mq ^= mr
# asm 1: pxor  <mr=int6464#8,<mq=int6464#6
# asm 2: pxor  <mr=%xmm7,<mq=%xmm5
pxor  %xmm7,%xmm5

# qhasm: 		  		mu = mq
# asm 1: movdqa <mq=int6464#6,>mu=int6464#3
# asm 2: movdqa <mq=%xmm5,>mu=%xmm2
movdqa %xmm5,%xmm2

# qhasm: uint32323232	  		mu >>= 20
# asm 1: psrld $20,<mu=int6464#3
# asm 2: psrld $20,<mu=%xmm2
psrld $20,%xmm2

# qhasm: uint32323232	  		mq <<= 12
# asm 1: pslld $12,<mq=int6464#6
# asm 2: pslld $12,<mq=%xmm5
pslld $12,%xmm5

# qhasm: 		  		mq ^= mu
# asm 1: pxor  <mu=int6464#3,<mq=int6464#6
# asm 2: pxor  <mu=%xmm2,<mq=%xmm5
pxor  %xmm2,%xmm5

# qhasm:                 				t = z13_stack
# asm 1: movdqa <z13_stack=stack128#20,>t=int6464#3
# asm 2: movdqa <z13_stack=336(%esp),>t=%xmm2
movdqa 336(%esp),%xmm2

# qhasm: uint32323232	  		mp += mq
# asm 1: paddd <mq=int6464#6,<mp=int6464#5
# asm 2: paddd <mq=%xmm5,<mp=%xmm4
paddd %xmm5,%xmm4

# qhasm: 		  		z1_stack = mp
# asm 1: movdqa <mp=int6464#5,>z1_stack=stack128#24
# asm 2: movdqa <mp=%xmm4,>z1_stack=400(%esp)
movdqa %xmm4,400(%esp)

# qhasm: 		  		mt ^= mp
# asm 1: pxor  <mp=int6464#5,<mt=int6464#7
# asm 2: pxor  <mp=%xmm4,<mt=%xmm6
pxor  %xmm4,%xmm6

# qhasm: 		  		mu = mt
# asm 1: movdqa <mt=int6464#7,>mu=int6464#5
# asm 2: movdqa <mt=%xmm6,>mu=%xmm4
movdqa %xmm6,%xmm4

# qhasm: uint32323232	  		mu >>= 24
# asm 1: psrld $24,<mu=int6464#5
# asm 2: psrld $24,<mu=%xmm4
psrld $24,%xmm4

# qhasm: uint32323232	  		mt <<= 8
# asm 1: pslld $8,<mt=int6464#7
# asm 2: pslld $8,<mt=%xmm6
pslld $8,%xmm6

# qhasm: 		  		mt ^= mu
# asm 1: pxor  <mu=int6464#5,<mt=int6464#7
# asm 2: pxor  <mu=%xmm4,<mt=%xmm6
pxor  %xmm4,%xmm6

# qhasm: 		  		z12_stack = mt
# asm 1: movdqa <mt=int6464#7,>z12_stack=stack128#32
# asm 2: movdqa <mt=%xmm6,>z12_stack=528(%esp)
movdqa %xmm6,528(%esp)

# qhasm: uint32323232	  		mr += mt
# asm 1: paddd <mt=int6464#7,<mr=int6464#8
# asm 2: paddd <mt=%xmm6,<mr=%xmm7
paddd %xmm6,%xmm7

# qhasm: 		  		z11_stack = mr
# asm 1: movdqa <mr=int6464#8,>z11_stack=stack128#23
# asm 2: movdqa <mr=%xmm7,>z11_stack=384(%esp)
movdqa %xmm7,384(%esp)

# qhasm: 		  		mq ^= mr
# asm 1: pxor  <mr=int6464#8,<mq=int6464#6
# asm 2: pxor  <mr=%xmm7,<mq=%xmm5
pxor  %xmm7,%xmm5

# qhasm: 		  		mu = mq
# asm 1: movdqa <mq=int6464#6,>mu=int6464#5
# asm 2: movdqa <mq=%xmm5,>mu=%xmm4
movdqa %xmm5,%xmm4

# qhasm: uint32323232	  		mu >>= 25
# asm 1: psrld $25,<mu=int6464#5
# asm 2: psrld $25,<mu=%xmm4
psrld $25,%xmm4

# qhasm: uint32323232	  		mq <<= 7
# asm 1: pslld $7,<mq=int6464#6
# asm 2: pslld $7,<mq=%xmm5
pslld $7,%xmm5

# qhasm: 		  		mq ^= mu
# asm 1: pxor  <mu=int6464#5,<mq=int6464#6
# asm 2: pxor  <mu=%xmm4,<mq=%xmm5
pxor  %xmm4,%xmm5

# qhasm: 		  		z6_stack = mq
# asm 1: movdqa <mq=int6464#6,>z6_stack=stack128#22
# asm 2: movdqa <mq=%xmm5,>z6_stack=368(%esp)
movdqa %xmm5,368(%esp)

# qhasm:                   						mp = z3_stack
# asm 1: movdqa <z3_stack=stack128#29,>mp=int6464#5
# asm 2: movdqa <z3_stack=480(%esp),>mp=%xmm4
movdqa 480(%esp),%xmm4

# qhasm:                   						mq = z4_stack
# asm 1: movdqa <z4_stack=stack128#28,>mq=int6464#6
# asm 2: movdqa <z4_stack=464(%esp),>mq=%xmm5
movdqa 464(%esp),%xmm5

# qhasm:                   						mt = z14_stack
# asm 1: movdqa <z14_stack=stack128#25,>mt=int6464#7
# asm 2: movdqa <z14_stack=416(%esp),>mt=%xmm6
movdqa 416(%esp),%xmm6

# qhasm: 						assign xmm0 to p

# qhasm: 						assign xmm1 to r

# qhasm: 						assign xmm2 to t

# qhasm: 						assign xmm3 to q

# qhasm: uint32323232					p += q
# asm 1: paddd <q=int6464#4,<p=int6464#1
# asm 2: paddd <q=%xmm3,<p=%xmm0
paddd %xmm3,%xmm0

# qhasm: 						t ^= p
# asm 1: pxor  <p=int6464#1,<t=int6464#3
# asm 2: pxor  <p=%xmm0,<t=%xmm2
pxor  %xmm0,%xmm2

# qhasm: 						u = t
# asm 1: movdqa <t=int6464#3,>u=int6464#8
# asm 2: movdqa <t=%xmm2,>u=%xmm7
movdqa %xmm2,%xmm7

# qhasm: uint32323232					u >>= 16
# asm 1: psrld $16,<u=int6464#8
# asm 2: psrld $16,<u=%xmm7
psrld $16,%xmm7

# qhasm: uint32323232					t <<= 16
# asm 1: pslld $16,<t=int6464#3
# asm 2: pslld $16,<t=%xmm2
pslld $16,%xmm2

# qhasm: 						t ^= u
# asm 1: pxor  <u=int6464#8,<t=int6464#3
# asm 2: pxor  <u=%xmm7,<t=%xmm2
pxor  %xmm7,%xmm2

# qhasm: uint32323232					r += t
# asm 1: paddd <t=int6464#3,<r=int6464#2
# asm 2: paddd <t=%xmm2,<r=%xmm1
paddd %xmm2,%xmm1

# qhasm: 						q ^= r
# asm 1: pxor  <r=int6464#2,<q=int6464#4
# asm 2: pxor  <r=%xmm1,<q=%xmm3
pxor  %xmm1,%xmm3

# qhasm: 						u = q
# asm 1: movdqa <q=int6464#4,>u=int6464#8
# asm 2: movdqa <q=%xmm3,>u=%xmm7
movdqa %xmm3,%xmm7

# qhasm: uint32323232					u >>= 20
# asm 1: psrld $20,<u=int6464#8
# asm 2: psrld $20,<u=%xmm7
psrld $20,%xmm7

# qhasm: uint32323232					q <<= 12
# asm 1: pslld $12,<q=int6464#4
# asm 2: pslld $12,<q=%xmm3
pslld $12,%xmm3

# qhasm: 						q ^= u
# asm 1: pxor  <u=int6464#8,<q=int6464#4
# asm 2: pxor  <u=%xmm7,<q=%xmm3
pxor  %xmm7,%xmm3

# qhasm:                   						mr = z9_stack
# asm 1: movdqa <z9_stack=stack128#27,>mr=int6464#8
# asm 2: movdqa <z9_stack=448(%esp),>mr=%xmm7
movdqa 448(%esp),%xmm7

# qhasm: uint32323232					p += q
# asm 1: paddd <q=int6464#4,<p=int6464#1
# asm 2: paddd <q=%xmm3,<p=%xmm0
paddd %xmm3,%xmm0

# qhasm: 						z2_stack = p
# asm 1: movdqa <p=int6464#1,>z2_stack=stack128#27
# asm 2: movdqa <p=%xmm0,>z2_stack=448(%esp)
movdqa %xmm0,448(%esp)

# qhasm: 						t ^= p
# asm 1: pxor  <p=int6464#1,<t=int6464#3
# asm 2: pxor  <p=%xmm0,<t=%xmm2
pxor  %xmm0,%xmm2

# qhasm: 						u = t
# asm 1: movdqa <t=int6464#3,>u=int6464#1
# asm 2: movdqa <t=%xmm2,>u=%xmm0
movdqa %xmm2,%xmm0

# qhasm: uint32323232					u >>= 24
# asm 1: psrld $24,<u=int6464#1
# asm 2: psrld $24,<u=%xmm0
psrld $24,%xmm0

# qhasm: uint32323232					t <<= 8
# asm 1: pslld $8,<t=int6464#3
# asm 2: pslld $8,<t=%xmm2
pslld $8,%xmm2

# qhasm: 						t ^= u
# asm 1: pxor  <u=int6464#1,<t=int6464#3
# asm 2: pxor  <u=%xmm0,<t=%xmm2
pxor  %xmm0,%xmm2

# qhasm: 						z13_stack = t
# asm 1: movdqa <t=int6464#3,>z13_stack=stack128#26
# asm 2: movdqa <t=%xmm2,>z13_stack=432(%esp)
movdqa %xmm2,432(%esp)

# qhasm: uint32323232					r += t
# asm 1: paddd <t=int6464#3,<r=int6464#2
# asm 2: paddd <t=%xmm2,<r=%xmm1
paddd %xmm2,%xmm1

# qhasm: 						z8_stack = r
# asm 1: movdqa <r=int6464#2,>z8_stack=stack128#29
# asm 2: movdqa <r=%xmm1,>z8_stack=480(%esp)
movdqa %xmm1,480(%esp)

# qhasm: 						q ^= r
# asm 1: pxor  <r=int6464#2,<q=int6464#4
# asm 2: pxor  <r=%xmm1,<q=%xmm3
pxor  %xmm1,%xmm3

# qhasm: 						u = q
# asm 1: movdqa <q=int6464#4,>u=int6464#1
# asm 2: movdqa <q=%xmm3,>u=%xmm0
movdqa %xmm3,%xmm0

# qhasm: uint32323232					u >>= 25
# asm 1: psrld $25,<u=int6464#1
# asm 2: psrld $25,<u=%xmm0
psrld $25,%xmm0

# qhasm: uint32323232					q <<= 7
# asm 1: pslld $7,<q=int6464#4
# asm 2: pslld $7,<q=%xmm3
pslld $7,%xmm3

# qhasm: 						q ^= u
# asm 1: pxor  <u=int6464#1,<q=int6464#4
# asm 2: pxor  <u=%xmm0,<q=%xmm3
pxor  %xmm0,%xmm3

# qhasm: 						z7_stack = q
# asm 1: movdqa <q=int6464#4,>z7_stack=stack128#25
# asm 2: movdqa <q=%xmm3,>z7_stack=416(%esp)
movdqa %xmm3,416(%esp)

# qhasm:                 p = z0_stack
# asm 1: movdqa <z0_stack=stack128#31,>p=int6464#1
# asm 2: movdqa <z0_stack=512(%esp),>p=%xmm0
movdqa 512(%esp),%xmm0

# qhasm:                 r = z8_stack
# asm 1: movdqa <z8_stack=stack128#29,>r=int6464#2
# asm 2: movdqa <z8_stack=480(%esp),>r=%xmm1
movdqa 480(%esp),%xmm1

# qhasm:                 t = z12_stack
# asm 1: movdqa <z12_stack=stack128#32,>t=int6464#3
# asm 2: movdqa <z12_stack=528(%esp),>t=%xmm2
movdqa 528(%esp),%xmm2

# qhasm: uint32323232					  		mp += mq
# asm 1: paddd <mq=int6464#6,<mp=int6464#5
# asm 2: paddd <mq=%xmm5,<mp=%xmm4
paddd %xmm5,%xmm4

# qhasm: 		  						mt ^= mp
# asm 1: pxor  <mp=int6464#5,<mt=int6464#7
# asm 2: pxor  <mp=%xmm4,<mt=%xmm6
pxor  %xmm4,%xmm6

# qhasm: 						  		mu = mt
# asm 1: movdqa <mt=int6464#7,>mu=int6464#4
# asm 2: movdqa <mt=%xmm6,>mu=%xmm3
movdqa %xmm6,%xmm3

# qhasm: uint32323232	  						mu >>= 16
# asm 1: psrld $16,<mu=int6464#4
# asm 2: psrld $16,<mu=%xmm3
psrld $16,%xmm3

# qhasm: uint32323232	  						mt <<= 16
# asm 1: pslld $16,<mt=int6464#7
# asm 2: pslld $16,<mt=%xmm6
pslld $16,%xmm6

# qhasm: 		  						mt ^= mu
# asm 1: pxor  <mu=int6464#4,<mt=int6464#7
# asm 2: pxor  <mu=%xmm3,<mt=%xmm6
pxor  %xmm3,%xmm6

# qhasm: uint32323232	  						mr += mt
# asm 1: paddd <mt=int6464#7,<mr=int6464#8
# asm 2: paddd <mt=%xmm6,<mr=%xmm7
paddd %xmm6,%xmm7

# qhasm: 		  						mq ^= mr
# asm 1: pxor  <mr=int6464#8,<mq=int6464#6
# asm 2: pxor  <mr=%xmm7,<mq=%xmm5
pxor  %xmm7,%xmm5

# qhasm: 		  						mu = mq
# asm 1: movdqa <mq=int6464#6,>mu=int6464#4
# asm 2: movdqa <mq=%xmm5,>mu=%xmm3
movdqa %xmm5,%xmm3

# qhasm: uint32323232	  						mu >>= 20
# asm 1: psrld $20,<mu=int6464#4
# asm 2: psrld $20,<mu=%xmm3
psrld $20,%xmm3

# qhasm: uint32323232	  						mq <<= 12
# asm 1: pslld $12,<mq=int6464#6
# asm 2: pslld $12,<mq=%xmm5
pslld $12,%xmm5

# qhasm: 		  						mq ^= mu
# asm 1: pxor  <mu=int6464#4,<mq=int6464#6
# asm 2: pxor  <mu=%xmm3,<mq=%xmm5
pxor  %xmm3,%xmm5

# qhasm: uint32323232	  						mp += mq
# asm 1: paddd <mq=int6464#6,<mp=int6464#5
# asm 2: paddd <mq=%xmm5,<mp=%xmm4
paddd %xmm5,%xmm4

# qhasm: 		  						z3_stack = mp
# asm 1: movdqa <mp=int6464#5,>z3_stack=stack128#21
# asm 2: movdqa <mp=%xmm4,>z3_stack=352(%esp)
movdqa %xmm4,352(%esp)

# qhasm: 		  						mt ^= mp
# asm 1: pxor  <mp=int6464#5,<mt=int6464#7
# asm 2: pxor  <mp=%xmm4,<mt=%xmm6
pxor  %xmm4,%xmm6

# qhasm: 		  						mu = mt
# asm 1: movdqa <mt=int6464#7,>mu=int6464#4
# asm 2: movdqa <mt=%xmm6,>mu=%xmm3
movdqa %xmm6,%xmm3

# qhasm: uint32323232	  						mu >>= 24
# asm 1: psrld $24,<mu=int6464#4
# asm 2: psrld $24,<mu=%xmm3
psrld $24,%xmm3

# qhasm: uint32323232	  						mt <<= 8
# asm 1: pslld $8,<mt=int6464#7
# asm 2: pslld $8,<mt=%xmm6
pslld $8,%xmm6

# qhasm: 		  						mt ^= mu
# asm 1: pxor  <mu=int6464#4,<mt=int6464#7
# asm 2: pxor  <mu=%xmm3,<mt=%xmm6
pxor  %xmm3,%xmm6

# qhasm: 		  						z14_stack = mt
# asm 1: movdqa <mt=int6464#7,>z14_stack=stack128#20
# asm 2: movdqa <mt=%xmm6,>z14_stack=336(%esp)
movdqa %xmm6,336(%esp)

# qhasm: uint32323232	  						mr += mt
# asm 1: paddd <mt=int6464#7,<mr=int6464#8
# asm 2: paddd <mt=%xmm6,<mr=%xmm7
paddd %xmm6,%xmm7

# qhasm: 		  						z9_stack = mr
# asm 1: movdqa <mr=int6464#8,>z9_stack=stack128#28
# asm 2: movdqa <mr=%xmm7,>z9_stack=464(%esp)
movdqa %xmm7,464(%esp)

# qhasm: 		  						mq ^= mr
# asm 1: pxor  <mr=int6464#8,<mq=int6464#6
# asm 2: pxor  <mr=%xmm7,<mq=%xmm5
pxor  %xmm7,%xmm5

# qhasm: 		  						mu = mq
# asm 1: movdqa <mq=int6464#6,>mu=int6464#4
# asm 2: movdqa <mq=%xmm5,>mu=%xmm3
movdqa %xmm5,%xmm3

# qhasm: uint32323232	  						mu >>= 25
# asm 1: psrld $25,<mu=int6464#4
# asm 2: psrld $25,<mu=%xmm3
psrld $25,%xmm3

# qhasm: uint32323232	  						mq <<= 7
# asm 1: pslld $7,<mq=int6464#6
# asm 2: pslld $7,<mq=%xmm5
pslld $7,%xmm5

# qhasm: 		  						mq ^= mu
# asm 1: pxor  <mu=int6464#4,<mq=int6464#6
# asm 2: pxor  <mu=%xmm3,<mq=%xmm5
pxor  %xmm3,%xmm5

# qhasm: 		  						z4_stack = mq
# asm 1: movdqa <mq=int6464#6,>z4_stack=stack128#33
# asm 2: movdqa <mq=%xmm5,>z4_stack=544(%esp)
movdqa %xmm5,544(%esp)

# qhasm:                 q = mq
# asm 1: movdqa <mq=int6464#6,>q=int6464#4
# asm 2: movdqa <mq=%xmm5,>q=%xmm3
movdqa %xmm5,%xmm3

# qhasm:                   unsigned>? i -= 2
# asm 1: sub  $2,<i=int32#1
# asm 2: sub  $2,<i=%eax
sub  $2,%eax
# comment:fp stack unchanged by jump

# qhasm: goto mainloop1 if unsigned>
ja ._mainloop1

# qhasm:   z0 = z0_stack
# asm 1: movdqa <z0_stack=stack128#31,>z0=int6464#1
# asm 2: movdqa <z0_stack=512(%esp),>z0=%xmm0
movdqa 512(%esp),%xmm0

# qhasm:   z1 = z1_stack
# asm 1: movdqa <z1_stack=stack128#24,>z1=int6464#2
# asm 2: movdqa <z1_stack=400(%esp),>z1=%xmm1
movdqa 400(%esp),%xmm1

# qhasm:   z2 = z2_stack
# asm 1: movdqa <z2_stack=stack128#27,>z2=int6464#3
# asm 2: movdqa <z2_stack=448(%esp),>z2=%xmm2
movdqa 448(%esp),%xmm2

# qhasm:   z3 = z3_stack
# asm 1: movdqa <z3_stack=stack128#21,>z3=int6464#4
# asm 2: movdqa <z3_stack=352(%esp),>z3=%xmm3
movdqa 352(%esp),%xmm3

# qhasm:   uint32323232 z0 += orig0
# asm 1: paddd <orig0=stack128#1,<z0=int6464#1
# asm 2: paddd <orig0=32(%esp),<z0=%xmm0
paddd 32(%esp),%xmm0

# qhasm:   uint32323232 z1 += orig1
# asm 1: paddd <orig1=stack128#2,<z1=int6464#2
# asm 2: paddd <orig1=48(%esp),<z1=%xmm1
paddd 48(%esp),%xmm1

# qhasm:   uint32323232 z2 += orig2
# asm 1: paddd <orig2=stack128#3,<z2=int6464#3
# asm 2: paddd <orig2=64(%esp),<z2=%xmm2
paddd 64(%esp),%xmm2

# qhasm:   uint32323232 z3 += orig3
# asm 1: paddd <orig3=stack128#4,<z3=int6464#4
# asm 2: paddd <orig3=80(%esp),<z3=%xmm3
paddd 80(%esp),%xmm3

# qhasm:   in0 = z0
# asm 1: movd   <z0=int6464#1,>in0=int32#1
# asm 2: movd   <z0=%xmm0,>in0=%eax
movd   %xmm0,%eax

# qhasm:   in1 = z1
# asm 1: movd   <z1=int6464#2,>in1=int32#2
# asm 2: movd   <z1=%xmm1,>in1=%ecx
movd   %xmm1,%ecx

# qhasm:   in2 = z2
# asm 1: movd   <z2=int6464#3,>in2=int32#4
# asm 2: movd   <z2=%xmm2,>in2=%ebx
movd   %xmm2,%ebx

# qhasm:   in3 = z3
# asm 1: movd   <z3=int6464#4,>in3=int32#7
# asm 2: movd   <z3=%xmm3,>in3=%ebp
movd   %xmm3,%ebp

# qhasm:   z0 <<<= 96
# asm 1: pshufd $0x39,<z0=int6464#1,<z0=int6464#1
# asm 2: pshufd $0x39,<z0=%xmm0,<z0=%xmm0
pshufd $0x39,%xmm0,%xmm0

# qhasm:   z1 <<<= 96
# asm 1: pshufd $0x39,<z1=int6464#2,<z1=int6464#2
# asm 2: pshufd $0x39,<z1=%xmm1,<z1=%xmm1
pshufd $0x39,%xmm1,%xmm1

# qhasm:   z2 <<<= 96
# asm 1: pshufd $0x39,<z2=int6464#3,<z2=int6464#3
# asm 2: pshufd $0x39,<z2=%xmm2,<z2=%xmm2
pshufd $0x39,%xmm2,%xmm2

# qhasm:   z3 <<<= 96
# asm 1: pshufd $0x39,<z3=int6464#4,<z3=int6464#4
# asm 2: pshufd $0x39,<z3=%xmm3,<z3=%xmm3
pshufd $0x39,%xmm3,%xmm3

# qhasm:   in0 ^= *(uint32 *) (m + 0)
# asm 1: xorl 0(<m=int32#5),<in0=int32#1
# asm 2: xorl 0(<m=%esi),<in0=%eax
xorl 0(%esi),%eax

# qhasm:   in1 ^= *(uint32 *) (m + 4)
# asm 1: xorl 4(<m=int32#5),<in1=int32#2
# asm 2: xorl 4(<m=%esi),<in1=%ecx
xorl 4(%esi),%ecx

# qhasm:   in2 ^= *(uint32 *) (m + 8)
# asm 1: xorl 8(<m=int32#5),<in2=int32#4
# asm 2: xorl 8(<m=%esi),<in2=%ebx
xorl 8(%esi),%ebx

# qhasm:   in3 ^= *(uint32 *) (m + 12)
# asm 1: xorl 12(<m=int32#5),<in3=int32#7
# asm 2: xorl 12(<m=%esi),<in3=%ebp
xorl 12(%esi),%ebp

# qhasm:   *(uint32 *) (out + 0) = in0
# asm 1: movl <in0=int32#1,0(<out=int32#6)
# asm 2: movl <in0=%eax,0(<out=%edi)
movl %eax,0(%edi)

# qhasm:   *(uint32 *) (out + 4) = in1
# asm 1: movl <in1=int32#2,4(<out=int32#6)
# asm 2: movl <in1=%ecx,4(<out=%edi)
movl %ecx,4(%edi)

# qhasm:   *(uint32 *) (out + 8) = in2
# asm 1: movl <in2=int32#4,8(<out=int32#6)
# asm 2: movl <in2=%ebx,8(<out=%edi)
movl %ebx,8(%edi)

# qhasm:   *(uint32 *) (out + 12) = in3
# asm 1: movl <in3=int32#7,12(<out=int32#6)
# asm 2: movl <in3=%ebp,12(<out=%edi)
movl %ebp,12(%edi)

# qhasm:   in0 = z0
# asm 1: movd   <z0=int6464#1,>in0=int32#1
# asm 2: movd   <z0=%xmm0,>in0=%eax
movd   %xmm0,%eax

# qhasm:   in1 = z1
# asm 1: movd   <z1=int6464#2,>in1=int32#2
# asm 2: movd   <z1=%xmm1,>in1=%ecx
movd   %xmm1,%ecx

# qhasm:   in2 = z2
# asm 1: movd   <z2=int6464#3,>in2=int32#4
# asm 2: movd   <z2=%xmm2,>in2=%ebx
movd   %xmm2,%ebx

# qhasm:   in3 = z3
# asm 1: movd   <z3=int6464#4,>in3=int32#7
# asm 2: movd   <z3=%xmm3,>in3=%ebp
movd   %xmm3,%ebp

# qhasm:   z0 <<<= 96
# asm 1: pshufd $0x39,<z0=int6464#1,<z0=int6464#1
# asm 2: pshufd $0x39,<z0=%xmm0,<z0=%xmm0
pshufd $0x39,%xmm0,%xmm0

# qhasm:   z1 <<<= 96
# asm 1: pshufd $0x39,<z1=int6464#2,<z1=int6464#2
# asm 2: pshufd $0x39,<z1=%xmm1,<z1=%xmm1
pshufd $0x39,%xmm1,%xmm1

# qhasm:   z2 <<<= 96
# asm 1: pshufd $0x39,<z2=int6464#3,<z2=int6464#3
# asm 2: pshufd $0x39,<z2=%xmm2,<z2=%xmm2
pshufd $0x39,%xmm2,%xmm2

# qhasm:   z3 <<<= 96
# asm 1: pshufd $0x39,<z3=int6464#4,<z3=int6464#4
# asm 2: pshufd $0x39,<z3=%xmm3,<z3=%xmm3
pshufd $0x39,%xmm3,%xmm3

# qhasm:   in0 ^= *(uint32 *) (m + 64)
# asm 1: xorl 64(<m=int32#5),<in0=int32#1
# asm 2: xorl 64(<m=%esi),<in0=%eax
xorl 64(%esi),%eax

# qhasm:   in1 ^= *(uint32 *) (m + 68)
# asm 1: xorl 68(<m=int32#5),<in1=int32#2
# asm 2: xorl 68(<m=%esi),<in1=%ecx
xorl 68(%esi),%ecx

# qhasm:   in2 ^= *(uint32 *) (m + 72)
# asm 1: xorl 72(<m=int32#5),<in2=int32#4
# asm 2: xorl 72(<m=%esi),<in2=%ebx
xorl 72(%esi),%ebx

# qhasm:   in3 ^= *(uint32 *) (m + 76)
# asm 1: xorl 76(<m=int32#5),<in3=int32#7
# asm 2: xorl 76(<m=%esi),<in3=%ebp
xorl 76(%esi),%ebp

# qhasm:   *(uint32 *) (out + 64) = in0
# asm 1: movl <in0=int32#1,64(<out=int32#6)
# asm 2: movl <in0=%eax,64(<out=%edi)
movl %eax,64(%edi)

# qhasm:   *(uint32 *) (out + 68) = in1
# asm 1: movl <in1=int32#2,68(<out=int32#6)
# asm 2: movl <in1=%ecx,68(<out=%edi)
movl %ecx,68(%edi)

# qhasm:   *(uint32 *) (out + 72) = in2
# asm 1: movl <in2=int32#4,72(<out=int32#6)
# asm 2: movl <in2=%ebx,72(<out=%edi)
movl %ebx,72(%edi)

# qhasm:   *(uint32 *) (out + 76) = in3
# asm 1: movl <in3=int32#7,76(<out=int32#6)
# asm 2: movl <in3=%ebp,76(<out=%edi)
movl %ebp,76(%edi)

# qhasm:   in0 = z0
# asm 1: movd   <z0=int6464#1,>in0=int32#1
# asm 2: movd   <z0=%xmm0,>in0=%eax
movd   %xmm0,%eax

# qhasm:   in1 = z1
# asm 1: movd   <z1=int6464#2,>in1=int32#2
# asm 2: movd   <z1=%xmm1,>in1=%ecx
movd   %xmm1,%ecx

# qhasm:   in2 = z2
# asm 1: movd   <z2=int6464#3,>in2=int32#4
# asm 2: movd   <z2=%xmm2,>in2=%ebx
movd   %xmm2,%ebx

# qhasm:   in3 = z3
# asm 1: movd   <z3=int6464#4,>in3=int32#7
# asm 2: movd   <z3=%xmm3,>in3=%ebp
movd   %xmm3,%ebp

# qhasm:   z0 <<<= 96
# asm 1: pshufd $0x39,<z0=int6464#1,<z0=int6464#1
# asm 2: pshufd $0x39,<z0=%xmm0,<z0=%xmm0
pshufd $0x39,%xmm0,%xmm0

# qhasm:   z1 <<<= 96
# asm 1: pshufd $0x39,<z1=int6464#2,<z1=int6464#2
# asm 2: pshufd $0x39,<z1=%xmm1,<z1=%xmm1
pshufd $0x39,%xmm1,%xmm1

# qhasm:   z2 <<<= 96
# asm 1: pshufd $0x39,<z2=int6464#3,<z2=int6464#3
# asm 2: pshufd $0x39,<z2=%xmm2,<z2=%xmm2
pshufd $0x39,%xmm2,%xmm2

# qhasm:   z3 <<<= 96
# asm 1: pshufd $0x39,<z3=int6464#4,<z3=int6464#4
# asm 2: pshufd $0x39,<z3=%xmm3,<z3=%xmm3
pshufd $0x39,%xmm3,%xmm3

# qhasm:   in0 ^= *(uint32 *) (m + 128)
# asm 1: xorl 128(<m=int32#5),<in0=int32#1
# asm 2: xorl 128(<m=%esi),<in0=%eax
xorl 128(%esi),%eax

# qhasm:   in1 ^= *(uint32 *) (m + 132)
# asm 1: xorl 132(<m=int32#5),<in1=int32#2
# asm 2: xorl 132(<m=%esi),<in1=%ecx
xorl 132(%esi),%ecx

# qhasm:   in2 ^= *(uint32 *) (m + 136)
# asm 1: xorl 136(<m=int32#5),<in2=int32#4
# asm 2: xorl 136(<m=%esi),<in2=%ebx
xorl 136(%esi),%ebx

# qhasm:   in3 ^= *(uint32 *) (m + 140)
# asm 1: xorl 140(<m=int32#5),<in3=int32#7
# asm 2: xorl 140(<m=%esi),<in3=%ebp
xorl 140(%esi),%ebp

# qhasm:   *(uint32 *) (out + 128) = in0
# asm 1: movl <in0=int32#1,128(<out=int32#6)
# asm 2: movl <in0=%eax,128(<out=%edi)
movl %eax,128(%edi)

# qhasm:   *(uint32 *) (out + 132) = in1
# asm 1: movl <in1=int32#2,132(<out=int32#6)
# asm 2: movl <in1=%ecx,132(<out=%edi)
movl %ecx,132(%edi)

# qhasm:   *(uint32 *) (out + 136) = in2
# asm 1: movl <in2=int32#4,136(<out=int32#6)
# asm 2: movl <in2=%ebx,136(<out=%edi)
movl %ebx,136(%edi)

# qhasm:   *(uint32 *) (out + 140) = in3
# asm 1: movl <in3=int32#7,140(<out=int32#6)
# asm 2: movl <in3=%ebp,140(<out=%edi)
movl %ebp,140(%edi)

# qhasm:   in0 = z0
# asm 1: movd   <z0=int6464#1,>in0=int32#1
# asm 2: movd   <z0=%xmm0,>in0=%eax
movd   %xmm0,%eax

# qhasm:   in1 = z1
# asm 1: movd   <z1=int6464#2,>in1=int32#2
# asm 2: movd   <z1=%xmm1,>in1=%ecx
movd   %xmm1,%ecx

# qhasm:   in2 = z2
# asm 1: movd   <z2=int6464#3,>in2=int32#4
# asm 2: movd   <z2=%xmm2,>in2=%ebx
movd   %xmm2,%ebx

# qhasm:   in3 = z3
# asm 1: movd   <z3=int6464#4,>in3=int32#7
# asm 2: movd   <z3=%xmm3,>in3=%ebp
movd   %xmm3,%ebp

# qhasm:   in0 ^= *(uint32 *) (m + 192)
# asm 1: xorl 192(<m=int32#5),<in0=int32#1
# asm 2: xorl 192(<m=%esi),<in0=%eax
xorl 192(%esi),%eax

# qhasm:   in1 ^= *(uint32 *) (m + 196)
# asm 1: xorl 196(<m=int32#5),<in1=int32#2
# asm 2: xorl 196(<m=%esi),<in1=%ecx
xorl 196(%esi),%ecx

# qhasm:   in2 ^= *(uint32 *) (m + 200)
# asm 1: xorl 200(<m=int32#5),<in2=int32#4
# asm 2: xorl 200(<m=%esi),<in2=%ebx
xorl 200(%esi),%ebx

# qhasm:   in3 ^= *(uint32 *) (m + 204)
# asm 1: xorl 204(<m=int32#5),<in3=int32#7
# asm 2: xorl 204(<m=%esi),<in3=%ebp
xorl 204(%esi),%ebp

# qhasm:   *(uint32 *) (out + 192) = in0
# asm 1: movl <in0=int32#1,192(<out=int32#6)
# asm 2: movl <in0=%eax,192(<out=%edi)
movl %eax,192(%edi)

# qhasm:   *(uint32 *) (out + 196) = in1
# asm 1: movl <in1=int32#2,196(<out=int32#6)
# asm 2: movl <in1=%ecx,196(<out=%edi)
movl %ecx,196(%edi)

# qhasm:   *(uint32 *) (out + 200) = in2
# asm 1: movl <in2=int32#4,200(<out=int32#6)
# asm 2: movl <in2=%ebx,200(<out=%edi)
movl %ebx,200(%edi)

# qhasm:   *(uint32 *) (out + 204) = in3
# asm 1: movl <in3=int32#7,204(<out=int32#6)
# asm 2: movl <in3=%ebp,204(<out=%edi)
movl %ebp,204(%edi)

# qhasm:   z4 = z4_stack
# asm 1: movdqa <z4_stack=stack128#33,>z4=int6464#1
# asm 2: movdqa <z4_stack=544(%esp),>z4=%xmm0
movdqa 544(%esp),%xmm0

# qhasm:   z5 = z5_stack
# asm 1: movdqa <z5_stack=stack128#17,>z5=int6464#2
# asm 2: movdqa <z5_stack=288(%esp),>z5=%xmm1
movdqa 288(%esp),%xmm1

# qhasm:   z6 = z6_stack
# asm 1: movdqa <z6_stack=stack128#22,>z6=int6464#3
# asm 2: movdqa <z6_stack=368(%esp),>z6=%xmm2
movdqa 368(%esp),%xmm2

# qhasm:   z7 = z7_stack
# asm 1: movdqa <z7_stack=stack128#25,>z7=int6464#4
# asm 2: movdqa <z7_stack=416(%esp),>z7=%xmm3
movdqa 416(%esp),%xmm3

# qhasm:   uint32323232 z4 += orig4
# asm 1: paddd <orig4=stack128#5,<z4=int6464#1
# asm 2: paddd <orig4=96(%esp),<z4=%xmm0
paddd 96(%esp),%xmm0

# qhasm:   uint32323232 z5 += orig5
# asm 1: paddd <orig5=stack128#6,<z5=int6464#2
# asm 2: paddd <orig5=112(%esp),<z5=%xmm1
paddd 112(%esp),%xmm1

# qhasm:   uint32323232 z6 += orig6
# asm 1: paddd <orig6=stack128#7,<z6=int6464#3
# asm 2: paddd <orig6=128(%esp),<z6=%xmm2
paddd 128(%esp),%xmm2

# qhasm:   uint32323232 z7 += orig7
# asm 1: paddd <orig7=stack128#8,<z7=int6464#4
# asm 2: paddd <orig7=144(%esp),<z7=%xmm3
paddd 144(%esp),%xmm3

# qhasm:   in4 = z4
# asm 1: movd   <z4=int6464#1,>in4=int32#1
# asm 2: movd   <z4=%xmm0,>in4=%eax
movd   %xmm0,%eax

# qhasm:   in5 = z5
# asm 1: movd   <z5=int6464#2,>in5=int32#2
# asm 2: movd   <z5=%xmm1,>in5=%ecx
movd   %xmm1,%ecx

# qhasm:   in6 = z6
# asm 1: movd   <z6=int6464#3,>in6=int32#4
# asm 2: movd   <z6=%xmm2,>in6=%ebx
movd   %xmm2,%ebx

# qhasm:   in7 = z7
# asm 1: movd   <z7=int6464#4,>in7=int32#7
# asm 2: movd   <z7=%xmm3,>in7=%ebp
movd   %xmm3,%ebp

# qhasm:   z4 <<<= 96
# asm 1: pshufd $0x39,<z4=int6464#1,<z4=int6464#1
# asm 2: pshufd $0x39,<z4=%xmm0,<z4=%xmm0
pshufd $0x39,%xmm0,%xmm0

# qhasm:   z5 <<<= 96
# asm 1: pshufd $0x39,<z5=int6464#2,<z5=int6464#2
# asm 2: pshufd $0x39,<z5=%xmm1,<z5=%xmm1
pshufd $0x39,%xmm1,%xmm1

# qhasm:   z6 <<<= 96
# asm 1: pshufd $0x39,<z6=int6464#3,<z6=int6464#3
# asm 2: pshufd $0x39,<z6=%xmm2,<z6=%xmm2
pshufd $0x39,%xmm2,%xmm2

# qhasm:   z7 <<<= 96
# asm 1: pshufd $0x39,<z7=int6464#4,<z7=int6464#4
# asm 2: pshufd $0x39,<z7=%xmm3,<z7=%xmm3
pshufd $0x39,%xmm3,%xmm3

# qhasm:   in4 ^= *(uint32 *) (m + 16)
# asm 1: xorl 16(<m=int32#5),<in4=int32#1
# asm 2: xorl 16(<m=%esi),<in4=%eax
xorl 16(%esi),%eax

# qhasm:   in5 ^= *(uint32 *) (m + 20)
# asm 1: xorl 20(<m=int32#5),<in5=int32#2
# asm 2: xorl 20(<m=%esi),<in5=%ecx
xorl 20(%esi),%ecx

# qhasm:   in6 ^= *(uint32 *) (m + 24)
# asm 1: xorl 24(<m=int32#5),<in6=int32#4
# asm 2: xorl 24(<m=%esi),<in6=%ebx
xorl 24(%esi),%ebx

# qhasm:   in7 ^= *(uint32 *) (m + 28)
# asm 1: xorl 28(<m=int32#5),<in7=int32#7
# asm 2: xorl 28(<m=%esi),<in7=%ebp
xorl 28(%esi),%ebp

# qhasm:   *(uint32 *) (out + 16) = in4
# asm 1: movl <in4=int32#1,16(<out=int32#6)
# asm 2: movl <in4=%eax,16(<out=%edi)
movl %eax,16(%edi)

# qhasm:   *(uint32 *) (out + 20) = in5
# asm 1: movl <in5=int32#2,20(<out=int32#6)
# asm 2: movl <in5=%ecx,20(<out=%edi)
movl %ecx,20(%edi)

# qhasm:   *(uint32 *) (out + 24) = in6
# asm 1: movl <in6=int32#4,24(<out=int32#6)
# asm 2: movl <in6=%ebx,24(<out=%edi)
movl %ebx,24(%edi)

# qhasm:   *(uint32 *) (out + 28) = in7
# asm 1: movl <in7=int32#7,28(<out=int32#6)
# asm 2: movl <in7=%ebp,28(<out=%edi)
movl %ebp,28(%edi)

# qhasm:   in4 = z4
# asm 1: movd   <z4=int6464#1,>in4=int32#1
# asm 2: movd   <z4=%xmm0,>in4=%eax
movd   %xmm0,%eax

# qhasm:   in5 = z5
# asm 1: movd   <z5=int6464#2,>in5=int32#2
# asm 2: movd   <z5=%xmm1,>in5=%ecx
movd   %xmm1,%ecx

# qhasm:   in6 = z6
# asm 1: movd   <z6=int6464#3,>in6=int32#4
# asm 2: movd   <z6=%xmm2,>in6=%ebx
movd   %xmm2,%ebx

# qhasm:   in7 = z7
# asm 1: movd   <z7=int6464#4,>in7=int32#7
# asm 2: movd   <z7=%xmm3,>in7=%ebp
movd   %xmm3,%ebp

# qhasm:   z4 <<<= 96
# asm 1: pshufd $0x39,<z4=int6464#1,<z4=int6464#1
# asm 2: pshufd $0x39,<z4=%xmm0,<z4=%xmm0
pshufd $0x39,%xmm0,%xmm0

# qhasm:   z5 <<<= 96
# asm 1: pshufd $0x39,<z5=int6464#2,<z5=int6464#2
# asm 2: pshufd $0x39,<z5=%xmm1,<z5=%xmm1
pshufd $0x39,%xmm1,%xmm1

# qhasm:   z6 <<<= 96
# asm 1: pshufd $0x39,<z6=int6464#3,<z6=int6464#3
# asm 2: pshufd $0x39,<z6=%xmm2,<z6=%xmm2
pshufd $0x39,%xmm2,%xmm2

# qhasm:   z7 <<<= 96
# asm 1: pshufd $0x39,<z7=int6464#4,<z7=int6464#4
# asm 2: pshufd $0x39,<z7=%xmm3,<z7=%xmm3
pshufd $0x39,%xmm3,%xmm3

# qhasm:   in4 ^= *(uint32 *) (m + 80)
# asm 1: xorl 80(<m=int32#5),<in4=int32#1
# asm 2: xorl 80(<m=%esi),<in4=%eax
xorl 80(%esi),%eax

# qhasm:   in5 ^= *(uint32 *) (m + 84)
# asm 1: xorl 84(<m=int32#5),<in5=int32#2
# asm 2: xorl 84(<m=%esi),<in5=%ecx
xorl 84(%esi),%ecx

# qhasm:   in6 ^= *(uint32 *) (m + 88)
# asm 1: xorl 88(<m=int32#5),<in6=int32#4
# asm 2: xorl 88(<m=%esi),<in6=%ebx
xorl 88(%esi),%ebx

# qhasm:   in7 ^= *(uint32 *) (m + 92)
# asm 1: xorl 92(<m=int32#5),<in7=int32#7
# asm 2: xorl 92(<m=%esi),<in7=%ebp
xorl 92(%esi),%ebp

# qhasm:   *(uint32 *) (out + 80) = in4
# asm 1: movl <in4=int32#1,80(<out=int32#6)
# asm 2: movl <in4=%eax,80(<out=%edi)
movl %eax,80(%edi)

# qhasm:   *(uint32 *) (out + 84) = in5
# asm 1: movl <in5=int32#2,84(<out=int32#6)
# asm 2: movl <in5=%ecx,84(<out=%edi)
movl %ecx,84(%edi)

# qhasm:   *(uint32 *) (out + 88) = in6
# asm 1: movl <in6=int32#4,88(<out=int32#6)
# asm 2: movl <in6=%ebx,88(<out=%edi)
movl %ebx,88(%edi)

# qhasm:   *(uint32 *) (out + 92) = in7
# asm 1: movl <in7=int32#7,92(<out=int32#6)
# asm 2: movl <in7=%ebp,92(<out=%edi)
movl %ebp,92(%edi)

# qhasm:   in4 = z4
# asm 1: movd   <z4=int6464#1,>in4=int32#1
# asm 2: movd   <z4=%xmm0,>in4=%eax
movd   %xmm0,%eax

# qhasm:   in5 = z5
# asm 1: movd   <z5=int6464#2,>in5=int32#2
# asm 2: movd   <z5=%xmm1,>in5=%ecx
movd   %xmm1,%ecx

# qhasm:   in6 = z6
# asm 1: movd   <z6=int6464#3,>in6=int32#4
# asm 2: movd   <z6=%xmm2,>in6=%ebx
movd   %xmm2,%ebx

# qhasm:   in7 = z7
# asm 1: movd   <z7=int6464#4,>in7=int32#7
# asm 2: movd   <z7=%xmm3,>in7=%ebp
movd   %xmm3,%ebp

# qhasm:   z4 <<<= 96
# asm 1: pshufd $0x39,<z4=int6464#1,<z4=int6464#1
# asm 2: pshufd $0x39,<z4=%xmm0,<z4=%xmm0
pshufd $0x39,%xmm0,%xmm0

# qhasm:   z5 <<<= 96
# asm 1: pshufd $0x39,<z5=int6464#2,<z5=int6464#2
# asm 2: pshufd $0x39,<z5=%xmm1,<z5=%xmm1
pshufd $0x39,%xmm1,%xmm1

# qhasm:   z6 <<<= 96
# asm 1: pshufd $0x39,<z6=int6464#3,<z6=int6464#3
# asm 2: pshufd $0x39,<z6=%xmm2,<z6=%xmm2
pshufd $0x39,%xmm2,%xmm2

# qhasm:   z7 <<<= 96
# asm 1: pshufd $0x39,<z7=int6464#4,<z7=int6464#4
# asm 2: pshufd $0x39,<z7=%xmm3,<z7=%xmm3
pshufd $0x39,%xmm3,%xmm3

# qhasm:   in4 ^= *(uint32 *) (m + 144)
# asm 1: xorl 144(<m=int32#5),<in4=int32#1
# asm 2: xorl 144(<m=%esi),<in4=%eax
xorl 144(%esi),%eax

# qhasm:   in5 ^= *(uint32 *) (m + 148)
# asm 1: xorl 148(<m=int32#5),<in5=int32#2
# asm 2: xorl 148(<m=%esi),<in5=%ecx
xorl 148(%esi),%ecx

# qhasm:   in6 ^= *(uint32 *) (m + 152)
# asm 1: xorl 152(<m=int32#5),<in6=int32#4
# asm 2: xorl 152(<m=%esi),<in6=%ebx
xorl 152(%esi),%ebx

# qhasm:   in7 ^= *(uint32 *) (m + 156)
# asm 1: xorl 156(<m=int32#5),<in7=int32#7
# asm 2: xorl 156(<m=%esi),<in7=%ebp
xorl 156(%esi),%ebp

# qhasm:   *(uint32 *) (out + 144) = in4
# asm 1: movl <in4=int32#1,144(<out=int32#6)
# asm 2: movl <in4=%eax,144(<out=%edi)
movl %eax,144(%edi)

# qhasm:   *(uint32 *) (out + 148) = in5
# asm 1: movl <in5=int32#2,148(<out=int32#6)
# asm 2: movl <in5=%ecx,148(<out=%edi)
movl %ecx,148(%edi)

# qhasm:   *(uint32 *) (out + 152) = in6
# asm 1: movl <in6=int32#4,152(<out=int32#6)
# asm 2: movl <in6=%ebx,152(<out=%edi)
movl %ebx,152(%edi)

# qhasm:   *(uint32 *) (out + 156) = in7
# asm 1: movl <in7=int32#7,156(<out=int32#6)
# asm 2: movl <in7=%ebp,156(<out=%edi)
movl %ebp,156(%edi)

# qhasm:   in4 = z4
# asm 1: movd   <z4=int6464#1,>in4=int32#1
# asm 2: movd   <z4=%xmm0,>in4=%eax
movd   %xmm0,%eax

# qhasm:   in5 = z5
# asm 1: movd   <z5=int6464#2,>in5=int32#2
# asm 2: movd   <z5=%xmm1,>in5=%ecx
movd   %xmm1,%ecx

# qhasm:   in6 = z6
# asm 1: movd   <z6=int6464#3,>in6=int32#4
# asm 2: movd   <z6=%xmm2,>in6=%ebx
movd   %xmm2,%ebx

# qhasm:   in7 = z7
# asm 1: movd   <z7=int6464#4,>in7=int32#7
# asm 2: movd   <z7=%xmm3,>in7=%ebp
movd   %xmm3,%ebp

# qhasm:   in4 ^= *(uint32 *) (m + 208)
# asm 1: xorl 208(<m=int32#5),<in4=int32#1
# asm 2: xorl 208(<m=%esi),<in4=%eax
xorl 208(%esi),%eax

# qhasm:   in5 ^= *(uint32 *) (m + 212)
# asm 1: xorl 212(<m=int32#5),<in5=int32#2
# asm 2: xorl 212(<m=%esi),<in5=%ecx
xorl 212(%esi),%ecx

# qhasm:   in6 ^= *(uint32 *) (m + 216)
# asm 1: xorl 216(<m=int32#5),<in6=int32#4
# asm 2: xorl 216(<m=%esi),<in6=%ebx
xorl 216(%esi),%ebx

# qhasm:   in7 ^= *(uint32 *) (m + 220)
# asm 1: xorl 220(<m=int32#5),<in7=int32#7
# asm 2: xorl 220(<m=%esi),<in7=%ebp
xorl 220(%esi),%ebp

# qhasm:   *(uint32 *) (out + 208) = in4
# asm 1: movl <in4=int32#1,208(<out=int32#6)
# asm 2: movl <in4=%eax,208(<out=%edi)
movl %eax,208(%edi)

# qhasm:   *(uint32 *) (out + 212) = in5
# asm 1: movl <in5=int32#2,212(<out=int32#6)
# asm 2: movl <in5=%ecx,212(<out=%edi)
movl %ecx,212(%edi)

# qhasm:   *(uint32 *) (out + 216) = in6
# asm 1: movl <in6=int32#4,216(<out=int32#6)
# asm 2: movl <in6=%ebx,216(<out=%edi)
movl %ebx,216(%edi)

# qhasm:   *(uint32 *) (out + 220) = in7
# asm 1: movl <in7=int32#7,220(<out=int32#6)
# asm 2: movl <in7=%ebp,220(<out=%edi)
movl %ebp,220(%edi)

# qhasm:   z8 = z8_stack
# asm 1: movdqa <z8_stack=stack128#29,>z8=int6464#1
# asm 2: movdqa <z8_stack=480(%esp),>z8=%xmm0
movdqa 480(%esp),%xmm0

# qhasm:   z9 = z9_stack
# asm 1: movdqa <z9_stack=stack128#28,>z9=int6464#2
# asm 2: movdqa <z9_stack=464(%esp),>z9=%xmm1
movdqa 464(%esp),%xmm1

# qhasm:   z10 = z10_stack
# asm 1: movdqa <z10_stack=stack128#18,>z10=int6464#3
# asm 2: movdqa <z10_stack=304(%esp),>z10=%xmm2
movdqa 304(%esp),%xmm2

# qhasm:   z11 = z11_stack
# asm 1: movdqa <z11_stack=stack128#23,>z11=int6464#4
# asm 2: movdqa <z11_stack=384(%esp),>z11=%xmm3
movdqa 384(%esp),%xmm3

# qhasm:   uint32323232 z8 += orig8
# asm 1: paddd <orig8=stack128#9,<z8=int6464#1
# asm 2: paddd <orig8=160(%esp),<z8=%xmm0
paddd 160(%esp),%xmm0

# qhasm:   uint32323232 z9 += orig9
# asm 1: paddd <orig9=stack128#10,<z9=int6464#2
# asm 2: paddd <orig9=176(%esp),<z9=%xmm1
paddd 176(%esp),%xmm1

# qhasm:   uint32323232 z10 += orig10
# asm 1: paddd <orig10=stack128#11,<z10=int6464#3
# asm 2: paddd <orig10=192(%esp),<z10=%xmm2
paddd 192(%esp),%xmm2

# qhasm:   uint32323232 z11 += orig11
# asm 1: paddd <orig11=stack128#12,<z11=int6464#4
# asm 2: paddd <orig11=208(%esp),<z11=%xmm3
paddd 208(%esp),%xmm3

# qhasm:   in8 = z8
# asm 1: movd   <z8=int6464#1,>in8=int32#1
# asm 2: movd   <z8=%xmm0,>in8=%eax
movd   %xmm0,%eax

# qhasm:   in9 = z9
# asm 1: movd   <z9=int6464#2,>in9=int32#2
# asm 2: movd   <z9=%xmm1,>in9=%ecx
movd   %xmm1,%ecx

# qhasm:   in10 = z10
# asm 1: movd   <z10=int6464#3,>in10=int32#4
# asm 2: movd   <z10=%xmm2,>in10=%ebx
movd   %xmm2,%ebx

# qhasm:   in11 = z11
# asm 1: movd   <z11=int6464#4,>in11=int32#7
# asm 2: movd   <z11=%xmm3,>in11=%ebp
movd   %xmm3,%ebp

# qhasm:   z8 <<<= 96
# asm 1: pshufd $0x39,<z8=int6464#1,<z8=int6464#1
# asm 2: pshufd $0x39,<z8=%xmm0,<z8=%xmm0
pshufd $0x39,%xmm0,%xmm0

# qhasm:   z9 <<<= 96
# asm 1: pshufd $0x39,<z9=int6464#2,<z9=int6464#2
# asm 2: pshufd $0x39,<z9=%xmm1,<z9=%xmm1
pshufd $0x39,%xmm1,%xmm1

# qhasm:   z10 <<<= 96
# asm 1: pshufd $0x39,<z10=int6464#3,<z10=int6464#3
# asm 2: pshufd $0x39,<z10=%xmm2,<z10=%xmm2
pshufd $0x39,%xmm2,%xmm2

# qhasm:   z11 <<<= 96
# asm 1: pshufd $0x39,<z11=int6464#4,<z11=int6464#4
# asm 2: pshufd $0x39,<z11=%xmm3,<z11=%xmm3
pshufd $0x39,%xmm3,%xmm3

# qhasm:   in8 ^= *(uint32 *) (m + 32)
# asm 1: xorl 32(<m=int32#5),<in8=int32#1
# asm 2: xorl 32(<m=%esi),<in8=%eax
xorl 32(%esi),%eax

# qhasm:   in9 ^= *(uint32 *) (m + 36)
# asm 1: xorl 36(<m=int32#5),<in9=int32#2
# asm 2: xorl 36(<m=%esi),<in9=%ecx
xorl 36(%esi),%ecx

# qhasm:   in10 ^= *(uint32 *) (m + 40)
# asm 1: xorl 40(<m=int32#5),<in10=int32#4
# asm 2: xorl 40(<m=%esi),<in10=%ebx
xorl 40(%esi),%ebx

# qhasm:   in11 ^= *(uint32 *) (m + 44)
# asm 1: xorl 44(<m=int32#5),<in11=int32#7
# asm 2: xorl 44(<m=%esi),<in11=%ebp
xorl 44(%esi),%ebp

# qhasm:   *(uint32 *) (out + 32) = in8
# asm 1: movl <in8=int32#1,32(<out=int32#6)
# asm 2: movl <in8=%eax,32(<out=%edi)
movl %eax,32(%edi)

# qhasm:   *(uint32 *) (out + 36) = in9
# asm 1: movl <in9=int32#2,36(<out=int32#6)
# asm 2: movl <in9=%ecx,36(<out=%edi)
movl %ecx,36(%edi)

# qhasm:   *(uint32 *) (out + 40) = in10
# asm 1: movl <in10=int32#4,40(<out=int32#6)
# asm 2: movl <in10=%ebx,40(<out=%edi)
movl %ebx,40(%edi)

# qhasm:   *(uint32 *) (out + 44) = in11
# asm 1: movl <in11=int32#7,44(<out=int32#6)
# asm 2: movl <in11=%ebp,44(<out=%edi)
movl %ebp,44(%edi)

# qhasm:   in8 = z8
# asm 1: movd   <z8=int6464#1,>in8=int32#1
# asm 2: movd   <z8=%xmm0,>in8=%eax
movd   %xmm0,%eax

# qhasm:   in9 = z9
# asm 1: movd   <z9=int6464#2,>in9=int32#2
# asm 2: movd   <z9=%xmm1,>in9=%ecx
movd   %xmm1,%ecx

# qhasm:   in10 = z10
# asm 1: movd   <z10=int6464#3,>in10=int32#4
# asm 2: movd   <z10=%xmm2,>in10=%ebx
movd   %xmm2,%ebx

# qhasm:   in11 = z11
# asm 1: movd   <z11=int6464#4,>in11=int32#7
# asm 2: movd   <z11=%xmm3,>in11=%ebp
movd   %xmm3,%ebp

# qhasm:   z8 <<<= 96
# asm 1: pshufd $0x39,<z8=int6464#1,<z8=int6464#1
# asm 2: pshufd $0x39,<z8=%xmm0,<z8=%xmm0
pshufd $0x39,%xmm0,%xmm0

# qhasm:   z9 <<<= 96
# asm 1: pshufd $0x39,<z9=int6464#2,<z9=int6464#2
# asm 2: pshufd $0x39,<z9=%xmm1,<z9=%xmm1
pshufd $0x39,%xmm1,%xmm1

# qhasm:   z10 <<<= 96
# asm 1: pshufd $0x39,<z10=int6464#3,<z10=int6464#3
# asm 2: pshufd $0x39,<z10=%xmm2,<z10=%xmm2
pshufd $0x39,%xmm2,%xmm2

# qhasm:   z11 <<<= 96
# asm 1: pshufd $0x39,<z11=int6464#4,<z11=int6464#4
# asm 2: pshufd $0x39,<z11=%xmm3,<z11=%xmm3
pshufd $0x39,%xmm3,%xmm3

# qhasm:   in8 ^= *(uint32 *) (m + 96)
# asm 1: xorl 96(<m=int32#5),<in8=int32#1
# asm 2: xorl 96(<m=%esi),<in8=%eax
xorl 96(%esi),%eax

# qhasm:   in9 ^= *(uint32 *) (m + 100)
# asm 1: xorl 100(<m=int32#5),<in9=int32#2
# asm 2: xorl 100(<m=%esi),<in9=%ecx
xorl 100(%esi),%ecx

# qhasm:   in10 ^= *(uint32 *) (m + 104)
# asm 1: xorl 104(<m=int32#5),<in10=int32#4
# asm 2: xorl 104(<m=%esi),<in10=%ebx
xorl 104(%esi),%ebx

# qhasm:   in11 ^= *(uint32 *) (m + 108)
# asm 1: xorl 108(<m=int32#5),<in11=int32#7
# asm 2: xorl 108(<m=%esi),<in11=%ebp
xorl 108(%esi),%ebp

# qhasm:   *(uint32 *) (out + 96) = in8
# asm 1: movl <in8=int32#1,96(<out=int32#6)
# asm 2: movl <in8=%eax,96(<out=%edi)
movl %eax,96(%edi)

# qhasm:   *(uint32 *) (out + 100) = in9
# asm 1: movl <in9=int32#2,100(<out=int32#6)
# asm 2: movl <in9=%ecx,100(<out=%edi)
movl %ecx,100(%edi)

# qhasm:   *(uint32 *) (out + 104) = in10
# asm 1: movl <in10=int32#4,104(<out=int32#6)
# asm 2: movl <in10=%ebx,104(<out=%edi)
movl %ebx,104(%edi)

# qhasm:   *(uint32 *) (out + 108) = in11
# asm 1: movl <in11=int32#7,108(<out=int32#6)
# asm 2: movl <in11=%ebp,108(<out=%edi)
movl %ebp,108(%edi)

# qhasm:   in8 = z8
# asm 1: movd   <z8=int6464#1,>in8=int32#1
# asm 2: movd   <z8=%xmm0,>in8=%eax
movd   %xmm0,%eax

# qhasm:   in9 = z9
# asm 1: movd   <z9=int6464#2,>in9=int32#2
# asm 2: movd   <z9=%xmm1,>in9=%ecx
movd   %xmm1,%ecx

# qhasm:   in10 = z10
# asm 1: movd   <z10=int6464#3,>in10=int32#4
# asm 2: movd   <z10=%xmm2,>in10=%ebx
movd   %xmm2,%ebx

# qhasm:   in11 = z11
# asm 1: movd   <z11=int6464#4,>in11=int32#7
# asm 2: movd   <z11=%xmm3,>in11=%ebp
movd   %xmm3,%ebp

# qhasm:   z8 <<<= 96
# asm 1: pshufd $0x39,<z8=int6464#1,<z8=int6464#1
# asm 2: pshufd $0x39,<z8=%xmm0,<z8=%xmm0
pshufd $0x39,%xmm0,%xmm0

# qhasm:   z9 <<<= 96
# asm 1: pshufd $0x39,<z9=int6464#2,<z9=int6464#2
# asm 2: pshufd $0x39,<z9=%xmm1,<z9=%xmm1
pshufd $0x39,%xmm1,%xmm1

# qhasm:   z10 <<<= 96
# asm 1: pshufd $0x39,<z10=int6464#3,<z10=int6464#3
# asm 2: pshufd $0x39,<z10=%xmm2,<z10=%xmm2
pshufd $0x39,%xmm2,%xmm2

# qhasm:   z11 <<<= 96
# asm 1: pshufd $0x39,<z11=int6464#4,<z11=int6464#4
# asm 2: pshufd $0x39,<z11=%xmm3,<z11=%xmm3
pshufd $0x39,%xmm3,%xmm3

# qhasm:   in8 ^= *(uint32 *) (m + 160)
# asm 1: xorl 160(<m=int32#5),<in8=int32#1
# asm 2: xorl 160(<m=%esi),<in8=%eax
xorl 160(%esi),%eax

# qhasm:   in9 ^= *(uint32 *) (m + 164)
# asm 1: xorl 164(<m=int32#5),<in9=int32#2
# asm 2: xorl 164(<m=%esi),<in9=%ecx
xorl 164(%esi),%ecx

# qhasm:   in10 ^= *(uint32 *) (m + 168)
# asm 1: xorl 168(<m=int32#5),<in10=int32#4
# asm 2: xorl 168(<m=%esi),<in10=%ebx
xorl 168(%esi),%ebx

# qhasm:   in11 ^= *(uint32 *) (m + 172)
# asm 1: xorl 172(<m=int32#5),<in11=int32#7
# asm 2: xorl 172(<m=%esi),<in11=%ebp
xorl 172(%esi),%ebp

# qhasm:   *(uint32 *) (out + 160) = in8
# asm 1: movl <in8=int32#1,160(<out=int32#6)
# asm 2: movl <in8=%eax,160(<out=%edi)
movl %eax,160(%edi)

# qhasm:   *(uint32 *) (out + 164) = in9
# asm 1: movl <in9=int32#2,164(<out=int32#6)
# asm 2: movl <in9=%ecx,164(<out=%edi)
movl %ecx,164(%edi)

# qhasm:   *(uint32 *) (out + 168) = in10
# asm 1: movl <in10=int32#4,168(<out=int32#6)
# asm 2: movl <in10=%ebx,168(<out=%edi)
movl %ebx,168(%edi)

# qhasm:   *(uint32 *) (out + 172) = in11
# asm 1: movl <in11=int32#7,172(<out=int32#6)
# asm 2: movl <in11=%ebp,172(<out=%edi)
movl %ebp,172(%edi)

# qhasm:   in8 = z8
# asm 1: movd   <z8=int6464#1,>in8=int32#1
# asm 2: movd   <z8=%xmm0,>in8=%eax
movd   %xmm0,%eax

# qhasm:   in9 = z9
# asm 1: movd   <z9=int6464#2,>in9=int32#2
# asm 2: movd   <z9=%xmm1,>in9=%ecx
movd   %xmm1,%ecx

# qhasm:   in10 = z10
# asm 1: movd   <z10=int6464#3,>in10=int32#4
# asm 2: movd   <z10=%xmm2,>in10=%ebx
movd   %xmm2,%ebx

# qhasm:   in11 = z11
# asm 1: movd   <z11=int6464#4,>in11=int32#7
# asm 2: movd   <z11=%xmm3,>in11=%ebp
movd   %xmm3,%ebp

# qhasm:   in8 ^= *(uint32 *) (m + 224)
# asm 1: xorl 224(<m=int32#5),<in8=int32#1
# asm 2: xorl 224(<m=%esi),<in8=%eax
xorl 224(%esi),%eax

# qhasm:   in9 ^= *(uint32 *) (m + 228)
# asm 1: xorl 228(<m=int32#5),<in9=int32#2
# asm 2: xorl 228(<m=%esi),<in9=%ecx
xorl 228(%esi),%ecx

# qhasm:   in10 ^= *(uint32 *) (m + 232)
# asm 1: xorl 232(<m=int32#5),<in10=int32#4
# asm 2: xorl 232(<m=%esi),<in10=%ebx
xorl 232(%esi),%ebx

# qhasm:   in11 ^= *(uint32 *) (m + 236)
# asm 1: xorl 236(<m=int32#5),<in11=int32#7
# asm 2: xorl 236(<m=%esi),<in11=%ebp
xorl 236(%esi),%ebp

# qhasm:   *(uint32 *) (out + 224) = in8
# asm 1: movl <in8=int32#1,224(<out=int32#6)
# asm 2: movl <in8=%eax,224(<out=%edi)
movl %eax,224(%edi)

# qhasm:   *(uint32 *) (out + 228) = in9
# asm 1: movl <in9=int32#2,228(<out=int32#6)
# asm 2: movl <in9=%ecx,228(<out=%edi)
movl %ecx,228(%edi)

# qhasm:   *(uint32 *) (out + 232) = in10
# asm 1: movl <in10=int32#4,232(<out=int32#6)
# asm 2: movl <in10=%ebx,232(<out=%edi)
movl %ebx,232(%edi)

# qhasm:   *(uint32 *) (out + 236) = in11
# asm 1: movl <in11=int32#7,236(<out=int32#6)
# asm 2: movl <in11=%ebp,236(<out=%edi)
movl %ebp,236(%edi)

# qhasm:   z12 = z12_stack
# asm 1: movdqa <z12_stack=stack128#32,>z12=int6464#1
# asm 2: movdqa <z12_stack=528(%esp),>z12=%xmm0
movdqa 528(%esp),%xmm0

# qhasm:   z13 = z13_stack
# asm 1: movdqa <z13_stack=stack128#26,>z13=int6464#2
# asm 2: movdqa <z13_stack=432(%esp),>z13=%xmm1
movdqa 432(%esp),%xmm1

# qhasm:   z14 = z14_stack
# asm 1: movdqa <z14_stack=stack128#20,>z14=int6464#3
# asm 2: movdqa <z14_stack=336(%esp),>z14=%xmm2
movdqa 336(%esp),%xmm2

# qhasm:   z15 = z15_stack
# asm 1: movdqa <z15_stack=stack128#19,>z15=int6464#4
# asm 2: movdqa <z15_stack=320(%esp),>z15=%xmm3
movdqa 320(%esp),%xmm3

# qhasm:   uint32323232 z12 += orig12
# asm 1: paddd <orig12=stack128#15,<z12=int6464#1
# asm 2: paddd <orig12=256(%esp),<z12=%xmm0
paddd 256(%esp),%xmm0

# qhasm:   uint32323232 z13 += orig13
# asm 1: paddd <orig13=stack128#16,<z13=int6464#2
# asm 2: paddd <orig13=272(%esp),<z13=%xmm1
paddd 272(%esp),%xmm1

# qhasm:   uint32323232 z14 += orig14
# asm 1: paddd <orig14=stack128#13,<z14=int6464#3
# asm 2: paddd <orig14=224(%esp),<z14=%xmm2
paddd 224(%esp),%xmm2

# qhasm:   uint32323232 z15 += orig15
# asm 1: paddd <orig15=stack128#14,<z15=int6464#4
# asm 2: paddd <orig15=240(%esp),<z15=%xmm3
paddd 240(%esp),%xmm3

# qhasm:   in12 = z12
# asm 1: movd   <z12=int6464#1,>in12=int32#1
# asm 2: movd   <z12=%xmm0,>in12=%eax
movd   %xmm0,%eax

# qhasm:   in13 = z13
# asm 1: movd   <z13=int6464#2,>in13=int32#2
# asm 2: movd   <z13=%xmm1,>in13=%ecx
movd   %xmm1,%ecx

# qhasm:   in14 = z14
# asm 1: movd   <z14=int6464#3,>in14=int32#4
# asm 2: movd   <z14=%xmm2,>in14=%ebx
movd   %xmm2,%ebx

# qhasm:   in15 = z15
# asm 1: movd   <z15=int6464#4,>in15=int32#7
# asm 2: movd   <z15=%xmm3,>in15=%ebp
movd   %xmm3,%ebp

# qhasm:   z12 <<<= 96
# asm 1: pshufd $0x39,<z12=int6464#1,<z12=int6464#1
# asm 2: pshufd $0x39,<z12=%xmm0,<z12=%xmm0
pshufd $0x39,%xmm0,%xmm0

# qhasm:   z13 <<<= 96
# asm 1: pshufd $0x39,<z13=int6464#2,<z13=int6464#2
# asm 2: pshufd $0x39,<z13=%xmm1,<z13=%xmm1
pshufd $0x39,%xmm1,%xmm1

# qhasm:   z14 <<<= 96
# asm 1: pshufd $0x39,<z14=int6464#3,<z14=int6464#3
# asm 2: pshufd $0x39,<z14=%xmm2,<z14=%xmm2
pshufd $0x39,%xmm2,%xmm2

# qhasm:   z15 <<<= 96
# asm 1: pshufd $0x39,<z15=int6464#4,<z15=int6464#4
# asm 2: pshufd $0x39,<z15=%xmm3,<z15=%xmm3
pshufd $0x39,%xmm3,%xmm3

# qhasm:   in12 ^= *(uint32 *) (m + 48)
# asm 1: xorl 48(<m=int32#5),<in12=int32#1
# asm 2: xorl 48(<m=%esi),<in12=%eax
xorl 48(%esi),%eax

# qhasm:   in13 ^= *(uint32 *) (m + 52)
# asm 1: xorl 52(<m=int32#5),<in13=int32#2
# asm 2: xorl 52(<m=%esi),<in13=%ecx
xorl 52(%esi),%ecx

# qhasm:   in14 ^= *(uint32 *) (m + 56)
# asm 1: xorl 56(<m=int32#5),<in14=int32#4
# asm 2: xorl 56(<m=%esi),<in14=%ebx
xorl 56(%esi),%ebx

# qhasm:   in15 ^= *(uint32 *) (m + 60)
# asm 1: xorl 60(<m=int32#5),<in15=int32#7
# asm 2: xorl 60(<m=%esi),<in15=%ebp
xorl 60(%esi),%ebp

# qhasm:   *(uint32 *) (out + 48) = in12
# asm 1: movl <in12=int32#1,48(<out=int32#6)
# asm 2: movl <in12=%eax,48(<out=%edi)
movl %eax,48(%edi)

# qhasm:   *(uint32 *) (out + 52) = in13
# asm 1: movl <in13=int32#2,52(<out=int32#6)
# asm 2: movl <in13=%ecx,52(<out=%edi)
movl %ecx,52(%edi)

# qhasm:   *(uint32 *) (out + 56) = in14
# asm 1: movl <in14=int32#4,56(<out=int32#6)
# asm 2: movl <in14=%ebx,56(<out=%edi)
movl %ebx,56(%edi)

# qhasm:   *(uint32 *) (out + 60) = in15
# asm 1: movl <in15=int32#7,60(<out=int32#6)
# asm 2: movl <in15=%ebp,60(<out=%edi)
movl %ebp,60(%edi)

# qhasm:   in12 = z12
# asm 1: movd   <z12=int6464#1,>in12=int32#1
# asm 2: movd   <z12=%xmm0,>in12=%eax
movd   %xmm0,%eax

# qhasm:   in13 = z13
# asm 1: movd   <z13=int6464#2,>in13=int32#2
# asm 2: movd   <z13=%xmm1,>in13=%ecx
movd   %xmm1,%ecx

# qhasm:   in14 = z14
# asm 1: movd   <z14=int6464#3,>in14=int32#4
# asm 2: movd   <z14=%xmm2,>in14=%ebx
movd   %xmm2,%ebx

# qhasm:   in15 = z15
# asm 1: movd   <z15=int6464#4,>in15=int32#7
# asm 2: movd   <z15=%xmm3,>in15=%ebp
movd   %xmm3,%ebp

# qhasm:   z12 <<<= 96
# asm 1: pshufd $0x39,<z12=int6464#1,<z12=int6464#1
# asm 2: pshufd $0x39,<z12=%xmm0,<z12=%xmm0
pshufd $0x39,%xmm0,%xmm0

# qhasm:   z13 <<<= 96
# asm 1: pshufd $0x39,<z13=int6464#2,<z13=int6464#2
# asm 2: pshufd $0x39,<z13=%xmm1,<z13=%xmm1
pshufd $0x39,%xmm1,%xmm1

# qhasm:   z14 <<<= 96
# asm 1: pshufd $0x39,<z14=int6464#3,<z14=int6464#3
# asm 2: pshufd $0x39,<z14=%xmm2,<z14=%xmm2
pshufd $0x39,%xmm2,%xmm2

# qhasm:   z15 <<<= 96
# asm 1: pshufd $0x39,<z15=int6464#4,<z15=int6464#4
# asm 2: pshufd $0x39,<z15=%xmm3,<z15=%xmm3
pshufd $0x39,%xmm3,%xmm3

# qhasm:   in12 ^= *(uint32 *) (m + 112)
# asm 1: xorl 112(<m=int32#5),<in12=int32#1
# asm 2: xorl 112(<m=%esi),<in12=%eax
xorl 112(%esi),%eax

# qhasm:   in13 ^= *(uint32 *) (m + 116)
# asm 1: xorl 116(<m=int32#5),<in13=int32#2
# asm 2: xorl 116(<m=%esi),<in13=%ecx
xorl 116(%esi),%ecx

# qhasm:   in14 ^= *(uint32 *) (m + 120)
# asm 1: xorl 120(<m=int32#5),<in14=int32#4
# asm 2: xorl 120(<m=%esi),<in14=%ebx
xorl 120(%esi),%ebx

# qhasm:   in15 ^= *(uint32 *) (m + 124)
# asm 1: xorl 124(<m=int32#5),<in15=int32#7
# asm 2: xorl 124(<m=%esi),<in15=%ebp
xorl 124(%esi),%ebp

# qhasm:   *(uint32 *) (out + 112) = in12
# asm 1: movl <in12=int32#1,112(<out=int32#6)
# asm 2: movl <in12=%eax,112(<out=%edi)
movl %eax,112(%edi)

# qhasm:   *(uint32 *) (out + 116) = in13
# asm 1: movl <in13=int32#2,116(<out=int32#6)
# asm 2: movl <in13=%ecx,116(<out=%edi)
movl %ecx,116(%edi)

# qhasm:   *(uint32 *) (out + 120) = in14
# asm 1: movl <in14=int32#4,120(<out=int32#6)
# asm 2: movl <in14=%ebx,120(<out=%edi)
movl %ebx,120(%edi)

# qhasm:   *(uint32 *) (out + 124) = in15
# asm 1: movl <in15=int32#7,124(<out=int32#6)
# asm 2: movl <in15=%ebp,124(<out=%edi)
movl %ebp,124(%edi)

# qhasm:   in12 = z12
# asm 1: movd   <z12=int6464#1,>in12=int32#1
# asm 2: movd   <z12=%xmm0,>in12=%eax
movd   %xmm0,%eax

# qhasm:   in13 = z13
# asm 1: movd   <z13=int6464#2,>in13=int32#2
# asm 2: movd   <z13=%xmm1,>in13=%ecx
movd   %xmm1,%ecx

# qhasm:   in14 = z14
# asm 1: movd   <z14=int6464#3,>in14=int32#4
# asm 2: movd   <z14=%xmm2,>in14=%ebx
movd   %xmm2,%ebx

# qhasm:   in15 = z15
# asm 1: movd   <z15=int6464#4,>in15=int32#7
# asm 2: movd   <z15=%xmm3,>in15=%ebp
movd   %xmm3,%ebp

# qhasm:   z12 <<<= 96
# asm 1: pshufd $0x39,<z12=int6464#1,<z12=int6464#1
# asm 2: pshufd $0x39,<z12=%xmm0,<z12=%xmm0
pshufd $0x39,%xmm0,%xmm0

# qhasm:   z13 <<<= 96
# asm 1: pshufd $0x39,<z13=int6464#2,<z13=int6464#2
# asm 2: pshufd $0x39,<z13=%xmm1,<z13=%xmm1
pshufd $0x39,%xmm1,%xmm1

# qhasm:   z14 <<<= 96
# asm 1: pshufd $0x39,<z14=int6464#3,<z14=int6464#3
# asm 2: pshufd $0x39,<z14=%xmm2,<z14=%xmm2
pshufd $0x39,%xmm2,%xmm2

# qhasm:   z15 <<<= 96
# asm 1: pshufd $0x39,<z15=int6464#4,<z15=int6464#4
# asm 2: pshufd $0x39,<z15=%xmm3,<z15=%xmm3
pshufd $0x39,%xmm3,%xmm3

# qhasm:   in12 ^= *(uint32 *) (m + 176)
# asm 1: xorl 176(<m=int32#5),<in12=int32#1
# asm 2: xorl 176(<m=%esi),<in12=%eax
xorl 176(%esi),%eax

# qhasm:   in13 ^= *(uint32 *) (m + 180)
# asm 1: xorl 180(<m=int32#5),<in13=int32#2
# asm 2: xorl 180(<m=%esi),<in13=%ecx
xorl 180(%esi),%ecx

# qhasm:   in14 ^= *(uint32 *) (m + 184)
# asm 1: xorl 184(<m=int32#5),<in14=int32#4
# asm 2: xorl 184(<m=%esi),<in14=%ebx
xorl 184(%esi),%ebx

# qhasm:   in15 ^= *(uint32 *) (m + 188)
# asm 1: xorl 188(<m=int32#5),<in15=int32#7
# asm 2: xorl 188(<m=%esi),<in15=%ebp
xorl 188(%esi),%ebp

# qhasm:   *(uint32 *) (out + 176) = in12
# asm 1: movl <in12=int32#1,176(<out=int32#6)
# asm 2: movl <in12=%eax,176(<out=%edi)
movl %eax,176(%edi)

# qhasm:   *(uint32 *) (out + 180) = in13
# asm 1: movl <in13=int32#2,180(<out=int32#6)
# asm 2: movl <in13=%ecx,180(<out=%edi)
movl %ecx,180(%edi)

# qhasm:   *(uint32 *) (out + 184) = in14
# asm 1: movl <in14=int32#4,184(<out=int32#6)
# asm 2: movl <in14=%ebx,184(<out=%edi)
movl %ebx,184(%edi)

# qhasm:   *(uint32 *) (out + 188) = in15
# asm 1: movl <in15=int32#7,188(<out=int32#6)
# asm 2: movl <in15=%ebp,188(<out=%edi)
movl %ebp,188(%edi)

# qhasm:   in12 = z12
# asm 1: movd   <z12=int6464#1,>in12=int32#1
# asm 2: movd   <z12=%xmm0,>in12=%eax
movd   %xmm0,%eax

# qhasm:   in13 = z13
# asm 1: movd   <z13=int6464#2,>in13=int32#2
# asm 2: movd   <z13=%xmm1,>in13=%ecx
movd   %xmm1,%ecx

# qhasm:   in14 = z14
# asm 1: movd   <z14=int6464#3,>in14=int32#4
# asm 2: movd   <z14=%xmm2,>in14=%ebx
movd   %xmm2,%ebx

# qhasm:   in15 = z15
# asm 1: movd   <z15=int6464#4,>in15=int32#7
# asm 2: movd   <z15=%xmm3,>in15=%ebp
movd   %xmm3,%ebp

# qhasm:   in12 ^= *(uint32 *) (m + 240)
# asm 1: xorl 240(<m=int32#5),<in12=int32#1
# asm 2: xorl 240(<m=%esi),<in12=%eax
xorl 240(%esi),%eax

# qhasm:   in13 ^= *(uint32 *) (m + 244)
# asm 1: xorl 244(<m=int32#5),<in13=int32#2
# asm 2: xorl 244(<m=%esi),<in13=%ecx
xorl 244(%esi),%ecx

# qhasm:   in14 ^= *(uint32 *) (m + 248)
# asm 1: xorl 248(<m=int32#5),<in14=int32#4
# asm 2: xorl 248(<m=%esi),<in14=%ebx
xorl 248(%esi),%ebx

# qhasm:   in15 ^= *(uint32 *) (m + 252)
# asm 1: xorl 252(<m=int32#5),<in15=int32#7
# asm 2: xorl 252(<m=%esi),<in15=%ebp
xorl 252(%esi),%ebp

# qhasm:   *(uint32 *) (out + 240) = in12
# asm 1: movl <in12=int32#1,240(<out=int32#6)
# asm 2: movl <in12=%eax,240(<out=%edi)
movl %eax,240(%edi)

# qhasm:   *(uint32 *) (out + 244) = in13
# asm 1: movl <in13=int32#2,244(<out=int32#6)
# asm 2: movl <in13=%ecx,244(<out=%edi)
movl %ecx,244(%edi)

# qhasm:   *(uint32 *) (out + 248) = in14
# asm 1: movl <in14=int32#4,248(<out=int32#6)
# asm 2: movl <in14=%ebx,248(<out=%edi)
movl %ebx,248(%edi)

# qhasm:   *(uint32 *) (out + 252) = in15
# asm 1: movl <in15=int32#7,252(<out=int32#6)
# asm 2: movl <in15=%ebp,252(<out=%edi)
movl %ebp,252(%edi)

# qhasm:   bytes = bytes_backup
# asm 1: movl <bytes_backup=stack32#6,>bytes=int32#4
# asm 2: movl <bytes_backup=20(%esp),>bytes=%ebx
movl 20(%esp),%ebx

# qhasm:   bytes -= 256
# asm 1: sub  $256,<bytes=int32#4
# asm 2: sub  $256,<bytes=%ebx
sub  $256,%ebx

# qhasm:   m += 256
# asm 1: add  $256,<m=int32#5
# asm 2: add  $256,<m=%esi
add  $256,%esi

# qhasm:   out += 256
# asm 1: add  $256,<out=int32#6
# asm 2: add  $256,<out=%edi
add  $256,%edi

# qhasm:                            unsigned<? bytes - 256
# asm 1: cmp  $256,<bytes=int32#4
# asm 2: cmp  $256,<bytes=%ebx
cmp  $256,%ebx
# comment:fp stack unchanged by jump

# qhasm:   goto bytesatleast256 if !unsigned<
jae ._bytesatleast256

# qhasm:                 unsigned>? bytes - 0
# asm 1: cmp  $0,<bytes=int32#4
# asm 2: cmp  $0,<bytes=%ebx
cmp  $0,%ebx
# comment:fp stack unchanged by jump

# qhasm:   goto done if !unsigned>
jbe ._done
# comment:fp stack unchanged by fallthrough

# qhasm: bytesbetween1and255:
._bytesbetween1and255:

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
# asm 2: leal <tmp=576(%esp),>out=%edi
leal 576(%esp),%edi

# qhasm:     i = bytes
# asm 1: mov  <bytes=int32#4,>i=int32#2
# asm 2: mov  <bytes=%ebx,>i=%ecx
mov  %ebx,%ecx

# qhasm:     while (i) { *out++ = *m++; --i }
rep movsb

# qhasm:     out = &tmp
# asm 1: leal <tmp=stack512#1,>out=int32#6
# asm 2: leal <tmp=576(%esp),>out=%edi
leal 576(%esp),%edi

# qhasm:     m = &tmp
# asm 1: leal <tmp=stack512#1,>m=int32#5
# asm 2: leal <tmp=576(%esp),>m=%esi
leal 576(%esp),%esi
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

# qhasm: mainloop2:
._mainloop2:

# qhasm: uint32323232    diag0 += diag1
# asm 1: paddd <diag1=int6464#2,<diag0=int6464#1
# asm 2: paddd <diag1=%xmm1,<diag0=%xmm0
paddd %xmm1,%xmm0

# qhasm:                 diag3 ^= diag0
# asm 1: pxor  <diag0=int6464#1,<diag3=int6464#4
# asm 2: pxor  <diag0=%xmm0,<diag3=%xmm3
pxor  %xmm0,%xmm3

# qhasm:                 b3 = diag3
# asm 1: movdqa <diag3=int6464#4,>b3=int6464#5
# asm 2: movdqa <diag3=%xmm3,>b3=%xmm4
movdqa %xmm3,%xmm4

# qhasm: uint32323232    diag3 <<= 16
# asm 1: pslld $16,<diag3=int6464#4
# asm 2: pslld $16,<diag3=%xmm3
pslld $16,%xmm3

# qhasm: uint32323232    b3 >>= 16
# asm 1: psrld $16,<b3=int6464#5
# asm 2: psrld $16,<b3=%xmm4
psrld $16,%xmm4

# qhasm:                 diag3 ^= b3
# asm 1: pxor  <b3=int6464#5,<diag3=int6464#4
# asm 2: pxor  <b3=%xmm4,<diag3=%xmm3
pxor  %xmm4,%xmm3

# qhasm: uint32323232                    diag2 += diag3
# asm 1: paddd <diag3=int6464#4,<diag2=int6464#3
# asm 2: paddd <diag3=%xmm3,<diag2=%xmm2
paddd %xmm3,%xmm2

# qhasm:                                 diag1 ^= diag2
# asm 1: pxor  <diag2=int6464#3,<diag1=int6464#2
# asm 2: pxor  <diag2=%xmm2,<diag1=%xmm1
pxor  %xmm2,%xmm1

# qhasm:                                 b1 = diag1
# asm 1: movdqa <diag1=int6464#2,>b1=int6464#5
# asm 2: movdqa <diag1=%xmm1,>b1=%xmm4
movdqa %xmm1,%xmm4

# qhasm: uint32323232                    diag1 <<= 12
# asm 1: pslld $12,<diag1=int6464#2
# asm 2: pslld $12,<diag1=%xmm1
pslld $12,%xmm1

# qhasm: uint32323232                    b1 >>= 20
# asm 1: psrld $20,<b1=int6464#5
# asm 2: psrld $20,<b1=%xmm4
psrld $20,%xmm4

# qhasm:                                 diag1 ^= b1
# asm 1: pxor  <b1=int6464#5,<diag1=int6464#2
# asm 2: pxor  <b1=%xmm4,<diag1=%xmm1
pxor  %xmm4,%xmm1

# qhasm: uint32323232                                    diag0 += diag1
# asm 1: paddd <diag1=int6464#2,<diag0=int6464#1
# asm 2: paddd <diag1=%xmm1,<diag0=%xmm0
paddd %xmm1,%xmm0

# qhasm:                                                 diag3 ^= diag0
# asm 1: pxor  <diag0=int6464#1,<diag3=int6464#4
# asm 2: pxor  <diag0=%xmm0,<diag3=%xmm3
pxor  %xmm0,%xmm3

# qhasm:                                                 b3 = diag3
# asm 1: movdqa <diag3=int6464#4,>b3=int6464#5
# asm 2: movdqa <diag3=%xmm3,>b3=%xmm4
movdqa %xmm3,%xmm4

# qhasm: uint32323232                                    diag3 <<= 8
# asm 1: pslld $8,<diag3=int6464#4
# asm 2: pslld $8,<diag3=%xmm3
pslld $8,%xmm3

# qhasm: uint32323232                                    b3 >>= 24
# asm 1: psrld $24,<b3=int6464#5
# asm 2: psrld $24,<b3=%xmm4
psrld $24,%xmm4

# qhasm:                 diag0 <<<= 32
# asm 1: pshufd $0x93,<diag0=int6464#1,<diag0=int6464#1
# asm 2: pshufd $0x93,<diag0=%xmm0,<diag0=%xmm0
pshufd $0x93,%xmm0,%xmm0

# qhasm:                                                 diag3 ^= b3
# asm 1: pxor  <b3=int6464#5,<diag3=int6464#4
# asm 2: pxor  <b3=%xmm4,<diag3=%xmm3
pxor  %xmm4,%xmm3

# qhasm: uint32323232                                                    diag2 += diag3
# asm 1: paddd <diag3=int6464#4,<diag2=int6464#3
# asm 2: paddd <diag3=%xmm3,<diag2=%xmm2
paddd %xmm3,%xmm2

# qhasm:                 diag3 <<<= 64
# asm 1: pshufd $0x4e,<diag3=int6464#4,<diag3=int6464#4
# asm 2: pshufd $0x4e,<diag3=%xmm3,<diag3=%xmm3
pshufd $0x4e,%xmm3,%xmm3

# qhasm:                                                                 diag1 ^= diag2
# asm 1: pxor  <diag2=int6464#3,<diag1=int6464#2
# asm 2: pxor  <diag2=%xmm2,<diag1=%xmm1
pxor  %xmm2,%xmm1

# qhasm:                 diag2 <<<= 96
# asm 1: pshufd $0x39,<diag2=int6464#3,<diag2=int6464#3
# asm 2: pshufd $0x39,<diag2=%xmm2,<diag2=%xmm2
pshufd $0x39,%xmm2,%xmm2

# qhasm:                                                                 b1 = diag1
# asm 1: movdqa <diag1=int6464#2,>b1=int6464#5
# asm 2: movdqa <diag1=%xmm1,>b1=%xmm4
movdqa %xmm1,%xmm4

# qhasm: uint32323232                                                    diag1 <<= 7
# asm 1: pslld $7,<diag1=int6464#2
# asm 2: pslld $7,<diag1=%xmm1
pslld $7,%xmm1

# qhasm: uint32323232                                                    b1 >>= 25
# asm 1: psrld $25,<b1=int6464#5
# asm 2: psrld $25,<b1=%xmm4
psrld $25,%xmm4

# qhasm:                                                                 diag1 ^= b1
# asm 1: pxor  <b1=int6464#5,<diag1=int6464#2
# asm 2: pxor  <b1=%xmm4,<diag1=%xmm1
pxor  %xmm4,%xmm1

# qhasm:                  unsigned>? i -= 2
# asm 1: sub  $2,<i=int32#1
# asm 2: sub  $2,<i=%eax
sub  $2,%eax

# qhasm: uint32323232    diag0 += diag1
# asm 1: paddd <diag1=int6464#2,<diag0=int6464#1
# asm 2: paddd <diag1=%xmm1,<diag0=%xmm0
paddd %xmm1,%xmm0

# qhasm:                 diag3 ^= diag0
# asm 1: pxor  <diag0=int6464#1,<diag3=int6464#4
# asm 2: pxor  <diag0=%xmm0,<diag3=%xmm3
pxor  %xmm0,%xmm3

# qhasm:                 b3 = diag3
# asm 1: movdqa <diag3=int6464#4,>b3=int6464#5
# asm 2: movdqa <diag3=%xmm3,>b3=%xmm4
movdqa %xmm3,%xmm4

# qhasm: uint32323232    diag3 <<= 16
# asm 1: pslld $16,<diag3=int6464#4
# asm 2: pslld $16,<diag3=%xmm3
pslld $16,%xmm3

# qhasm: uint32323232    b3 >>= 16
# asm 1: psrld $16,<b3=int6464#5
# asm 2: psrld $16,<b3=%xmm4
psrld $16,%xmm4

# qhasm:                 diag3 ^= b3
# asm 1: pxor  <b3=int6464#5,<diag3=int6464#4
# asm 2: pxor  <b3=%xmm4,<diag3=%xmm3
pxor  %xmm4,%xmm3

# qhasm: uint32323232                    diag2 += diag3
# asm 1: paddd <diag3=int6464#4,<diag2=int6464#3
# asm 2: paddd <diag3=%xmm3,<diag2=%xmm2
paddd %xmm3,%xmm2

# qhasm:                                 diag1 ^= diag2
# asm 1: pxor  <diag2=int6464#3,<diag1=int6464#2
# asm 2: pxor  <diag2=%xmm2,<diag1=%xmm1
pxor  %xmm2,%xmm1

# qhasm:                                 b1 = diag1
# asm 1: movdqa <diag1=int6464#2,>b1=int6464#5
# asm 2: movdqa <diag1=%xmm1,>b1=%xmm4
movdqa %xmm1,%xmm4

# qhasm: uint32323232                    diag1 <<= 12
# asm 1: pslld $12,<diag1=int6464#2
# asm 2: pslld $12,<diag1=%xmm1
pslld $12,%xmm1

# qhasm: uint32323232                    b1 >>= 20
# asm 1: psrld $20,<b1=int6464#5
# asm 2: psrld $20,<b1=%xmm4
psrld $20,%xmm4

# qhasm:                                 diag1 ^= b1
# asm 1: pxor  <b1=int6464#5,<diag1=int6464#2
# asm 2: pxor  <b1=%xmm4,<diag1=%xmm1
pxor  %xmm4,%xmm1

# qhasm: uint32323232                                    diag0 += diag1
# asm 1: paddd <diag1=int6464#2,<diag0=int6464#1
# asm 2: paddd <diag1=%xmm1,<diag0=%xmm0
paddd %xmm1,%xmm0

# qhasm:                                                 diag3 ^= diag0
# asm 1: pxor  <diag0=int6464#1,<diag3=int6464#4
# asm 2: pxor  <diag0=%xmm0,<diag3=%xmm3
pxor  %xmm0,%xmm3

# qhasm:                                                 b3 = diag3
# asm 1: movdqa <diag3=int6464#4,>b3=int6464#5
# asm 2: movdqa <diag3=%xmm3,>b3=%xmm4
movdqa %xmm3,%xmm4

# qhasm: uint32323232                                    diag3 <<= 8
# asm 1: pslld $8,<diag3=int6464#4
# asm 2: pslld $8,<diag3=%xmm3
pslld $8,%xmm3

# qhasm: uint32323232                                    b3 >>= 24
# asm 1: psrld $24,<b3=int6464#5
# asm 2: psrld $24,<b3=%xmm4
psrld $24,%xmm4

# qhasm:                 diag0 <<<= 96
# asm 1: pshufd $0x39,<diag0=int6464#1,<diag0=int6464#1
# asm 2: pshufd $0x39,<diag0=%xmm0,<diag0=%xmm0
pshufd $0x39,%xmm0,%xmm0

# qhasm:                                                 diag3 ^= b3
# asm 1: pxor  <b3=int6464#5,<diag3=int6464#4
# asm 2: pxor  <b3=%xmm4,<diag3=%xmm3
pxor  %xmm4,%xmm3

# qhasm: uint32323232                                                    diag2 += diag3
# asm 1: paddd <diag3=int6464#4,<diag2=int6464#3
# asm 2: paddd <diag3=%xmm3,<diag2=%xmm2
paddd %xmm3,%xmm2

# qhasm:                 diag3 <<<= 64
# asm 1: pshufd $0x4e,<diag3=int6464#4,<diag3=int6464#4
# asm 2: pshufd $0x4e,<diag3=%xmm3,<diag3=%xmm3
pshufd $0x4e,%xmm3,%xmm3

# qhasm:                                                                 diag1 ^= diag2
# asm 1: pxor  <diag2=int6464#3,<diag1=int6464#2
# asm 2: pxor  <diag2=%xmm2,<diag1=%xmm1
pxor  %xmm2,%xmm1

# qhasm:                 diag2 <<<= 32
# asm 1: pshufd $0x93,<diag2=int6464#3,<diag2=int6464#3
# asm 2: pshufd $0x93,<diag2=%xmm2,<diag2=%xmm2
pshufd $0x93,%xmm2,%xmm2

# qhasm:                                                                 b1 = diag1
# asm 1: movdqa <diag1=int6464#2,>b1=int6464#5
# asm 2: movdqa <diag1=%xmm1,>b1=%xmm4
movdqa %xmm1,%xmm4

# qhasm: uint32323232                                                    diag1 <<= 7
# asm 1: pslld $7,<diag1=int6464#2
# asm 2: pslld $7,<diag1=%xmm1
pslld $7,%xmm1

# qhasm: uint32323232                                                    b1 >>= 25
# asm 1: psrld $25,<b1=int6464#5
# asm 2: psrld $25,<b1=%xmm4
psrld $25,%xmm4

# qhasm:                                                                 diag1 ^= b1
# asm 1: pxor  <b1=int6464#5,<diag1=int6464#2
# asm 2: pxor  <b1=%xmm4,<diag1=%xmm1
pxor  %xmm4,%xmm1
# comment:fp stack unchanged by jump

# qhasm: goto mainloop2 if unsigned>
ja ._mainloop2

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

# qhasm: goto bytesbetween1and255
jmp ._bytesbetween1and255

# qhasm: enter ECRYPT_init
.text
.p2align 5
.globl _ECRYPT_init
.globl ECRYPT_init
_ECRYPT_init:
ECRYPT_init:
mov %esp,%eax
and $31,%eax
add $640,%eax
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
add $640,%eax
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
add $640,%eax
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
