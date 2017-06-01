
# qhasm: int64 x

# qhasm: int64 arg2

# qhasm: int64 arg3

# qhasm: int64 arg4

# qhasm: input x

# qhasm: input arg2

# qhasm: input arg3

# qhasm: input arg4

# qhasm: int64 i

# qhasm: int64 a

# qhasm: int64 m

# qhasm: int64 out

# qhasm: int64 bytes

# qhasm: stack64 ctarget

# qhasm: stack512 tmp

# qhasm: stack64 bytes_stack

# qhasm: stack64 out_stack

# qhasm: stack64 m_stack

# qhasm: stack64 x_stack

# qhasm: int64 z0

# qhasm: int64 z1

# qhasm: int64 z2

# qhasm: int64 z3

# qhasm: int64 z4

# qhasm: int64 z5

# qhasm: int64 z6

# qhasm: int64 z7

# qhasm: int64 z8

# qhasm: int64 z9

# qhasm: int64 z10

# qhasm: int64 z11

# qhasm: int64 z12

# qhasm: int64 z13

# qhasm: int64 z14

# qhasm: int64 z15

# qhasm: int64 u0

# qhasm: int64 u1

# qhasm: int64 u2

# qhasm: int64 u3

# qhasm: int64 u4

# qhasm: int64 u5

# qhasm: int64 u6

# qhasm: int64 u7

# qhasm: int64 u8

# qhasm: int64 u9

# qhasm: int64 u10

# qhasm: int64 u11

# qhasm: int64 u12

# qhasm: int64 u13

# qhasm: int64 u14

# qhasm: int64 u15

# qhasm: int64 y0

# qhasm: int64 y1

# qhasm: int64 y2

# qhasm: int64 y3

# qhasm: int64 y4

# qhasm: int64 y5

# qhasm: int64 y6

# qhasm: int64 y7

# qhasm: int64 y8

# qhasm: int64 y9

# qhasm: int64 y10

# qhasm: int64 y11

# qhasm: int64 y12

# qhasm: int64 y13

# qhasm: int64 y14

# qhasm: int64 y15

# qhasm: int64 x0

# qhasm: int64 x1

# qhasm: int64 x2

# qhasm: int64 x3

# qhasm: int64 x4

# qhasm: int64 x5

# qhasm: int64 x6

# qhasm: int64 x7

# qhasm: int64 x8

# qhasm: int64 x9

# qhasm: int64 x10

# qhasm: int64 x11

# qhasm: int64 x12

# qhasm: int64 x13

# qhasm: int64 x14

# qhasm: int64 x15

# qhasm: int64 q0

# qhasm: int64 q1

# qhasm: int64 q2

# qhasm: int64 q3

# qhasm: int64 q4

# qhasm: int64 q5

# qhasm: int64 q6

# qhasm: int64 q7

# qhasm: int64 q8

# qhasm: int64 q9

# qhasm: int64 q10

# qhasm: int64 q11

# qhasm: int64 q12

# qhasm: int64 q13

# qhasm: int64 q14

# qhasm: int64 q15

# qhasm: int64 m0

# qhasm: int64 m1

# qhasm: int64 m2

# qhasm: int64 m3

# qhasm: int64 m4

# qhasm: int64 m5

# qhasm: int64 m6

# qhasm: int64 m7

# qhasm: int64 m8

# qhasm: int64 m9

# qhasm: int64 m10

# qhasm: int64 m11

# qhasm: int64 m12

# qhasm: int64 m13

# qhasm: int64 m14

# qhasm: int64 m15

# qhasm: enter ECRYPT_keystream_bytes
.section ".text"
.align 32
.global ECRYPT_keystream_bytes
ECRYPT_keystream_bytes:
save %sp,-288,%sp

# qhasm: bytes = arg3
# asm 1: add %g0,<arg3=int64#3,>bytes=int64#5
# asm 2: add %g0,<arg3=%i2,>bytes=%i4
add %g0,%i2,%i4

# qhasm: m = arg2
# asm 1: add %g0,<arg2=int64#2,>m=int64#6
# asm 2: add %g0,<arg2=%i1,>m=%i5
add %g0,%i1,%i5

# qhasm: out = arg2
# asm 1: add %g0,<arg2=int64#2,>out=int64#2
# asm 2: add %g0,<arg2=%i1,>out=%i1
add %g0,%i1,%i1

# qhasm:               unsigned>? bytes - 0
# asm 1: subcc <bytes=int64#5,0,%g0
# asm 2: subcc <bytes=%i4,0,%g0
subcc %i4,0,%g0

# qhasm: goto done if !unsigned>
bleu,pt %xcc,._done
nop

# qhasm:   a = 0
# asm 1: add %g0,0,>a=int64#3
# asm 2: add %g0,0,>a=%i2
add %g0,0,%i2

# qhasm:   i = bytes
# asm 1: add %g0,<bytes=int64#5,>i=int64#4
# asm 2: add %g0,<bytes=%i4,>i=%i3
add %g0,%i4,%i3

# qhasm:   zeroloop:
._zeroloop:

# qhasm:     *(int8 *) (out + 0) = a
# asm 1: stb <a=int64#3,[<out=int64#2+0]
# asm 2: stb <a=%i2,[<out=%i1+0]
stb %i2,[%i1+0]

# qhasm:     out += 1
# asm 1: add <out=int64#2,1,>out=int64#2
# asm 2: add <out=%i1,1,>out=%i1
add %i1,1,%i1

# qhasm:                    unsigned>? i -= 1
# asm 1: subcc <i=int64#4,1,>i=int64#4
# asm 2: subcc <i=%i3,1,>i=%i3
subcc %i3,1,%i3

# qhasm:   goto zeroloop if unsigned>
bgu,pt %xcc,._zeroloop
nop

# qhasm:   out -= bytes
# asm 1: sub <out=int64#2,<bytes=int64#5,>out=int64#2
# asm 2: sub <out=%i1,<bytes=%i4,>out=%i1
sub %i1,%i4,%i1

# qhasm: goto bytesatleast1
b ._bytesatleast1
nop

# qhasm: enter ECRYPT_decrypt_bytes
.section ".text"
.align 32
.global ECRYPT_decrypt_bytes
ECRYPT_decrypt_bytes:
save %sp,-288,%sp

# qhasm: bytes = arg4
# asm 1: add %g0,<arg4=int64#4,>bytes=int64#5
# asm 2: add %g0,<arg4=%i3,>bytes=%i4
add %g0,%i3,%i4

# qhasm: m = arg2
# asm 1: add %g0,<arg2=int64#2,>m=int64#6
# asm 2: add %g0,<arg2=%i1,>m=%i5
add %g0,%i1,%i5

# qhasm: out = arg3
# asm 1: add %g0,<arg3=int64#3,>out=int64#2
# asm 2: add %g0,<arg3=%i2,>out=%i1
add %g0,%i2,%i1

# qhasm:               unsigned>? bytes - 0
# asm 1: subcc <bytes=int64#5,0,%g0
# asm 2: subcc <bytes=%i4,0,%g0
subcc %i4,0,%g0

# qhasm: goto done if !unsigned>
bleu,pt %xcc,._done
nop

# qhasm: goto bytesatleast1
b ._bytesatleast1
nop

# qhasm: enter ECRYPT_encrypt_bytes
.section ".text"
.align 32
.global ECRYPT_encrypt_bytes
ECRYPT_encrypt_bytes:
save %sp,-288,%sp

# qhasm: bytes = arg4
# asm 1: add %g0,<arg4=int64#4,>bytes=int64#5
# asm 2: add %g0,<arg4=%i3,>bytes=%i4
add %g0,%i3,%i4

# qhasm: m = arg2
# asm 1: add %g0,<arg2=int64#2,>m=int64#6
# asm 2: add %g0,<arg2=%i1,>m=%i5
add %g0,%i1,%i5

# qhasm: out = arg3
# asm 1: add %g0,<arg3=int64#3,>out=int64#2
# asm 2: add %g0,<arg3=%i2,>out=%i1
add %g0,%i2,%i1

# qhasm:               unsigned>? bytes - 0
# asm 1: subcc <bytes=int64#5,0,%g0
# asm 2: subcc <bytes=%i4,0,%g0
subcc %i4,0,%g0

# qhasm: goto done if !unsigned>
bleu,pt %xcc,._done
nop

# qhasm: bytesatleast1:
._bytesatleast1:

# qhasm:                           unsigned<? bytes - 64
# asm 1: subcc <bytes=int64#5,64,%g0
# asm 2: subcc <bytes=%i4,64,%g0
subcc %i4,64,%g0

# qhasm:   goto bytesatleast64 if !unsigned<
bgeu,pt %xcc,._bytesatleast64
nop

# qhasm:     ctarget = out
# asm 1: stx <out=int64#2,[%fp+2023->ctarget=stack64#1]
# asm 2: stx <out=%i1,[%fp+2023->ctarget=0]
stx %i1,[%fp+2023-0]

# qhasm:     out = &tmp
# asm 1: add %fp,1967->tmp=stack512#1,>out=int64#2
# asm 2: add %fp,1967->tmp=48,>out=%i1
add %fp,1967-48,%i1

# qhasm:     i = 0
# asm 1: add %g0,0,>i=int64#3
# asm 2: add %g0,0,>i=%i2
add %g0,0,%i2

# qhasm:     mcopyloop:
._mcopyloop:

# qhasm:       a = *(int8 *) (m + i)
# asm 1: ldsb [<m=int64#6+<i=int64#3],>a=int64#4
# asm 2: ldsb [<m=%i5+<i=%i2],>a=%i3
ldsb [%i5+%i2],%i3

# qhasm:       *(int8 *) (out + i) = a
# asm 1: stb <a=int64#4,[<out=int64#2+<i=int64#3]
# asm 2: stb <a=%i3,[<out=%i1+<i=%i2]
stb %i3,[%i1+%i2]

# qhasm:       i += 1
# asm 1: add <i=int64#3,1,>i=int64#3
# asm 2: add <i=%i2,1,>i=%i2
add %i2,1,%i2

# qhasm:                       unsigned<? i - bytes
# asm 1: subcc <i=int64#3,<bytes=int64#5,%g0
# asm 2: subcc <i=%i2,<bytes=%i4,%g0
subcc %i2,%i4,%g0

# qhasm:     goto mcopyloop if unsigned<
blu,pt %xcc,._mcopyloop
nop

# qhasm:     m = &tmp
# asm 1: add %fp,1967->tmp=stack512#1,>m=int64#6
# asm 2: add %fp,1967->tmp=48,>m=%i5
add %fp,1967-48,%i5

# qhasm:   bytesatleast64:
._bytesatleast64:

# qhasm:     x0 = *(uint32 *) (x + 0)
# asm 1: lduw [<x=int64#1+0],>x0=int64#3
# asm 2: lduw [<x=%i0+0],>x0=%i2
lduw [%i0+0],%i2

# qhasm:     x1 = *(uint32 *) (x + 4)
# asm 1: lduw [<x=int64#1+4],>x1=int64#4
# asm 2: lduw [<x=%i0+4],>x1=%i3
lduw [%i0+4],%i3

# qhasm:     x2 = *(uint32 *) (x + 8)
# asm 1: lduw [<x=int64#1+8],>x2=int64#7
# asm 2: lduw [<x=%i0+8],>x2=%g1
lduw [%i0+8],%g1

# qhasm:     x3 = *(uint32 *) (x + 12)
# asm 1: lduw [<x=int64#1+12],>x3=int64#8
# asm 2: lduw [<x=%i0+12],>x3=%g4
lduw [%i0+12],%g4

# qhasm:     x4 = *(uint32 *) (x + 16)
# asm 1: lduw [<x=int64#1+16],>x4=int64#9
# asm 2: lduw [<x=%i0+16],>x4=%g5
lduw [%i0+16],%g5

# qhasm:     x5 = *(uint32 *) (x + 20)
# asm 1: lduw [<x=int64#1+20],>x5=int64#10
# asm 2: lduw [<x=%i0+20],>x5=%o0
lduw [%i0+20],%o0

# qhasm:     x6 = *(uint32 *) (x + 24)
# asm 1: lduw [<x=int64#1+24],>x6=int64#11
# asm 2: lduw [<x=%i0+24],>x6=%o1
lduw [%i0+24],%o1

# qhasm:     x7 = *(uint32 *) (x + 28)
# asm 1: lduw [<x=int64#1+28],>x7=int64#12
# asm 2: lduw [<x=%i0+28],>x7=%o2
lduw [%i0+28],%o2

# qhasm:     x8 = *(uint32 *) (x + 32)
# asm 1: lduw [<x=int64#1+32],>x8=int64#13
# asm 2: lduw [<x=%i0+32],>x8=%o3
lduw [%i0+32],%o3

# qhasm:     x9 = *(uint32 *) (x + 36)
# asm 1: lduw [<x=int64#1+36],>x9=int64#14
# asm 2: lduw [<x=%i0+36],>x9=%o4
lduw [%i0+36],%o4

# qhasm:     x10 = *(uint32 *) (x + 40)
# asm 1: lduw [<x=int64#1+40],>x10=int64#15
# asm 2: lduw [<x=%i0+40],>x10=%o5
lduw [%i0+40],%o5

# qhasm:     x11 = *(uint32 *) (x + 44)
# asm 1: lduw [<x=int64#1+44],>x11=int64#16
# asm 2: lduw [<x=%i0+44],>x11=%o7
lduw [%i0+44],%o7

# qhasm:     x12 = *(uint32 *) (x + 48)
# asm 1: lduw [<x=int64#1+48],>x12=int64#17
# asm 2: lduw [<x=%i0+48],>x12=%l0
lduw [%i0+48],%l0

# qhasm:     x13 = *(uint32 *) (x + 52)
# asm 1: lduw [<x=int64#1+52],>x13=int64#18
# asm 2: lduw [<x=%i0+52],>x13=%l1
lduw [%i0+52],%l1

# qhasm:     x14 = *(uint32 *) (x + 56)
# asm 1: lduw [<x=int64#1+56],>x14=int64#19
# asm 2: lduw [<x=%i0+56],>x14=%l2
lduw [%i0+56],%l2

# qhasm:     x15 = *(uint32 *) (x + 60)
# asm 1: lduw [<x=int64#1+60],>x15=int64#20
# asm 2: lduw [<x=%i0+60],>x15=%l3
lduw [%i0+60],%l3

# qhasm:     i = 20
# asm 1: add %g0,20,>i=int64#21
# asm 2: add %g0,20,>i=%l4
add %g0,20,%l4

# qhasm:     bytes_stack = bytes
# asm 1: stx <bytes=int64#5,[%fp+2023->bytes_stack=stack64#2]
# asm 2: stx <bytes=%i4,[%fp+2023->bytes_stack=8]
stx %i4,[%fp+2023-8]

# qhasm:     out_stack = out
# asm 1: stx <out=int64#2,[%fp+2023->out_stack=stack64#3]
# asm 2: stx <out=%i1,[%fp+2023->out_stack=16]
stx %i1,[%fp+2023-16]

# qhasm:     m_stack = m
# asm 1: stx <m=int64#6,[%fp+2023->m_stack=stack64#4]
# asm 2: stx <m=%i5,[%fp+2023->m_stack=24]
stx %i5,[%fp+2023-24]

# qhasm:     x_stack = x
# asm 1: stx <x=int64#1,[%fp+2023->x_stack=stack64#5]
# asm 2: stx <x=%i0,[%fp+2023->x_stack=32]
stx %i0,[%fp+2023-32]

# qhasm:     mainloop:
._mainloop:

# qhasm: x0 += x4
# asm 1: add <x0=int64#3,<x4=int64#9,>x0=int64#1
# asm 2: add <x0=%i2,<x4=%g5,>x0=%i0
add %i2,%g5,%i0

# qhasm:                 x1 += x5
# asm 1: add <x1=int64#4,<x5=int64#10,>x1=int64#2
# asm 2: add <x1=%i3,<x5=%o0,>x1=%i1
add %i3,%o0,%i1

# qhasm: x12 ^= x0
# asm 1: xor <x12=int64#17,<x0=int64#1,>x12=int64#3
# asm 2: xor <x12=%l0,<x0=%i0,>x12=%i2
xor %l0,%i0,%i2

# qhasm:                                 x2 += x6
# asm 1: add <x2=int64#7,<x6=int64#11,>x2=int64#4
# asm 2: add <x2=%g1,<x6=%o1,>x2=%i3
add %g1,%o1,%i3

# qhasm: z12 = (uint32) x12 << 16
# asm 1: sll <x12=int64#3,16,>z12=int64#5
# asm 2: sll <x12=%i2,16,>z12=%i4
sll %i2,16,%i4

# qhasm:                 x13 ^= x1
# asm 1: xor <x13=int64#18,<x1=int64#2,>x13=int64#6
# asm 2: xor <x13=%l1,<x1=%i1,>x13=%i5
xor %l1,%i1,%i5

# qhasm: x12 = (uint32) x12 >> 16
# asm 1: srl <x12=int64#3,16,>x12=int64#3
# asm 2: srl <x12=%i2,16,>x12=%i2
srl %i2,16,%i2

# qhasm:                                 x14 ^= x2
# asm 1: xor <x14=int64#19,<x2=int64#4,>x14=int64#7
# asm 2: xor <x14=%l2,<x2=%i3,>x14=%g1
xor %l2,%i3,%g1

# qhasm:                 z13 = (uint32) x13 << 16
# asm 1: sll <x13=int64#6,16,>z13=int64#17
# asm 2: sll <x13=%i5,16,>z13=%l0
sll %i5,16,%l0

# qhasm: x12 |= z12
# asm 1: or  <x12=int64#3,<z12=int64#5,>x12=int64#3
# asm 2: or  <x12=%i2,<z12=%i4,>x12=%i2
or  %i2,%i4,%i2

# qhasm: 		x13 = (uint32) x13 >> 16
# asm 1: srl <x13=int64#6,16,>x13=int64#5
# asm 2: srl <x13=%i5,16,>x13=%i4
srl %i5,16,%i4

# qhasm:                                                 x3 += x7
# asm 1: add <x3=int64#8,<x7=int64#12,>x3=int64#6
# asm 2: add <x3=%g4,<x7=%o2,>x3=%i5
add %g4,%o2,%i5

# qhasm:                                 z14 = (uint32) x14 << 16
# asm 1: sll <x14=int64#7,16,>z14=int64#8
# asm 2: sll <x14=%g1,16,>z14=%g4
sll %g1,16,%g4

# qhasm:                                                 x15 ^= x3
# asm 1: xor <x15=int64#20,<x3=int64#6,>x15=int64#18
# asm 2: xor <x15=%l3,<x3=%i5,>x15=%l1
xor %l3,%i5,%l1

# qhasm: 				x14 = (uint32) x14 >> 16
# asm 1: srl <x14=int64#7,16,>x14=int64#7
# asm 2: srl <x14=%g1,16,>x14=%g1
srl %g1,16,%g1

# qhasm: 		x13 |= z13
# asm 1: or  <x13=int64#5,<z13=int64#17,>x13=int64#5
# asm 2: or  <x13=%i4,<z13=%l0,>x13=%i4
or  %i4,%l0,%i4

# qhasm:                                                 z15 = (uint32) x15 << 16
# asm 1: sll <x15=int64#18,16,>z15=int64#17
# asm 2: sll <x15=%l1,16,>z15=%l0
sll %l1,16,%l0

# qhasm: 				x14 |= z14
# asm 1: or  <x14=int64#7,<z14=int64#8,>x14=int64#7
# asm 2: or  <x14=%g1,<z14=%g4,>x14=%g1
or  %g1,%g4,%g1

# qhasm: 						x15 = (uint32) x15 >> 16
# asm 1: srl <x15=int64#18,16,>x15=int64#8
# asm 2: srl <x15=%l1,16,>x15=%g4
srl %l1,16,%g4

# qhasm: x8 += x12
# asm 1: add <x8=int64#13,<x12=int64#3,>x8=int64#13
# asm 2: add <x8=%o3,<x12=%i2,>x8=%o3
add %o3,%i2,%o3

# qhasm: 						x15 |= z15
# asm 1: or  <x15=int64#8,<z15=int64#17,>x15=int64#8
# asm 2: or  <x15=%g4,<z15=%l0,>x15=%g4
or  %g4,%l0,%g4

# qhasm:                 x9 += x13
# asm 1: add <x9=int64#14,<x13=int64#5,>x9=int64#14
# asm 2: add <x9=%o4,<x13=%i4,>x9=%o4
add %o4,%i4,%o4

# qhasm: x4 ^= x8
# asm 1: xor <x4=int64#9,<x8=int64#13,>x4=int64#9
# asm 2: xor <x4=%g5,<x8=%o3,>x4=%g5
xor %g5,%o3,%g5

# qhasm:                                 x10 += x14
# asm 1: add <x10=int64#15,<x14=int64#7,>x10=int64#15
# asm 2: add <x10=%o5,<x14=%g1,>x10=%o5
add %o5,%g1,%o5

# qhasm: z4 = (uint32) x4 << 12
# asm 1: sll <x4=int64#9,12,>z4=int64#17
# asm 2: sll <x4=%g5,12,>z4=%l0
sll %g5,12,%l0

# qhasm:                 x5 ^= x9
# asm 1: xor <x5=int64#10,<x9=int64#14,>x5=int64#10
# asm 2: xor <x5=%o0,<x9=%o4,>x5=%o0
xor %o0,%o4,%o0

# qhasm: x4 = (uint32) x4 >> 20
# asm 1: srl <x4=int64#9,20,>x4=int64#9
# asm 2: srl <x4=%g5,20,>x4=%g5
srl %g5,20,%g5

# qhasm:                                 x6 ^= x10
# asm 1: xor <x6=int64#11,<x10=int64#15,>x6=int64#11
# asm 2: xor <x6=%o1,<x10=%o5,>x6=%o1
xor %o1,%o5,%o1

# qhasm:                 z5 = (uint32) x5 << 12
# asm 1: sll <x5=int64#10,12,>z5=int64#18
# asm 2: sll <x5=%o0,12,>z5=%l1
sll %o0,12,%l1

# qhasm: x4 |= z4
# asm 1: or  <x4=int64#9,<z4=int64#17,>x4=int64#9
# asm 2: or  <x4=%g5,<z4=%l0,>x4=%g5
or  %g5,%l0,%g5

# qhasm: 		x5 = (uint32) x5 >> 20
# asm 1: srl <x5=int64#10,20,>x5=int64#10
# asm 2: srl <x5=%o0,20,>x5=%o0
srl %o0,20,%o0

# qhasm:                                                 x11 += x15
# asm 1: add <x11=int64#16,<x15=int64#8,>x11=int64#16
# asm 2: add <x11=%o7,<x15=%g4,>x11=%o7
add %o7,%g4,%o7

# qhasm:                                 z6 = (uint32) x6 << 12
# asm 1: sll <x6=int64#11,12,>z6=int64#17
# asm 2: sll <x6=%o1,12,>z6=%l0
sll %o1,12,%l0

# qhasm:                                                 x7 ^= x11
# asm 1: xor <x7=int64#12,<x11=int64#16,>x7=int64#12
# asm 2: xor <x7=%o2,<x11=%o7,>x7=%o2
xor %o2,%o7,%o2

# qhasm: 				x6 = (uint32) x6 >> 20
# asm 1: srl <x6=int64#11,20,>x6=int64#11
# asm 2: srl <x6=%o1,20,>x6=%o1
srl %o1,20,%o1

# qhasm: 		x5 |= z5
# asm 1: or  <x5=int64#10,<z5=int64#18,>x5=int64#10
# asm 2: or  <x5=%o0,<z5=%l1,>x5=%o0
or  %o0,%l1,%o0

# qhasm:                                                 z7 = (uint32) x7 << 12
# asm 1: sll <x7=int64#12,12,>z7=int64#18
# asm 2: sll <x7=%o2,12,>z7=%l1
sll %o2,12,%l1

# qhasm: 				x6 |= z6
# asm 1: or  <x6=int64#11,<z6=int64#17,>x6=int64#11
# asm 2: or  <x6=%o1,<z6=%l0,>x6=%o1
or  %o1,%l0,%o1

# qhasm: 						x7 = (uint32) x7 >> 20
# asm 1: srl <x7=int64#12,20,>x7=int64#12
# asm 2: srl <x7=%o2,20,>x7=%o2
srl %o2,20,%o2

# qhasm: x0 += x4
# asm 1: add <x0=int64#1,<x4=int64#9,>x0=int64#1
# asm 2: add <x0=%i0,<x4=%g5,>x0=%i0
add %i0,%g5,%i0

# qhasm: 						x7 |= z7
# asm 1: or  <x7=int64#12,<z7=int64#18,>x7=int64#12
# asm 2: or  <x7=%o2,<z7=%l1,>x7=%o2
or  %o2,%l1,%o2

# qhasm:                 x1 += x5
# asm 1: add <x1=int64#2,<x5=int64#10,>x1=int64#2
# asm 2: add <x1=%i1,<x5=%o0,>x1=%i1
add %i1,%o0,%i1

# qhasm: x12 ^= x0
# asm 1: xor <x12=int64#3,<x0=int64#1,>x12=int64#3
# asm 2: xor <x12=%i2,<x0=%i0,>x12=%i2
xor %i2,%i0,%i2

# qhasm:                                 x2 += x6
# asm 1: add <x2=int64#4,<x6=int64#11,>x2=int64#4
# asm 2: add <x2=%i3,<x6=%o1,>x2=%i3
add %i3,%o1,%i3

# qhasm: z12 = (uint32) x12 << 8
# asm 1: sll <x12=int64#3,8,>z12=int64#17
# asm 2: sll <x12=%i2,8,>z12=%l0
sll %i2,8,%l0

# qhasm:                 x13 ^= x1
# asm 1: xor <x13=int64#5,<x1=int64#2,>x13=int64#5
# asm 2: xor <x13=%i4,<x1=%i1,>x13=%i4
xor %i4,%i1,%i4

# qhasm: x12 = (uint32) x12 >> 24
# asm 1: srl <x12=int64#3,24,>x12=int64#3
# asm 2: srl <x12=%i2,24,>x12=%i2
srl %i2,24,%i2

# qhasm:                                 x14 ^= x2
# asm 1: xor <x14=int64#7,<x2=int64#4,>x14=int64#7
# asm 2: xor <x14=%g1,<x2=%i3,>x14=%g1
xor %g1,%i3,%g1

# qhasm:                 z13 = (uint32) x13 << 8
# asm 1: sll <x13=int64#5,8,>z13=int64#18
# asm 2: sll <x13=%i4,8,>z13=%l1
sll %i4,8,%l1

# qhasm: x12 |= z12
# asm 1: or  <x12=int64#3,<z12=int64#17,>x12=int64#3
# asm 2: or  <x12=%i2,<z12=%l0,>x12=%i2
or  %i2,%l0,%i2

# qhasm: 		x13 = (uint32) x13 >> 24
# asm 1: srl <x13=int64#5,24,>x13=int64#5
# asm 2: srl <x13=%i4,24,>x13=%i4
srl %i4,24,%i4

# qhasm:                                                 x3 += x7
# asm 1: add <x3=int64#6,<x7=int64#12,>x3=int64#6
# asm 2: add <x3=%i5,<x7=%o2,>x3=%i5
add %i5,%o2,%i5

# qhasm:                                 z14 = (uint32) x14 << 8
# asm 1: sll <x14=int64#7,8,>z14=int64#17
# asm 2: sll <x14=%g1,8,>z14=%l0
sll %g1,8,%l0

# qhasm:                                                 x15 ^= x3
# asm 1: xor <x15=int64#8,<x3=int64#6,>x15=int64#8
# asm 2: xor <x15=%g4,<x3=%i5,>x15=%g4
xor %g4,%i5,%g4

# qhasm: 				x14 = (uint32) x14 >> 24
# asm 1: srl <x14=int64#7,24,>x14=int64#7
# asm 2: srl <x14=%g1,24,>x14=%g1
srl %g1,24,%g1

# qhasm: 		x13 |= z13
# asm 1: or  <x13=int64#5,<z13=int64#18,>x13=int64#5
# asm 2: or  <x13=%i4,<z13=%l1,>x13=%i4
or  %i4,%l1,%i4

# qhasm:                                                 z15 = (uint32) x15 << 8
# asm 1: sll <x15=int64#8,8,>z15=int64#18
# asm 2: sll <x15=%g4,8,>z15=%l1
sll %g4,8,%l1

# qhasm: 				x14 |= z14
# asm 1: or  <x14=int64#7,<z14=int64#17,>x14=int64#7
# asm 2: or  <x14=%g1,<z14=%l0,>x14=%g1
or  %g1,%l0,%g1

# qhasm: 						x15 = (uint32) x15 >> 24
# asm 1: srl <x15=int64#8,24,>x15=int64#8
# asm 2: srl <x15=%g4,24,>x15=%g4
srl %g4,24,%g4

# qhasm: x8 += x12
# asm 1: add <x8=int64#13,<x12=int64#3,>x8=int64#13
# asm 2: add <x8=%o3,<x12=%i2,>x8=%o3
add %o3,%i2,%o3

# qhasm: 						x15 |= z15
# asm 1: or  <x15=int64#8,<z15=int64#18,>x15=int64#8
# asm 2: or  <x15=%g4,<z15=%l1,>x15=%g4
or  %g4,%l1,%g4

# qhasm:                 x9 += x13
# asm 1: add <x9=int64#14,<x13=int64#5,>x9=int64#14
# asm 2: add <x9=%o4,<x13=%i4,>x9=%o4
add %o4,%i4,%o4

# qhasm: x4 ^= x8
# asm 1: xor <x4=int64#9,<x8=int64#13,>x4=int64#9
# asm 2: xor <x4=%g5,<x8=%o3,>x4=%g5
xor %g5,%o3,%g5

# qhasm:                                 x10 += x14
# asm 1: add <x10=int64#15,<x14=int64#7,>x10=int64#15
# asm 2: add <x10=%o5,<x14=%g1,>x10=%o5
add %o5,%g1,%o5

# qhasm: z4 = (uint32) x4 << 7
# asm 1: sll <x4=int64#9,7,>z4=int64#17
# asm 2: sll <x4=%g5,7,>z4=%l0
sll %g5,7,%l0

# qhasm:                 x5 ^= x9
# asm 1: xor <x5=int64#10,<x9=int64#14,>x5=int64#10
# asm 2: xor <x5=%o0,<x9=%o4,>x5=%o0
xor %o0,%o4,%o0

# qhasm: x4 = (uint32) x4 >> 25
# asm 1: srl <x4=int64#9,25,>x4=int64#9
# asm 2: srl <x4=%g5,25,>x4=%g5
srl %g5,25,%g5

# qhasm:                                 x6 ^= x10
# asm 1: xor <x6=int64#11,<x10=int64#15,>x6=int64#11
# asm 2: xor <x6=%o1,<x10=%o5,>x6=%o1
xor %o1,%o5,%o1

# qhasm:                 z5 = (uint32) x5 << 7
# asm 1: sll <x5=int64#10,7,>z5=int64#18
# asm 2: sll <x5=%o0,7,>z5=%l1
sll %o0,7,%l1

# qhasm: x4 |= z4
# asm 1: or  <x4=int64#9,<z4=int64#17,>x4=int64#9
# asm 2: or  <x4=%g5,<z4=%l0,>x4=%g5
or  %g5,%l0,%g5

# qhasm: 		x5 = (uint32) x5 >> 25
# asm 1: srl <x5=int64#10,25,>x5=int64#10
# asm 2: srl <x5=%o0,25,>x5=%o0
srl %o0,25,%o0

# qhasm:                                                 x11 += x15
# asm 1: add <x11=int64#16,<x15=int64#8,>x11=int64#16
# asm 2: add <x11=%o7,<x15=%g4,>x11=%o7
add %o7,%g4,%o7

# qhasm:                                 z6 = (uint32) x6 << 7
# asm 1: sll <x6=int64#11,7,>z6=int64#17
# asm 2: sll <x6=%o1,7,>z6=%l0
sll %o1,7,%l0

# qhasm:                                                 x7 ^= x11
# asm 1: xor <x7=int64#12,<x11=int64#16,>x7=int64#12
# asm 2: xor <x7=%o2,<x11=%o7,>x7=%o2
xor %o2,%o7,%o2

# qhasm: 				x6 = (uint32) x6 >> 25
# asm 1: srl <x6=int64#11,25,>x6=int64#11
# asm 2: srl <x6=%o1,25,>x6=%o1
srl %o1,25,%o1

# qhasm: 		x5 |= z5
# asm 1: or  <x5=int64#10,<z5=int64#18,>x5=int64#10
# asm 2: or  <x5=%o0,<z5=%l1,>x5=%o0
or  %o0,%l1,%o0

# qhasm:                                                 z7 = (uint32) x7 << 7
# asm 1: sll <x7=int64#12,7,>z7=int64#18
# asm 2: sll <x7=%o2,7,>z7=%l1
sll %o2,7,%l1

# qhasm: 				x6 |= z6
# asm 1: or  <x6=int64#11,<z6=int64#17,>x6=int64#11
# asm 2: or  <x6=%o1,<z6=%l0,>x6=%o1
or  %o1,%l0,%o1

# qhasm: 						x7 = (uint32) x7 >> 25
# asm 1: srl <x7=int64#12,25,>x7=int64#12
# asm 2: srl <x7=%o2,25,>x7=%o2
srl %o2,25,%o2

# qhasm: x0 += x5
# asm 1: add <x0=int64#1,<x5=int64#10,>x0=int64#1
# asm 2: add <x0=%i0,<x5=%o0,>x0=%i0
add %i0,%o0,%i0

# qhasm: 						x7 |= z7
# asm 1: or  <x7=int64#12,<z7=int64#18,>x7=int64#12
# asm 2: or  <x7=%o2,<z7=%l1,>x7=%o2
or  %o2,%l1,%o2

# qhasm:                 x1 += x6
# asm 1: add <x1=int64#2,<x6=int64#11,>x1=int64#2
# asm 2: add <x1=%i1,<x6=%o1,>x1=%i1
add %i1,%o1,%i1

# qhasm: x15 ^= x0
# asm 1: xor <x15=int64#8,<x0=int64#1,>x15=int64#8
# asm 2: xor <x15=%g4,<x0=%i0,>x15=%g4
xor %g4,%i0,%g4

# qhasm:                                 x2 += x7
# asm 1: add <x2=int64#4,<x7=int64#12,>x2=int64#17
# asm 2: add <x2=%i3,<x7=%o2,>x2=%l0
add %i3,%o2,%l0

# qhasm: z15 = (uint32) x15 << 16
# asm 1: sll <x15=int64#8,16,>z15=int64#4
# asm 2: sll <x15=%g4,16,>z15=%i3
sll %g4,16,%i3

# qhasm:                 x12 ^= x1
# asm 1: xor <x12=int64#3,<x1=int64#2,>x12=int64#3
# asm 2: xor <x12=%i2,<x1=%i1,>x12=%i2
xor %i2,%i1,%i2

# qhasm: x15 = (uint32) x15 >> 16
# asm 1: srl <x15=int64#8,16,>x15=int64#8
# asm 2: srl <x15=%g4,16,>x15=%g4
srl %g4,16,%g4

# qhasm:                                 x13 ^= x2
# asm 1: xor <x13=int64#5,<x2=int64#17,>x13=int64#5
# asm 2: xor <x13=%i4,<x2=%l0,>x13=%i4
xor %i4,%l0,%i4

# qhasm:                 z12 = (uint32) x12 << 16
# asm 1: sll <x12=int64#3,16,>z12=int64#18
# asm 2: sll <x12=%i2,16,>z12=%l1
sll %i2,16,%l1

# qhasm: x15 |= z15
# asm 1: or  <x15=int64#8,<z15=int64#4,>x15=int64#8
# asm 2: or  <x15=%g4,<z15=%i3,>x15=%g4
or  %g4,%i3,%g4

# qhasm: 		x12 = (uint32) x12 >> 16
# asm 1: srl <x12=int64#3,16,>x12=int64#3
# asm 2: srl <x12=%i2,16,>x12=%i2
srl %i2,16,%i2

# qhasm:                                                 x3 += x4
# asm 1: add <x3=int64#6,<x4=int64#9,>x3=int64#6
# asm 2: add <x3=%i5,<x4=%g5,>x3=%i5
add %i5,%g5,%i5

# qhasm:                                 z13 = (uint32) x13 << 16
# asm 1: sll <x13=int64#5,16,>z13=int64#4
# asm 2: sll <x13=%i4,16,>z13=%i3
sll %i4,16,%i3

# qhasm:                                                 x14 ^= x3
# asm 1: xor <x14=int64#7,<x3=int64#6,>x14=int64#7
# asm 2: xor <x14=%g1,<x3=%i5,>x14=%g1
xor %g1,%i5,%g1

# qhasm: 				x13 = (uint32) x13 >> 16
# asm 1: srl <x13=int64#5,16,>x13=int64#5
# asm 2: srl <x13=%i4,16,>x13=%i4
srl %i4,16,%i4

# qhasm: 		x12 |= z12
# asm 1: or  <x12=int64#3,<z12=int64#18,>x12=int64#18
# asm 2: or  <x12=%i2,<z12=%l1,>x12=%l1
or  %i2,%l1,%l1

# qhasm:                                                 z14 = (uint32) x14 << 16
# asm 1: sll <x14=int64#7,16,>z14=int64#3
# asm 2: sll <x14=%g1,16,>z14=%i2
sll %g1,16,%i2

# qhasm: 				x13 |= z13
# asm 1: or  <x13=int64#5,<z13=int64#4,>x13=int64#5
# asm 2: or  <x13=%i4,<z13=%i3,>x13=%i4
or  %i4,%i3,%i4

# qhasm: 						x14 = (uint32) x14 >> 16
# asm 1: srl <x14=int64#7,16,>x14=int64#4
# asm 2: srl <x14=%g1,16,>x14=%i3
srl %g1,16,%i3

# qhasm: x10 += x15
# asm 1: add <x10=int64#15,<x15=int64#8,>x10=int64#15
# asm 2: add <x10=%o5,<x15=%g4,>x10=%o5
add %o5,%g4,%o5

# qhasm: 						x14 |= z14
# asm 1: or  <x14=int64#4,<z14=int64#3,>x14=int64#19
# asm 2: or  <x14=%i3,<z14=%i2,>x14=%l2
or  %i3,%i2,%l2

# qhasm:                 x11 += x12
# asm 1: add <x11=int64#16,<x12=int64#18,>x11=int64#16
# asm 2: add <x11=%o7,<x12=%l1,>x11=%o7
add %o7,%l1,%o7

# qhasm: x5 ^= x10
# asm 1: xor <x5=int64#10,<x10=int64#15,>x5=int64#3
# asm 2: xor <x5=%o0,<x10=%o5,>x5=%i2
xor %o0,%o5,%i2

# qhasm:                                 x8 += x13
# asm 1: add <x8=int64#13,<x13=int64#5,>x8=int64#10
# asm 2: add <x8=%o3,<x13=%i4,>x8=%o0
add %o3,%i4,%o0

# qhasm: z5 = (uint32) x5 << 12
# asm 1: sll <x5=int64#3,12,>z5=int64#4
# asm 2: sll <x5=%i2,12,>z5=%i3
sll %i2,12,%i3

# qhasm:                 x6 ^= x11
# asm 1: xor <x6=int64#11,<x11=int64#16,>x6=int64#7
# asm 2: xor <x6=%o1,<x11=%o7,>x6=%g1
xor %o1,%o7,%g1

# qhasm: x5 = (uint32) x5 >> 20
# asm 1: srl <x5=int64#3,20,>x5=int64#3
# asm 2: srl <x5=%i2,20,>x5=%i2
srl %i2,20,%i2

# qhasm:                                 x7 ^= x8
# asm 1: xor <x7=int64#12,<x8=int64#10,>x7=int64#11
# asm 2: xor <x7=%o2,<x8=%o0,>x7=%o1
xor %o2,%o0,%o1

# qhasm:                 z6 = (uint32) x6 << 12
# asm 1: sll <x6=int64#7,12,>z6=int64#12
# asm 2: sll <x6=%g1,12,>z6=%o2
sll %g1,12,%o2

# qhasm: x5 |= z5
# asm 1: or  <x5=int64#3,<z5=int64#4,>x5=int64#13
# asm 2: or  <x5=%i2,<z5=%i3,>x5=%o3
or  %i2,%i3,%o3

# qhasm: 		x6 = (uint32) x6 >> 20
# asm 1: srl <x6=int64#7,20,>x6=int64#3
# asm 2: srl <x6=%g1,20,>x6=%i2
srl %g1,20,%i2

# qhasm:                                                 x9 += x14
# asm 1: add <x9=int64#14,<x14=int64#19,>x9=int64#14
# asm 2: add <x9=%o4,<x14=%l2,>x9=%o4
add %o4,%l2,%o4

# qhasm:                                 z7 = (uint32) x7 << 12
# asm 1: sll <x7=int64#11,12,>z7=int64#4
# asm 2: sll <x7=%o1,12,>z7=%i3
sll %o1,12,%i3

# qhasm:                                                 x4 ^= x9
# asm 1: xor <x4=int64#9,<x9=int64#14,>x4=int64#7
# asm 2: xor <x4=%g5,<x9=%o4,>x4=%g1
xor %g5,%o4,%g1

# qhasm: 				x7 = (uint32) x7 >> 20
# asm 1: srl <x7=int64#11,20,>x7=int64#9
# asm 2: srl <x7=%o1,20,>x7=%g5
srl %o1,20,%g5

# qhasm: 		x6 |= z6
# asm 1: or  <x6=int64#3,<z6=int64#12,>x6=int64#11
# asm 2: or  <x6=%i2,<z6=%o2,>x6=%o1
or  %i2,%o2,%o1

# qhasm:                                                 z4 = (uint32) x4 << 12
# asm 1: sll <x4=int64#7,12,>z4=int64#12
# asm 2: sll <x4=%g1,12,>z4=%o2
sll %g1,12,%o2

# qhasm: 				x7 |= z7
# asm 1: or  <x7=int64#9,<z7=int64#4,>x7=int64#9
# asm 2: or  <x7=%g5,<z7=%i3,>x7=%g5
or  %g5,%i3,%g5

# qhasm: 						x4 = (uint32) x4 >> 20
# asm 1: srl <x4=int64#7,20,>x4=int64#4
# asm 2: srl <x4=%g1,20,>x4=%i3
srl %g1,20,%i3

# qhasm: x0 += x5
# asm 1: add <x0=int64#1,<x5=int64#13,>x0=int64#3
# asm 2: add <x0=%i0,<x5=%o3,>x0=%i2
add %i0,%o3,%i2

# qhasm: 						x4 |= z4
# asm 1: or  <x4=int64#4,<z4=int64#12,>x4=int64#1
# asm 2: or  <x4=%i3,<z4=%o2,>x4=%i0
or  %i3,%o2,%i0

# qhasm:                 x1 += x6
# asm 1: add <x1=int64#2,<x6=int64#11,>x1=int64#4
# asm 2: add <x1=%i1,<x6=%o1,>x1=%i3
add %i1,%o1,%i3

# qhasm: x15 ^= x0
# asm 1: xor <x15=int64#8,<x0=int64#3,>x15=int64#2
# asm 2: xor <x15=%g4,<x0=%i2,>x15=%i1
xor %g4,%i2,%i1

# qhasm:                                 x2 += x7
# asm 1: add <x2=int64#17,<x7=int64#9,>x2=int64#7
# asm 2: add <x2=%l0,<x7=%g5,>x2=%g1
add %l0,%g5,%g1

# qhasm: z15 = (uint32) x15 << 8
# asm 1: sll <x15=int64#2,8,>z15=int64#8
# asm 2: sll <x15=%i1,8,>z15=%g4
sll %i1,8,%g4

# qhasm:                 x12 ^= x1
# asm 1: xor <x12=int64#18,<x1=int64#4,>x12=int64#12
# asm 2: xor <x12=%l1,<x1=%i3,>x12=%o2
xor %l1,%i3,%o2

# qhasm: x15 = (uint32) x15 >> 24
# asm 1: srl <x15=int64#2,24,>x15=int64#2
# asm 2: srl <x15=%i1,24,>x15=%i1
srl %i1,24,%i1

# qhasm:                                 x13 ^= x2
# asm 1: xor <x13=int64#5,<x2=int64#7,>x13=int64#5
# asm 2: xor <x13=%i4,<x2=%g1,>x13=%i4
xor %i4,%g1,%i4

# qhasm:                 z12 = (uint32) x12 << 8
# asm 1: sll <x12=int64#12,8,>z12=int64#17
# asm 2: sll <x12=%o2,8,>z12=%l0
sll %o2,8,%l0

# qhasm: x15 |= z15
# asm 1: or  <x15=int64#2,<z15=int64#8,>x15=int64#20
# asm 2: or  <x15=%i1,<z15=%g4,>x15=%l3
or  %i1,%g4,%l3

# qhasm: 		x12 = (uint32) x12 >> 24
# asm 1: srl <x12=int64#12,24,>x12=int64#2
# asm 2: srl <x12=%o2,24,>x12=%i1
srl %o2,24,%i1

# qhasm:                                                 x3 += x4
# asm 1: add <x3=int64#6,<x4=int64#1,>x3=int64#8
# asm 2: add <x3=%i5,<x4=%i0,>x3=%g4
add %i5,%i0,%g4

# qhasm:                                 z13 = (uint32) x13 << 8
# asm 1: sll <x13=int64#5,8,>z13=int64#6
# asm 2: sll <x13=%i4,8,>z13=%i5
sll %i4,8,%i5

# qhasm:                                                 x14 ^= x3
# asm 1: xor <x14=int64#19,<x3=int64#8,>x14=int64#12
# asm 2: xor <x14=%l2,<x3=%g4,>x14=%o2
xor %l2,%g4,%o2

# qhasm: 				x13 = (uint32) x13 >> 24
# asm 1: srl <x13=int64#5,24,>x13=int64#5
# asm 2: srl <x13=%i4,24,>x13=%i4
srl %i4,24,%i4

# qhasm: 		x12 |= z12
# asm 1: or  <x12=int64#2,<z12=int64#17,>x12=int64#17
# asm 2: or  <x12=%i1,<z12=%l0,>x12=%l0
or  %i1,%l0,%l0

# qhasm:                                                 z14 = (uint32) x14 << 8
# asm 1: sll <x14=int64#12,8,>z14=int64#2
# asm 2: sll <x14=%o2,8,>z14=%i1
sll %o2,8,%i1

# qhasm: 				x13 |= z13
# asm 1: or  <x13=int64#5,<z13=int64#6,>x13=int64#18
# asm 2: or  <x13=%i4,<z13=%i5,>x13=%l1
or  %i4,%i5,%l1

# qhasm: 						x14 = (uint32) x14 >> 24
# asm 1: srl <x14=int64#12,24,>x14=int64#5
# asm 2: srl <x14=%o2,24,>x14=%i4
srl %o2,24,%i4

# qhasm: x10 += x15
# asm 1: add <x10=int64#15,<x15=int64#20,>x10=int64#15
# asm 2: add <x10=%o5,<x15=%l3,>x10=%o5
add %o5,%l3,%o5

# qhasm: 						x14 |= z14
# asm 1: or  <x14=int64#5,<z14=int64#2,>x14=int64#19
# asm 2: or  <x14=%i4,<z14=%i1,>x14=%l2
or  %i4,%i1,%l2

# qhasm:                 x11 += x12
# asm 1: add <x11=int64#16,<x12=int64#17,>x11=int64#16
# asm 2: add <x11=%o7,<x12=%l0,>x11=%o7
add %o7,%l0,%o7

# qhasm: x5 ^= x10
# asm 1: xor <x5=int64#13,<x10=int64#15,>x5=int64#2
# asm 2: xor <x5=%o3,<x10=%o5,>x5=%i1
xor %o3,%o5,%i1

# qhasm:                                 x8 += x13
# asm 1: add <x8=int64#10,<x13=int64#18,>x8=int64#13
# asm 2: add <x8=%o0,<x13=%l1,>x8=%o3
add %o0,%l1,%o3

# qhasm: z5 = (uint32) x5 << 7
# asm 1: sll <x5=int64#2,7,>z5=int64#5
# asm 2: sll <x5=%i1,7,>z5=%i4
sll %i1,7,%i4

# qhasm:                 x6 ^= x11
# asm 1: xor <x6=int64#11,<x11=int64#16,>x6=int64#6
# asm 2: xor <x6=%o1,<x11=%o7,>x6=%i5
xor %o1,%o7,%i5

# qhasm: x5 = (uint32) x5 >> 25
# asm 1: srl <x5=int64#2,25,>x5=int64#2
# asm 2: srl <x5=%i1,25,>x5=%i1
srl %i1,25,%i1

# qhasm:                                 x7 ^= x8
# asm 1: xor <x7=int64#9,<x8=int64#13,>x7=int64#9
# asm 2: xor <x7=%g5,<x8=%o3,>x7=%g5
xor %g5,%o3,%g5

# qhasm:                 z6 = (uint32) x6 << 7
# asm 1: sll <x6=int64#6,7,>z6=int64#11
# asm 2: sll <x6=%i5,7,>z6=%o1
sll %i5,7,%o1

# qhasm: x5 |= z5
# asm 1: or  <x5=int64#2,<z5=int64#5,>x5=int64#10
# asm 2: or  <x5=%i1,<z5=%i4,>x5=%o0
or  %i1,%i4,%o0

# qhasm: 		x6 = (uint32) x6 >> 25
# asm 1: srl <x6=int64#6,25,>x6=int64#2
# asm 2: srl <x6=%i5,25,>x6=%i1
srl %i5,25,%i1

# qhasm:                                                 x9 += x14
# asm 1: add <x9=int64#14,<x14=int64#19,>x9=int64#14
# asm 2: add <x9=%o4,<x14=%l2,>x9=%o4
add %o4,%l2,%o4

# qhasm:                                 z7 = (uint32) x7 << 7
# asm 1: sll <x7=int64#9,7,>z7=int64#5
# asm 2: sll <x7=%g5,7,>z7=%i4
sll %g5,7,%i4

# qhasm:                                                 x4 ^= x9
# asm 1: xor <x4=int64#1,<x9=int64#14,>x4=int64#1
# asm 2: xor <x4=%i0,<x9=%o4,>x4=%i0
xor %i0,%o4,%i0

# qhasm: 				x7 = (uint32) x7 >> 25
# asm 1: srl <x7=int64#9,25,>x7=int64#6
# asm 2: srl <x7=%g5,25,>x7=%i5
srl %g5,25,%i5

# qhasm: 		x6 |= z6
# asm 1: or  <x6=int64#2,<z6=int64#11,>x6=int64#11
# asm 2: or  <x6=%i1,<z6=%o1,>x6=%o1
or  %i1,%o1,%o1

# qhasm:                                                 z4 = (uint32) x4 << 7
# asm 1: sll <x4=int64#1,7,>z4=int64#2
# asm 2: sll <x4=%i0,7,>z4=%i1
sll %i0,7,%i1

# qhasm: 				x7 |= z7
# asm 1: or  <x7=int64#6,<z7=int64#5,>x7=int64#12
# asm 2: or  <x7=%i5,<z7=%i4,>x7=%o2
or  %i5,%i4,%o2

# qhasm: 						x4 = (uint32) x4 >> 25
# asm 1: srl <x4=int64#1,25,>x4=int64#1
# asm 2: srl <x4=%i0,25,>x4=%i0
srl %i0,25,%i0

# qhasm:                  unsigned>? i -= 2
# asm 1: subcc <i=int64#21,2,>i=int64#21
# asm 2: subcc <i=%l4,2,>i=%l4
subcc %l4,2,%l4

# qhasm: 						x4 |= z4
# asm 1: or  <x4=int64#1,<z4=int64#2,>x4=int64#9
# asm 2: or  <x4=%i0,<z4=%i1,>x4=%g5
or  %i0,%i1,%g5

# qhasm: goto mainloop if unsigned>
bgu,pt %xcc,._mainloop
nop

# qhasm:   x = x_stack
# asm 1: ldx [%fp+2023-<x_stack=stack64#5],>x=int64#1
# asm 2: ldx [%fp+2023-<x_stack=32],>x=%i0
ldx [%fp+2023-32],%i0

# qhasm:   q0 = *(uint32 *) (x + 0)
# asm 1: lduw [<x=int64#1+0],>q0=int64#2
# asm 2: lduw [<x=%i0+0],>q0=%i1
lduw [%i0+0],%i1

# qhasm:   q1 = *(uint32 *) (x + 4)
# asm 1: lduw [<x=int64#1+4],>q1=int64#5
# asm 2: lduw [<x=%i0+4],>q1=%i4
lduw [%i0+4],%i4

# qhasm:   q2 = *(uint32 *) (x + 8)
# asm 1: lduw [<x=int64#1+8],>q2=int64#6
# asm 2: lduw [<x=%i0+8],>q2=%i5
lduw [%i0+8],%i5

# qhasm:   q3 = *(uint32 *) (x + 12)
# asm 1: lduw [<x=int64#1+12],>q3=int64#21
# asm 2: lduw [<x=%i0+12],>q3=%l4
lduw [%i0+12],%l4

# qhasm:   x0 += q0
# asm 1: add <x0=int64#3,<q0=int64#2,>x0=int64#2
# asm 2: add <x0=%i2,<q0=%i1,>x0=%i1
add %i2,%i1,%i1

# qhasm:   q4 = *(uint32 *) (x + 16)
# asm 1: lduw [<x=int64#1+16],>q4=int64#3
# asm 2: lduw [<x=%i0+16],>q4=%i2
lduw [%i0+16],%i2

# qhasm:   x1 += q1
# asm 1: add <x1=int64#4,<q1=int64#5,>x1=int64#4
# asm 2: add <x1=%i3,<q1=%i4,>x1=%i3
add %i3,%i4,%i3

# qhasm:   q5 = *(uint32 *) (x + 20)
# asm 1: lduw [<x=int64#1+20],>q5=int64#5
# asm 2: lduw [<x=%i0+20],>q5=%i4
lduw [%i0+20],%i4

# qhasm:   x2 += q2
# asm 1: add <x2=int64#7,<q2=int64#6,>x2=int64#6
# asm 2: add <x2=%g1,<q2=%i5,>x2=%i5
add %g1,%i5,%i5

# qhasm:   q6 = *(uint32 *) (x + 24)
# asm 1: lduw [<x=int64#1+24],>q6=int64#7
# asm 2: lduw [<x=%i0+24],>q6=%g1
lduw [%i0+24],%g1

# qhasm:   x3 += q3
# asm 1: add <x3=int64#8,<q3=int64#21,>x3=int64#8
# asm 2: add <x3=%g4,<q3=%l4,>x3=%g4
add %g4,%l4,%g4

# qhasm:   q7 = *(uint32 *) (x + 28)
# asm 1: lduw [<x=int64#1+28],>q7=int64#21
# asm 2: lduw [<x=%i0+28],>q7=%l4
lduw [%i0+28],%l4

# qhasm:   x4 += q4
# asm 1: add <x4=int64#9,<q4=int64#3,>x4=int64#3
# asm 2: add <x4=%g5,<q4=%i2,>x4=%i2
add %g5,%i2,%i2

# qhasm:   q8 = *(uint32 *) (x + 32)
# asm 1: lduw [<x=int64#1+32],>q8=int64#9
# asm 2: lduw [<x=%i0+32],>q8=%g5
lduw [%i0+32],%g5

# qhasm:   x5 += q5
# asm 1: add <x5=int64#10,<q5=int64#5,>x5=int64#5
# asm 2: add <x5=%o0,<q5=%i4,>x5=%i4
add %o0,%i4,%i4

# qhasm:   q9 = *(uint32 *) (x + 36)
# asm 1: lduw [<x=int64#1+36],>q9=int64#10
# asm 2: lduw [<x=%i0+36],>q9=%o0
lduw [%i0+36],%o0

# qhasm:   x6 += q6
# asm 1: add <x6=int64#11,<q6=int64#7,>x6=int64#7
# asm 2: add <x6=%o1,<q6=%g1,>x6=%g1
add %o1,%g1,%g1

# qhasm:   q10 = *(uint32 *) (x + 40)
# asm 1: lduw [<x=int64#1+40],>q10=int64#11
# asm 2: lduw [<x=%i0+40],>q10=%o1
lduw [%i0+40],%o1

# qhasm:   x7 += q7
# asm 1: add <x7=int64#12,<q7=int64#21,>x7=int64#12
# asm 2: add <x7=%o2,<q7=%l4,>x7=%o2
add %o2,%l4,%o2

# qhasm:   q11 = *(uint32 *) (x + 44)
# asm 1: lduw [<x=int64#1+44],>q11=int64#21
# asm 2: lduw [<x=%i0+44],>q11=%l4
lduw [%i0+44],%l4

# qhasm:   x8 += q8
# asm 1: add <x8=int64#13,<q8=int64#9,>x8=int64#9
# asm 2: add <x8=%o3,<q8=%g5,>x8=%g5
add %o3,%g5,%g5

# qhasm:   q12 = *(uint32 *) (x + 48)
# asm 1: lduw [<x=int64#1+48],>q12=int64#13
# asm 2: lduw [<x=%i0+48],>q12=%o3
lduw [%i0+48],%o3

# qhasm:   x9 += q9
# asm 1: add <x9=int64#14,<q9=int64#10,>x9=int64#10
# asm 2: add <x9=%o4,<q9=%o0,>x9=%o0
add %o4,%o0,%o0

# qhasm:   q13 = *(uint32 *) (x + 52)
# asm 1: lduw [<x=int64#1+52],>q13=int64#14
# asm 2: lduw [<x=%i0+52],>q13=%o4
lduw [%i0+52],%o4

# qhasm:   x10 += q10
# asm 1: add <x10=int64#15,<q10=int64#11,>x10=int64#11
# asm 2: add <x10=%o5,<q10=%o1,>x10=%o1
add %o5,%o1,%o1

# qhasm:   q14 = *(uint32 *) (x + 56)
# asm 1: lduw [<x=int64#1+56],>q14=int64#15
# asm 2: lduw [<x=%i0+56],>q14=%o5
lduw [%i0+56],%o5

# qhasm:   x11 += q11
# asm 1: add <x11=int64#16,<q11=int64#21,>x11=int64#16
# asm 2: add <x11=%o7,<q11=%l4,>x11=%o7
add %o7,%l4,%o7

# qhasm:   q15 = *(uint32 *) (x + 60)
# asm 1: lduw [<x=int64#1+60],>q15=int64#21
# asm 2: lduw [<x=%i0+60],>q15=%l4
lduw [%i0+60],%l4

# qhasm:   x12 += q12
# asm 1: add <x12=int64#17,<q12=int64#13,>x12=int64#17
# asm 2: add <x12=%l0,<q12=%o3,>x12=%l0
add %l0,%o3,%l0

# qhasm:   q12 += 1
# asm 1: add <q12=int64#13,1,>q12=int64#13
# asm 2: add <q12=%o3,1,>q12=%o3
add %o3,1,%o3

# qhasm:   *(uint32 *) (x + 48) = q12
# asm 1: stw <q12=int64#13,[<x=int64#1+48]
# asm 2: stw <q12=%o3,[<x=%i0+48]
stw %o3,[%i0+48]

# qhasm:   q12 = (uint64) q12 >> 32
# asm 1: srlx <q12=int64#13,32,>q12=int64#13
# asm 2: srlx <q12=%o3,32,>q12=%o3
srlx %o3,32,%o3

# qhasm:   x13 += q13
# asm 1: add <x13=int64#18,<q13=int64#14,>x13=int64#18
# asm 2: add <x13=%l1,<q13=%o4,>x13=%l1
add %l1,%o4,%l1

# qhasm:   q13 += q12
# asm 1: add <q13=int64#14,<q12=int64#13,>q13=int64#13
# asm 2: add <q13=%o4,<q12=%o3,>q13=%o3
add %o4,%o3,%o3

# qhasm:   *(uint32 *) (x + 52) = q13
# asm 1: stw <q13=int64#13,[<x=int64#1+52]
# asm 2: stw <q13=%o3,[<x=%i0+52]
stw %o3,[%i0+52]

# qhasm:   x14 += q14
# asm 1: add <x14=int64#19,<q14=int64#15,>x14=int64#13
# asm 2: add <x14=%l2,<q14=%o5,>x14=%o3
add %l2,%o5,%o3

# qhasm:   x15 += q15
# asm 1: add <x15=int64#20,<q15=int64#21,>x15=int64#14
# asm 2: add <x15=%l3,<q15=%l4,>x15=%o4
add %l3,%l4,%o4

# qhasm:   m = m_stack
# asm 1: ldx [%fp+2023-<m_stack=stack64#4],>m=int64#15
# asm 2: ldx [%fp+2023-<m_stack=24],>m=%o5
ldx [%fp+2023-24],%o5

# qhasm:   m0 = *(swapendian uint32 *) m
# asm 1: lduwa [<m=int64#15] 0x88,>m0=int64#19
# asm 2: lduwa [<m=%o5] 0x88,>m0=%l2
lduwa [%o5] 0x88,%l2

# qhasm:   m += 4
# asm 1: add <m=int64#15,4,>m=int64#15
# asm 2: add <m=%o5,4,>m=%o5
add %o5,4,%o5

# qhasm:   m1 = *(swapendian uint32 *) m
# asm 1: lduwa [<m=int64#15] 0x88,>m1=int64#20
# asm 2: lduwa [<m=%o5] 0x88,>m1=%l3
lduwa [%o5] 0x88,%l3

# qhasm:   m += 4
# asm 1: add <m=int64#15,4,>m=int64#15
# asm 2: add <m=%o5,4,>m=%o5
add %o5,4,%o5

# qhasm:   m2 = *(swapendian uint32 *) m
# asm 1: lduwa [<m=int64#15] 0x88,>m2=int64#21
# asm 2: lduwa [<m=%o5] 0x88,>m2=%l4
lduwa [%o5] 0x88,%l4

# qhasm:   m += 4
# asm 1: add <m=int64#15,4,>m=int64#15
# asm 2: add <m=%o5,4,>m=%o5
add %o5,4,%o5

# qhasm:   m3 = *(swapendian uint32 *) m
# asm 1: lduwa [<m=int64#15] 0x88,>m3=int64#22
# asm 2: lduwa [<m=%o5] 0x88,>m3=%l5
lduwa [%o5] 0x88,%l5

# qhasm:   m += 4
# asm 1: add <m=int64#15,4,>m=int64#15
# asm 2: add <m=%o5,4,>m=%o5
add %o5,4,%o5

# qhasm:   x0 ^= m0
# asm 1: xor <x0=int64#2,<m0=int64#19,>x0=int64#2
# asm 2: xor <x0=%i1,<m0=%l2,>x0=%i1
xor %i1,%l2,%i1

# qhasm:   m4 = *(swapendian uint32 *) m
# asm 1: lduwa [<m=int64#15] 0x88,>m4=int64#19
# asm 2: lduwa [<m=%o5] 0x88,>m4=%l2
lduwa [%o5] 0x88,%l2

# qhasm:   m += 4
# asm 1: add <m=int64#15,4,>m=int64#15
# asm 2: add <m=%o5,4,>m=%o5
add %o5,4,%o5

# qhasm:   x1 ^= m1
# asm 1: xor <x1=int64#4,<m1=int64#20,>x1=int64#4
# asm 2: xor <x1=%i3,<m1=%l3,>x1=%i3
xor %i3,%l3,%i3

# qhasm:   m5 = *(swapendian uint32 *) m
# asm 1: lduwa [<m=int64#15] 0x88,>m5=int64#20
# asm 2: lduwa [<m=%o5] 0x88,>m5=%l3
lduwa [%o5] 0x88,%l3

# qhasm:   m += 4
# asm 1: add <m=int64#15,4,>m=int64#15
# asm 2: add <m=%o5,4,>m=%o5
add %o5,4,%o5

# qhasm:   x2 ^= m2
# asm 1: xor <x2=int64#6,<m2=int64#21,>x2=int64#21
# asm 2: xor <x2=%i5,<m2=%l4,>x2=%l4
xor %i5,%l4,%l4

# qhasm:   m6 = *(swapendian uint32 *) m
# asm 1: lduwa [<m=int64#15] 0x88,>m6=int64#6
# asm 2: lduwa [<m=%o5] 0x88,>m6=%i5
lduwa [%o5] 0x88,%i5

# qhasm:   m += 4
# asm 1: add <m=int64#15,4,>m=int64#15
# asm 2: add <m=%o5,4,>m=%o5
add %o5,4,%o5

# qhasm:   x3 ^= m3
# asm 1: xor <x3=int64#8,<m3=int64#22,>x3=int64#8
# asm 2: xor <x3=%g4,<m3=%l5,>x3=%g4
xor %g4,%l5,%g4

# qhasm:   m7 = *(swapendian uint32 *) m
# asm 1: lduwa [<m=int64#15] 0x88,>m7=int64#22
# asm 2: lduwa [<m=%o5] 0x88,>m7=%l5
lduwa [%o5] 0x88,%l5

# qhasm:   m += 4
# asm 1: add <m=int64#15,4,>m=int64#15
# asm 2: add <m=%o5,4,>m=%o5
add %o5,4,%o5

# qhasm:   x4 ^= m4
# asm 1: xor <x4=int64#3,<m4=int64#19,>x4=int64#3
# asm 2: xor <x4=%i2,<m4=%l2,>x4=%i2
xor %i2,%l2,%i2

# qhasm:   m8 = *(swapendian uint32 *) m
# asm 1: lduwa [<m=int64#15] 0x88,>m8=int64#19
# asm 2: lduwa [<m=%o5] 0x88,>m8=%l2
lduwa [%o5] 0x88,%l2

# qhasm:   m += 4
# asm 1: add <m=int64#15,4,>m=int64#15
# asm 2: add <m=%o5,4,>m=%o5
add %o5,4,%o5

# qhasm:   x5 ^= m5
# asm 1: xor <x5=int64#5,<m5=int64#20,>x5=int64#5
# asm 2: xor <x5=%i4,<m5=%l3,>x5=%i4
xor %i4,%l3,%i4

# qhasm:   m9 = *(swapendian uint32 *) m
# asm 1: lduwa [<m=int64#15] 0x88,>m9=int64#20
# asm 2: lduwa [<m=%o5] 0x88,>m9=%l3
lduwa [%o5] 0x88,%l3

# qhasm:   m += 4
# asm 1: add <m=int64#15,4,>m=int64#15
# asm 2: add <m=%o5,4,>m=%o5
add %o5,4,%o5

# qhasm:   x6 ^= m6
# asm 1: xor <x6=int64#7,<m6=int64#6,>x6=int64#7
# asm 2: xor <x6=%g1,<m6=%i5,>x6=%g1
xor %g1,%i5,%g1

# qhasm:   m10 = *(swapendian uint32 *) m
# asm 1: lduwa [<m=int64#15] 0x88,>m10=int64#6
# asm 2: lduwa [<m=%o5] 0x88,>m10=%i5
lduwa [%o5] 0x88,%i5

# qhasm:   m += 4
# asm 1: add <m=int64#15,4,>m=int64#15
# asm 2: add <m=%o5,4,>m=%o5
add %o5,4,%o5

# qhasm:   x7 ^= m7
# asm 1: xor <x7=int64#12,<m7=int64#22,>x7=int64#12
# asm 2: xor <x7=%o2,<m7=%l5,>x7=%o2
xor %o2,%l5,%o2

# qhasm:   m11 = *(swapendian uint32 *) m
# asm 1: lduwa [<m=int64#15] 0x88,>m11=int64#22
# asm 2: lduwa [<m=%o5] 0x88,>m11=%l5
lduwa [%o5] 0x88,%l5

# qhasm:   m += 4
# asm 1: add <m=int64#15,4,>m=int64#15
# asm 2: add <m=%o5,4,>m=%o5
add %o5,4,%o5

# qhasm:   x8 ^= m8
# asm 1: xor <x8=int64#9,<m8=int64#19,>x8=int64#9
# asm 2: xor <x8=%g5,<m8=%l2,>x8=%g5
xor %g5,%l2,%g5

# qhasm:   m12 = *(swapendian uint32 *) m
# asm 1: lduwa [<m=int64#15] 0x88,>m12=int64#19
# asm 2: lduwa [<m=%o5] 0x88,>m12=%l2
lduwa [%o5] 0x88,%l2

# qhasm:   m += 4
# asm 1: add <m=int64#15,4,>m=int64#15
# asm 2: add <m=%o5,4,>m=%o5
add %o5,4,%o5

# qhasm:   x9 ^= m9
# asm 1: xor <x9=int64#10,<m9=int64#20,>x9=int64#10
# asm 2: xor <x9=%o0,<m9=%l3,>x9=%o0
xor %o0,%l3,%o0

# qhasm:   m13 = *(swapendian uint32 *) m
# asm 1: lduwa [<m=int64#15] 0x88,>m13=int64#20
# asm 2: lduwa [<m=%o5] 0x88,>m13=%l3
lduwa [%o5] 0x88,%l3

# qhasm:   m += 4
# asm 1: add <m=int64#15,4,>m=int64#15
# asm 2: add <m=%o5,4,>m=%o5
add %o5,4,%o5

# qhasm:   x10 ^= m10
# asm 1: xor <x10=int64#11,<m10=int64#6,>x10=int64#11
# asm 2: xor <x10=%o1,<m10=%i5,>x10=%o1
xor %o1,%i5,%o1

# qhasm:   m14 = *(swapendian uint32 *) m
# asm 1: lduwa [<m=int64#15] 0x88,>m14=int64#23
# asm 2: lduwa [<m=%o5] 0x88,>m14=%l6
lduwa [%o5] 0x88,%l6

# qhasm:   m += 4
# asm 1: add <m=int64#15,4,>m=int64#6
# asm 2: add <m=%o5,4,>m=%i5
add %o5,4,%i5

# qhasm:   x11 ^= m11
# asm 1: xor <x11=int64#16,<m11=int64#22,>x11=int64#15
# asm 2: xor <x11=%o7,<m11=%l5,>x11=%o5
xor %o7,%l5,%o5

# qhasm:   m15 = *(swapendian uint32 *) m
# asm 1: lduwa [<m=int64#6] 0x88,>m15=int64#16
# asm 2: lduwa [<m=%i5] 0x88,>m15=%o7
lduwa [%i5] 0x88,%o7

# qhasm:   m += 4
# asm 1: add <m=int64#6,4,>m=int64#6
# asm 2: add <m=%i5,4,>m=%i5
add %i5,4,%i5

# qhasm:   x12 ^= m12
# asm 1: xor <x12=int64#17,<m12=int64#19,>x12=int64#17
# asm 2: xor <x12=%l0,<m12=%l2,>x12=%l0
xor %l0,%l2,%l0

# qhasm:   x13 ^= m13
# asm 1: xor <x13=int64#18,<m13=int64#20,>x13=int64#18
# asm 2: xor <x13=%l1,<m13=%l3,>x13=%l1
xor %l1,%l3,%l1

# qhasm:   x14 ^= m14
# asm 1: xor <x14=int64#13,<m14=int64#23,>x14=int64#13
# asm 2: xor <x14=%o3,<m14=%l6,>x14=%o3
xor %o3,%l6,%o3

# qhasm:   x15 ^= m15
# asm 1: xor <x15=int64#14,<m15=int64#16,>x15=int64#14
# asm 2: xor <x15=%o4,<m15=%o7,>x15=%o4
xor %o4,%o7,%o4

# qhasm:   out = out_stack
# asm 1: ldx [%fp+2023-<out_stack=stack64#3],>out=int64#16
# asm 2: ldx [%fp+2023-<out_stack=16],>out=%o7
ldx [%fp+2023-16],%o7

# qhasm:   *(swapendian uint32 *) out = x0
# asm 1: stwa <x0=int64#2,[<out=int64#16] 0x88
# asm 2: stwa <x0=%i1,[<out=%o7] 0x88
stwa %i1,[%o7] 0x88

# qhasm:   out += 4
# asm 1: add <out=int64#16,4,>out=int64#2
# asm 2: add <out=%o7,4,>out=%i1
add %o7,4,%i1

# qhasm:   *(swapendian uint32 *) out = x1
# asm 1: stwa <x1=int64#4,[<out=int64#2] 0x88
# asm 2: stwa <x1=%i3,[<out=%i1] 0x88
stwa %i3,[%i1] 0x88

# qhasm:   out += 4
# asm 1: add <out=int64#2,4,>out=int64#2
# asm 2: add <out=%i1,4,>out=%i1
add %i1,4,%i1

# qhasm:   *(swapendian uint32 *) out = x2
# asm 1: stwa <x2=int64#21,[<out=int64#2] 0x88
# asm 2: stwa <x2=%l4,[<out=%i1] 0x88
stwa %l4,[%i1] 0x88

# qhasm:   out += 4
# asm 1: add <out=int64#2,4,>out=int64#2
# asm 2: add <out=%i1,4,>out=%i1
add %i1,4,%i1

# qhasm:   *(swapendian uint32 *) out = x3
# asm 1: stwa <x3=int64#8,[<out=int64#2] 0x88
# asm 2: stwa <x3=%g4,[<out=%i1] 0x88
stwa %g4,[%i1] 0x88

# qhasm:   out += 4
# asm 1: add <out=int64#2,4,>out=int64#2
# asm 2: add <out=%i1,4,>out=%i1
add %i1,4,%i1

# qhasm:   *(swapendian uint32 *) out = x4
# asm 1: stwa <x4=int64#3,[<out=int64#2] 0x88
# asm 2: stwa <x4=%i2,[<out=%i1] 0x88
stwa %i2,[%i1] 0x88

# qhasm:   out += 4
# asm 1: add <out=int64#2,4,>out=int64#2
# asm 2: add <out=%i1,4,>out=%i1
add %i1,4,%i1

# qhasm:   *(swapendian uint32 *) out = x5
# asm 1: stwa <x5=int64#5,[<out=int64#2] 0x88
# asm 2: stwa <x5=%i4,[<out=%i1] 0x88
stwa %i4,[%i1] 0x88

# qhasm:   out += 4
# asm 1: add <out=int64#2,4,>out=int64#2
# asm 2: add <out=%i1,4,>out=%i1
add %i1,4,%i1

# qhasm:   *(swapendian uint32 *) out = x6
# asm 1: stwa <x6=int64#7,[<out=int64#2] 0x88
# asm 2: stwa <x6=%g1,[<out=%i1] 0x88
stwa %g1,[%i1] 0x88

# qhasm:   out += 4
# asm 1: add <out=int64#2,4,>out=int64#2
# asm 2: add <out=%i1,4,>out=%i1
add %i1,4,%i1

# qhasm:   *(swapendian uint32 *) out = x7
# asm 1: stwa <x7=int64#12,[<out=int64#2] 0x88
# asm 2: stwa <x7=%o2,[<out=%i1] 0x88
stwa %o2,[%i1] 0x88

# qhasm:   out += 4
# asm 1: add <out=int64#2,4,>out=int64#2
# asm 2: add <out=%i1,4,>out=%i1
add %i1,4,%i1

# qhasm:   *(swapendian uint32 *) out = x8
# asm 1: stwa <x8=int64#9,[<out=int64#2] 0x88
# asm 2: stwa <x8=%g5,[<out=%i1] 0x88
stwa %g5,[%i1] 0x88

# qhasm:   out += 4
# asm 1: add <out=int64#2,4,>out=int64#2
# asm 2: add <out=%i1,4,>out=%i1
add %i1,4,%i1

# qhasm:   *(swapendian uint32 *) out = x9
# asm 1: stwa <x9=int64#10,[<out=int64#2] 0x88
# asm 2: stwa <x9=%o0,[<out=%i1] 0x88
stwa %o0,[%i1] 0x88

# qhasm:   out += 4
# asm 1: add <out=int64#2,4,>out=int64#2
# asm 2: add <out=%i1,4,>out=%i1
add %i1,4,%i1

# qhasm:   *(swapendian uint32 *) out = x10
# asm 1: stwa <x10=int64#11,[<out=int64#2] 0x88
# asm 2: stwa <x10=%o1,[<out=%i1] 0x88
stwa %o1,[%i1] 0x88

# qhasm:   out += 4
# asm 1: add <out=int64#2,4,>out=int64#2
# asm 2: add <out=%i1,4,>out=%i1
add %i1,4,%i1

# qhasm:   *(swapendian uint32 *) out = x11
# asm 1: stwa <x11=int64#15,[<out=int64#2] 0x88
# asm 2: stwa <x11=%o5,[<out=%i1] 0x88
stwa %o5,[%i1] 0x88

# qhasm:   out += 4
# asm 1: add <out=int64#2,4,>out=int64#2
# asm 2: add <out=%i1,4,>out=%i1
add %i1,4,%i1

# qhasm:   *(swapendian uint32 *) out = x12
# asm 1: stwa <x12=int64#17,[<out=int64#2] 0x88
# asm 2: stwa <x12=%l0,[<out=%i1] 0x88
stwa %l0,[%i1] 0x88

# qhasm:   out += 4
# asm 1: add <out=int64#2,4,>out=int64#2
# asm 2: add <out=%i1,4,>out=%i1
add %i1,4,%i1

# qhasm:   *(swapendian uint32 *) out = x13
# asm 1: stwa <x13=int64#18,[<out=int64#2] 0x88
# asm 2: stwa <x13=%l1,[<out=%i1] 0x88
stwa %l1,[%i1] 0x88

# qhasm:   out += 4
# asm 1: add <out=int64#2,4,>out=int64#2
# asm 2: add <out=%i1,4,>out=%i1
add %i1,4,%i1

# qhasm:   *(swapendian uint32 *) out = x14
# asm 1: stwa <x14=int64#13,[<out=int64#2] 0x88
# asm 2: stwa <x14=%o3,[<out=%i1] 0x88
stwa %o3,[%i1] 0x88

# qhasm:   out += 4
# asm 1: add <out=int64#2,4,>out=int64#2
# asm 2: add <out=%i1,4,>out=%i1
add %i1,4,%i1

# qhasm:   *(swapendian uint32 *) out = x15
# asm 1: stwa <x15=int64#14,[<out=int64#2] 0x88
# asm 2: stwa <x15=%o4,[<out=%i1] 0x88
stwa %o4,[%i1] 0x88

# qhasm:   out += 4
# asm 1: add <out=int64#2,4,>out=int64#2
# asm 2: add <out=%i1,4,>out=%i1
add %i1,4,%i1

# qhasm:   bytes = bytes_stack
# asm 1: ldx [%fp+2023-<bytes_stack=stack64#2],>bytes=int64#3
# asm 2: ldx [%fp+2023-<bytes_stack=8],>bytes=%i2
ldx [%fp+2023-8],%i2

# qhasm:                         unsigned>? bytes -= 64
# asm 1: subcc <bytes=int64#3,64,>bytes=int64#5
# asm 2: subcc <bytes=%i2,64,>bytes=%i4
subcc %i2,64,%i4

# qhasm:   goto bytesatleast1 if unsigned>
bgu,pt %xcc,._bytesatleast1
nop

# qhasm:   goto done if !unsigned<
bgeu,pt %xcc,._done
nop

# qhasm:     m = ctarget
# asm 1: ldx [%fp+2023-<ctarget=stack64#1],>m=int64#1
# asm 2: ldx [%fp+2023-<ctarget=0],>m=%i0
ldx [%fp+2023-0],%i0

# qhasm:     bytes += 64
# asm 1: add <bytes=int64#5,64,>bytes=int64#3
# asm 2: add <bytes=%i4,64,>bytes=%i2
add %i4,64,%i2

# qhasm:     out -= 64
# asm 1: sub <out=int64#2,64,>out=int64#2
# asm 2: sub <out=%i1,64,>out=%i1
sub %i1,64,%i1

# qhasm:     i = 0
# asm 1: add %g0,0,>i=int64#4
# asm 2: add %g0,0,>i=%i3
add %g0,0,%i3

# qhasm:     ccopyloop:
._ccopyloop:

# qhasm:       a = *(int8 *) (out + i)
# asm 1: ldsb [<out=int64#2+<i=int64#4],>a=int64#5
# asm 2: ldsb [<out=%i1+<i=%i3],>a=%i4
ldsb [%i1+%i3],%i4

# qhasm:       *(int8 *) (m + i) = a
# asm 1: stb <a=int64#5,[<m=int64#1+<i=int64#4]
# asm 2: stb <a=%i4,[<m=%i0+<i=%i3]
stb %i4,[%i0+%i3]

# qhasm:       i += 1
# asm 1: add <i=int64#4,1,>i=int64#4
# asm 2: add <i=%i3,1,>i=%i3
add %i3,1,%i3

# qhasm:                       unsigned<? i - bytes
# asm 1: subcc <i=int64#4,<bytes=int64#3,%g0
# asm 2: subcc <i=%i3,<bytes=%i2,%g0
subcc %i3,%i2,%g0

# qhasm:     goto ccopyloop if unsigned<
blu,pt %xcc,._ccopyloop
nop

# qhasm: done:
._done:

# qhasm: leave
ret
restore

# qhasm: enter ECRYPT_init
.section ".text"
.align 32
.global ECRYPT_init
ECRYPT_init:
save %sp,-288,%sp

# qhasm: leave
ret
restore

# qhasm: enter ECRYPT_ivsetup
.section ".text"
.align 32
.global ECRYPT_ivsetup
ECRYPT_ivsetup:
save %sp,-288,%sp

# qhasm:   x14 = *(uint32 *) (arg2 + 0)
# asm 1: lduw [<arg2=int64#2+0],>x14=int64#5
# asm 2: lduw [<arg2=%i1+0],>x14=%i4
lduw [%i1+0],%i4

# qhasm:   x12 = 0
# asm 1: add %g0,0,>x12=int64#6
# asm 2: add %g0,0,>x12=%i5
add %g0,0,%i5

# qhasm:   x15 = *(uint32 *) (arg2 + 4)
# asm 1: lduw [<arg2=int64#2+4],>x15=int64#2
# asm 2: lduw [<arg2=%i1+4],>x15=%i1
lduw [%i1+4],%i1

# qhasm:   x13 = 0
# asm 1: add %g0,0,>x13=int64#7
# asm 2: add %g0,0,>x13=%g1
add %g0,0,%g1

# qhasm:   x += 48
# asm 1: add <x=int64#1,48,>x=int64#1
# asm 2: add <x=%i0,48,>x=%i0
add %i0,48,%i0

# qhasm:   *(int32 *) (x + 0) = x12
# asm 1: stw <x12=int64#6,[<x=int64#1+0]
# asm 2: stw <x12=%i5,[<x=%i0+0]
stw %i5,[%i0+0]

# qhasm:   x += 4
# asm 1: add <x=int64#1,4,>x=int64#1
# asm 2: add <x=%i0,4,>x=%i0
add %i0,4,%i0

# qhasm:   *(int32 *) (x + 0) = x13
# asm 1: stw <x13=int64#7,[<x=int64#1+0]
# asm 2: stw <x13=%g1,[<x=%i0+0]
stw %g1,[%i0+0]

# qhasm:   x += 4
# asm 1: add <x=int64#1,4,>x=int64#1
# asm 2: add <x=%i0,4,>x=%i0
add %i0,4,%i0

# qhasm:   *(swapendian int32 *) x = x14
# asm 1: stwa <x14=int64#5,[<x=int64#1] 0x88
# asm 2: stwa <x14=%i4,[<x=%i0] 0x88
stwa %i4,[%i0] 0x88

# qhasm:   x += 4
# asm 1: add <x=int64#1,4,>x=int64#1
# asm 2: add <x=%i0,4,>x=%i0
add %i0,4,%i0

# qhasm:   *(swapendian int32 *) x = x15
# asm 1: stwa <x15=int64#2,[<x=int64#1] 0x88
# asm 2: stwa <x15=%i1,[<x=%i0] 0x88
stwa %i1,[%i0] 0x88

# qhasm: leave
ret
restore

# qhasm: enter ECRYPT_keysetup
.section ".text"
.align 32
.global ECRYPT_keysetup
ECRYPT_keysetup:
save %sp,-288,%sp

# qhasm:                  unsigned>? arg3 - 128
# asm 1: subcc <arg3=int64#3,128,%g0
# asm 2: subcc <arg3=%i2,128,%g0
subcc %i2,128,%g0

# qhasm: goto kbits256 if unsigned>
bgu,pt %xcc,._kbits256
nop

# qhasm: kbits128:
._kbits128:

# qhasm:   x4 = *(uint32 *) (arg2 + 0)
# asm 1: lduw [<arg2=int64#2+0],>x4=int64#3
# asm 2: lduw [<arg2=%i1+0],>x4=%i2
lduw [%i1+0],%i2

# qhasm:   x0 = 1634760805 & 0xfffffc00
# asm 1: sethi %lm(1634760805),>x0=int64#4
# asm 2: sethi %lm(1634760805),>x0=%i3
sethi %lm(1634760805),%i3

# qhasm:   x5 = *(uint32 *) (arg2 + 4)
# asm 1: lduw [<arg2=int64#2+4],>x5=int64#5
# asm 2: lduw [<arg2=%i1+4],>x5=%i4
lduw [%i1+4],%i4

# qhasm:   x1 = 824206446 & 0xfffffc00
# asm 1: sethi %lm(824206446),>x1=int64#6
# asm 2: sethi %lm(824206446),>x1=%i5
sethi %lm(824206446),%i5

# qhasm:   x6 = *(uint32 *) (arg2 + 8)
# asm 1: lduw [<arg2=int64#2+8],>x6=int64#7
# asm 2: lduw [<arg2=%i1+8],>x6=%g1
lduw [%i1+8],%g1

# qhasm:   x2 = 2036477238 & 0xfffffc00
# asm 1: sethi %lm(2036477238),>x2=int64#8
# asm 2: sethi %lm(2036477238),>x2=%g4
sethi %lm(2036477238),%g4

# qhasm:   x7 = *(uint32 *) (arg2 + 12)
# asm 1: lduw [<arg2=int64#2+12],>x7=int64#9
# asm 2: lduw [<arg2=%i1+12],>x7=%g5
lduw [%i1+12],%g5

# qhasm:   x3 = 1797285236 & 0xfffffc00
# asm 1: sethi %lm(1797285236),>x3=int64#2
# asm 2: sethi %lm(1797285236),>x3=%i1
sethi %lm(1797285236),%i1

# qhasm:   x8 = x4
# asm 1: add %g0,<x4=int64#3,>x8=int64#10
# asm 2: add %g0,<x4=%i2,>x8=%o0
add %g0,%i2,%o0

# qhasm:   x0 |= 1634760805 & 0x3ff
# asm 1: or <x0=int64#4,%lo(1634760805),>x0=int64#4
# asm 2: or <x0=%i3,%lo(1634760805),>x0=%i3
or %i3,%lo(1634760805),%i3

# qhasm:   x9 = x5
# asm 1: add %g0,<x5=int64#5,>x9=int64#11
# asm 2: add %g0,<x5=%i4,>x9=%o1
add %g0,%i4,%o1

# qhasm:   x1 |= 824206446 & 0x3ff
# asm 1: or <x1=int64#6,%lo(824206446),>x1=int64#6
# asm 2: or <x1=%i5,%lo(824206446),>x1=%i5
or %i5,%lo(824206446),%i5

# qhasm:   x10 = x6
# asm 1: add %g0,<x6=int64#7,>x10=int64#12
# asm 2: add %g0,<x6=%g1,>x10=%o2
add %g0,%g1,%o2

# qhasm:   x2 |= 2036477238 & 0x3ff
# asm 1: or <x2=int64#8,%lo(2036477238),>x2=int64#8
# asm 2: or <x2=%g4,%lo(2036477238),>x2=%g4
or %g4,%lo(2036477238),%g4

# qhasm:   x11 = x7
# asm 1: add %g0,<x7=int64#9,>x11=int64#13
# asm 2: add %g0,<x7=%g5,>x11=%o3
add %g0,%g5,%o3

# qhasm:   x3 |= 1797285236 & 0x3ff
# asm 1: or <x3=int64#2,%lo(1797285236),>x3=int64#2
# asm 2: or <x3=%i1,%lo(1797285236),>x3=%i1
or %i1,%lo(1797285236),%i1

# qhasm: goto storekey
b ._storekey
nop

# qhasm: kbits256:
._kbits256:

# qhasm:   x4 = *(uint32 *) (arg2 + 0)
# asm 1: lduw [<arg2=int64#2+0],>x4=int64#3
# asm 2: lduw [<arg2=%i1+0],>x4=%i2
lduw [%i1+0],%i2

# qhasm:   x0 = 1634760805 & 0xfffffc00
# asm 1: sethi %lm(1634760805),>x0=int64#4
# asm 2: sethi %lm(1634760805),>x0=%i3
sethi %lm(1634760805),%i3

# qhasm:   x5 = *(uint32 *) (arg2 + 4)
# asm 1: lduw [<arg2=int64#2+4],>x5=int64#5
# asm 2: lduw [<arg2=%i1+4],>x5=%i4
lduw [%i1+4],%i4

# qhasm:   x1 = 857760878 & 0xfffffc00
# asm 1: sethi %lm(857760878),>x1=int64#6
# asm 2: sethi %lm(857760878),>x1=%i5
sethi %lm(857760878),%i5

# qhasm:   x6 = *(uint32 *) (arg2 + 8)
# asm 1: lduw [<arg2=int64#2+8],>x6=int64#7
# asm 2: lduw [<arg2=%i1+8],>x6=%g1
lduw [%i1+8],%g1

# qhasm:   x2 = 2036477234 & 0xfffffc00
# asm 1: sethi %lm(2036477234),>x2=int64#8
# asm 2: sethi %lm(2036477234),>x2=%g4
sethi %lm(2036477234),%g4

# qhasm:   x7 = *(uint32 *) (arg2 + 12)
# asm 1: lduw [<arg2=int64#2+12],>x7=int64#9
# asm 2: lduw [<arg2=%i1+12],>x7=%g5
lduw [%i1+12],%g5

# qhasm:   x3 = 1797285236 & 0xfffffc00
# asm 1: sethi %lm(1797285236),>x3=int64#14
# asm 2: sethi %lm(1797285236),>x3=%o4
sethi %lm(1797285236),%o4

# qhasm:   x8 = *(uint32 *) (arg2 + 16)
# asm 1: lduw [<arg2=int64#2+16],>x8=int64#10
# asm 2: lduw [<arg2=%i1+16],>x8=%o0
lduw [%i1+16],%o0

# qhasm:   x0 |= 1634760805 & 0x3ff
# asm 1: or <x0=int64#4,%lo(1634760805),>x0=int64#4
# asm 2: or <x0=%i3,%lo(1634760805),>x0=%i3
or %i3,%lo(1634760805),%i3

# qhasm:   x9 = *(uint32 *) (arg2 + 20)
# asm 1: lduw [<arg2=int64#2+20],>x9=int64#11
# asm 2: lduw [<arg2=%i1+20],>x9=%o1
lduw [%i1+20],%o1

# qhasm:   x1 |= 857760878 & 0x3ff
# asm 1: or <x1=int64#6,%lo(857760878),>x1=int64#6
# asm 2: or <x1=%i5,%lo(857760878),>x1=%i5
or %i5,%lo(857760878),%i5

# qhasm:   x10 = *(uint32 *) (arg2 + 24)
# asm 1: lduw [<arg2=int64#2+24],>x10=int64#12
# asm 2: lduw [<arg2=%i1+24],>x10=%o2
lduw [%i1+24],%o2

# qhasm:   x2 |= 2036477234 & 0x3ff
# asm 1: or <x2=int64#8,%lo(2036477234),>x2=int64#8
# asm 2: or <x2=%g4,%lo(2036477234),>x2=%g4
or %g4,%lo(2036477234),%g4

# qhasm:   x11 = *(uint32 *) (arg2 + 28)
# asm 1: lduw [<arg2=int64#2+28],>x11=int64#13
# asm 2: lduw [<arg2=%i1+28],>x11=%o3
lduw [%i1+28],%o3

# qhasm:   x3 |= 1797285236 & 0x3ff
# asm 1: or <x3=int64#14,%lo(1797285236),>x3=int64#2
# asm 2: or <x3=%o4,%lo(1797285236),>x3=%i1
or %o4,%lo(1797285236),%i1

# qhasm: storekey:
._storekey:

# qhasm:   *(int32 *) (x + 0) = x0
# asm 1: stw <x0=int64#4,[<x=int64#1+0]
# asm 2: stw <x0=%i3,[<x=%i0+0]
stw %i3,[%i0+0]

# qhasm:   x += 4
# asm 1: add <x=int64#1,4,>x=int64#1
# asm 2: add <x=%i0,4,>x=%i0
add %i0,4,%i0

# qhasm:   *(int32 *) (x + 0) = x1
# asm 1: stw <x1=int64#6,[<x=int64#1+0]
# asm 2: stw <x1=%i5,[<x=%i0+0]
stw %i5,[%i0+0]

# qhasm:   x += 4
# asm 1: add <x=int64#1,4,>x=int64#1
# asm 2: add <x=%i0,4,>x=%i0
add %i0,4,%i0

# qhasm:   *(int32 *) (x + 0) = x2
# asm 1: stw <x2=int64#8,[<x=int64#1+0]
# asm 2: stw <x2=%g4,[<x=%i0+0]
stw %g4,[%i0+0]

# qhasm:   x += 4
# asm 1: add <x=int64#1,4,>x=int64#1
# asm 2: add <x=%i0,4,>x=%i0
add %i0,4,%i0

# qhasm:   *(int32 *) (x + 0) = x3
# asm 1: stw <x3=int64#2,[<x=int64#1+0]
# asm 2: stw <x3=%i1,[<x=%i0+0]
stw %i1,[%i0+0]

# qhasm:   x += 4
# asm 1: add <x=int64#1,4,>x=int64#1
# asm 2: add <x=%i0,4,>x=%i0
add %i0,4,%i0

# qhasm:   *(swapendian int32 *) x = x4
# asm 1: stwa <x4=int64#3,[<x=int64#1] 0x88
# asm 2: stwa <x4=%i2,[<x=%i0] 0x88
stwa %i2,[%i0] 0x88

# qhasm:   x += 4
# asm 1: add <x=int64#1,4,>x=int64#1
# asm 2: add <x=%i0,4,>x=%i0
add %i0,4,%i0

# qhasm:   *(swapendian int32 *) x = x5
# asm 1: stwa <x5=int64#5,[<x=int64#1] 0x88
# asm 2: stwa <x5=%i4,[<x=%i0] 0x88
stwa %i4,[%i0] 0x88

# qhasm:   x += 4
# asm 1: add <x=int64#1,4,>x=int64#1
# asm 2: add <x=%i0,4,>x=%i0
add %i0,4,%i0

# qhasm:   *(swapendian int32 *) x = x6
# asm 1: stwa <x6=int64#7,[<x=int64#1] 0x88
# asm 2: stwa <x6=%g1,[<x=%i0] 0x88
stwa %g1,[%i0] 0x88

# qhasm:   x += 4
# asm 1: add <x=int64#1,4,>x=int64#1
# asm 2: add <x=%i0,4,>x=%i0
add %i0,4,%i0

# qhasm:   *(swapendian int32 *) x = x7
# asm 1: stwa <x7=int64#9,[<x=int64#1] 0x88
# asm 2: stwa <x7=%g5,[<x=%i0] 0x88
stwa %g5,[%i0] 0x88

# qhasm:   x += 4
# asm 1: add <x=int64#1,4,>x=int64#1
# asm 2: add <x=%i0,4,>x=%i0
add %i0,4,%i0

# qhasm:   *(swapendian int32 *) x = x8
# asm 1: stwa <x8=int64#10,[<x=int64#1] 0x88
# asm 2: stwa <x8=%o0,[<x=%i0] 0x88
stwa %o0,[%i0] 0x88

# qhasm:   x += 4
# asm 1: add <x=int64#1,4,>x=int64#1
# asm 2: add <x=%i0,4,>x=%i0
add %i0,4,%i0

# qhasm:   *(swapendian int32 *) x = x9
# asm 1: stwa <x9=int64#11,[<x=int64#1] 0x88
# asm 2: stwa <x9=%o1,[<x=%i0] 0x88
stwa %o1,[%i0] 0x88

# qhasm:   x += 4
# asm 1: add <x=int64#1,4,>x=int64#1
# asm 2: add <x=%i0,4,>x=%i0
add %i0,4,%i0

# qhasm:   *(swapendian int32 *) x = x10
# asm 1: stwa <x10=int64#12,[<x=int64#1] 0x88
# asm 2: stwa <x10=%o2,[<x=%i0] 0x88
stwa %o2,[%i0] 0x88

# qhasm:   x += 4
# asm 1: add <x=int64#1,4,>x=int64#1
# asm 2: add <x=%i0,4,>x=%i0
add %i0,4,%i0

# qhasm:   *(swapendian int32 *) x = x11
# asm 1: stwa <x11=int64#13,[<x=int64#1] 0x88
# asm 2: stwa <x11=%o3,[<x=%i0] 0x88
stwa %o3,[%i0] 0x88

# qhasm: leave
ret
restore
